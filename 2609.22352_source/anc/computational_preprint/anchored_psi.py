"""Fix canonical column amplitudes by finite-lambda Lax transport.

No linearized PIV solution or conserved monodromy value is used to set an
amplitude. The independently evolved B system fixes the joint normalization.
"""
from bisect import bisect_right

from mpmath import mp

import high_precision as hp


class AnchorTransport:
    def __init__(self,reference,lam):
        self.segments,self.reference = {},reference
        p = reference.p
        for sign,background_segments in reference.segments.items():
            state = [mp.mpc(1),mp.mpc(0),mp.mpc(0),mp.mpc(1)]
            saved = []
            for start,end,bg in background_segments:
                order = len(bg[0])-1
                diag = [bg[0][n]/2+(lam+p.x0+start if n == 0 else 1 if n == 1 else 0) for n in range(order)]
                lower = [-hp.conv(bg[0],bg[1],n)-(2*p.b if n == 0 else 0) for n in range(order)]
                cols = [[v] for v in state]
                for n in range(order):
                    rhs = [hp.conv(diag,cols[0],n)+cols[1][n],
                           hp.conv(lower,cols[0],n)-hp.conv(diag,cols[1],n),
                           hp.conv(diag,cols[2],n)+cols[3][n],
                           hp.conv(lower,cols[2],n)-hp.conv(diag,cols[3],n)]
                    for col,value in zip(cols,rhs):
                        col.append(value/(n+1))
                state = [hp.horner(col,end-start) for col in cols]
                saved.append((start,end,cols))
            self.segments[sign] = saved

    def at(self,t):
        sign = 1 if t >= 0 else -1
        index = max(0,bisect_right(self.reference.starts[sign],abs(float(t)))-1)
        start,end,coeff = self.segments[sign][index]
        values = [hp.horner(col,mp.mpf(t)-start) for col in coeff]
        return mp.matrix([[values[0],values[2]],[values[1],values[3]]])


class AnchoredContours:
    def __init__(self,reference,radius=14,formal_order=40,tolerance='1e-26',anchors=None):
        self.ref,self.radius,self.order,self.tol = reference,radius,formal_order,tolerance
        self.anchor = anchors if anchors is not None else {
            name:AnchorTransport(reference,mp.mpf('1.45')*(1 if name == 'A' else -1)) for name in ('A','B')}
        self.initial_columns = {}
        self.coefficients = {}
        self.phi0 = self.raw(0)
        self.inverse = self.phi0**-1

    def raw(self,t):
        state = self.ref.at(t)
        q,h,_,logq = state[:4]
        p = self.ref.p
        x,root = p.x0+mp.mpf(t),mp.exp(logq/2)
        answers = []
        residuals,corrections = [],[]
        for name,spec in hp.c.old.CYCLES.items():
            cols,pairs = [],[]
            evolution = self.anchor[name].at(t)
            for j in spec['indices']:
                values,pair = hp.canonical_column(x,q,h,p,j,mp.mpf(self.radius),self.order,mp.mpf(self.tol),
                                                 root=root,vertex_angle=mp.mpf(0) if name == 'A' else mp.pi)
                local = mp.matrix(values)
                key = (name,j)
                if key not in self.initial_columns:
                    if t != 0:
                        raise RuntimeError('Initial canonical column missing')
                    self.initial_columns[key] = local
                target = evolution*self.initial_columns[key]
                pivot = 0 if abs(local[0]) >= abs(local[1]) else 1
                scale = target[pivot]/local[pivot]
                residuals.append(max(abs(v) for v in target-scale*local)/max(abs(v) for v in target))
                sign = 1 if j%2 else -1
                corrections.append(abs(scale/mp.exp(sign*state[4])-1))
                cols.append(scale*local)
                pairs.append([v*scale**2 for v in pair])
            if name not in self.coefficients:
                square = mp.matrix([[v[0]**2 for v in cols],[v[0]*v[1] for v in cols],[v[1]**2 for v in cols]])
                cf = [(-1)**j*mp.det(mp.matrix([[square[r,k] for k in range(4) if k != j] for r in range(3)])) for j in range(4)]
                scale = max(abs(v) for v in cf)
                self.coefficients[name] = [v/scale for v in cf]
            cf = self.coefficients[name]
            answers.append([sum(cf[k]*pairs[k][r] for k in range(4)) for r in range(2)])
        self.diagnostics = {'max_direction_residual':float(max(residuals)),
                            'max_relative_amplitude_correction':float(max(corrections)),
                            'max_anchor_determinant_error':float(max(abs(mp.det(a.at(t))-1) for a in self.anchor.values()))}
        return mp.matrix([[answers[0][0],answers[1][0]],[answers[0][1],answers[1][1]]])

    def at(self,t):
        return self.raw(t)*self.inverse
