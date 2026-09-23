# schlegel_n4_leg_vector_classes.sage
#
# Changelog (reverse chronological):
#   2026-09-07c Viewpoint chosen by MEASUREMENT rather than by first-that-works.
#               Sweep every facet and several epsilons, keep whichever maximises
#               the minimum pairwise distance between projected vertices, relative
#               to the diagram's overall size. Both diagrams jump from an
#               unreadable central cluster to a relative min-separation of ~0.23,
#               and in both cases the winner is a 4-vertex facet, not the largest
#               one -- which is what the earlier version picked.
#   2026-09-07b CORRECTED: the first version was not a Schlegel projection at all.
#               schlegel_projection().coords returned 4-tuples and the plot used
#               the first three, i.e. dropped a coordinate. Caught by comparing
#               against Jan's own .show() output, whose points are genuine
#               3-tuples. Sign trap: Sage writes facets as b + A.x >= 0, so A is
#               the INWARD normal and the viewpoint is at c_F - eps*u.
#   2026-09-07  Created.
#
# n = 4, d = 1 is the smallest case where the leg vector changes the combinatorics
# (m = 3, where binom(m-1,2) first becomes 1): 10 vertices / 21 edges for all-ones
# against 11 / 24 for a log-concave vector.
#
# These agree with Sage's own .show() (threejs) on vertex and edge counts; the
# layouts differ because Sage chooses its own projecting facet and projection
# point. Same graph, different drawing -- neither is more correct.

import itertools
import matplotlib; matplotlib.use("Agg")
import matplotlib.pyplot as plt
# Inlined 2026-09-08. This used to exec a scratch file in /tmp, which meant the script
# stopped working the moment /tmp was cleared -- a figure generator that cannot be re-run is
# how this project lost the ability to regenerate its first three images.
def ras(a,d,N):
    return [vector(QQ,[0]*d+[a[j] for j in range(k)]+[0]*(N-d-k)) for k in range(1,len(a)+1)]
def rams(a,degs):
    n=len(a); N=n+max(degs)
    return Polyhedron(vertices=[sum((ras(a,degs[i],N)[t[i]] for i in range(len(degs))),
                                    vector(QQ,[0]*N))
        for t in itertools.product(range(n),repeat=len(degs))],base_ring=QQ)
def fulldim(P):
    V=[v.vector() for v in P.vertices()]; v0=V[0]
    B=matrix(QQ,[v-v0 for v in V[1:]]).row_space().basis_matrix()
    return Polyhedron(vertices=[list(B.solve_left(v-v0)) for v in V],base_ring=QQ)
def project(Q,F,eps):
    H=[h for h in Q.Hrepresentation() if h.is_inequality()
       and all(h.eval(v.vector())==0 for v in F.vertices())][0]
    u=vector(QQ,H.A()); b=-QQ(H.b())
    cF=sum((v.vector() for v in F.vertices()),vector(QQ,[0]*Q.ambient_dim()))/len(F.vertices())
    p=cF-eps*u
    out={}
    for v in Q.vertices():
        w=v.vector(); den=u*(w-p)
        if den==0: return None
        t=(b-u*p)/den
        if t<=0: return None
        out[tuple(w)]=p+t*(w-p)
    B=matrix(QQ,[list(x) for x in matrix(QQ,[u]).right_kernel().basis()])
    o=list(out.values())[0]
    return {k:tuple(map(float,B.solve_left(x-o))) for k,x in out.items()}
def spread(pr):
    import math
    P=list(pr.values()); m=1e18
    for i in range(len(P)):
        for j in range(i+1,len(P)):
            m=min(m,math.dist(P[i],P[j]))
    ext=max(math.dist(a,b) for a in P for b in P) or 1
    return m/ext                      # min separation relative to overall size
for lab,a,col in (("schlegel-all-ones-1111",[1,1,1,1],"#d87a2a"),
                  ("schlegel-logconcave-1331",[1,3,3,1],"#3a6fd8")):
    P=rams(a,[0,1]); Q=fulldim(P)
    best=None
    for F in Q.faces(Q.dim()-1):
        for eps in [QQ(1)/2,QQ(1),QQ(2),QQ(4),QQ(8),QQ(16)]:
            pr=project(Q,F,eps)
            if pr is None: continue
            s=spread(pr)
            if best is None or s>best[0]: best=(s,F,eps,pr)
    s,F,eps,pr=best
    print("%-26s facet with %d verts, eps=%s, relative min-separation %.4f"%(lab,len(F.vertices()),eps,s))
    pts=list(pr.values())
    E=[(tuple(e.vertices()[0].vector()),tuple(e.vertices()[1].vector())) for e in Q.faces(1)]
    fig=plt.figure(figsize=(5.6,5.2)); ax=fig.add_subplot(111,projection='3d')
    for (x,y) in E:
        p1,p2=pr[x],pr[y]
        ax.plot([p1[0],p2[0]],[p1[1],p2[1]],[p1[2],p2[2]],color='k',lw=1.25,alpha=0.85)
    ax.scatter([q[0] for q in pts],[q[1] for q in pts],[q[2] for q in pts],
               color=col,s=48,depthshade=False,edgecolor='k',linewidth=0.7)
    lo=[min(q[k] for q in pts) for k in range(3)]; hi=[max(q[k] for q in pts) for k in range(3)]
    rng=max(hi[k]-lo[k] for k in range(3)) or 1
    for k,setl in enumerate((ax.set_xlim,ax.set_ylim,ax.set_zlim)):
        mid=(lo[k]+hi[k])/2; setl(mid-rng/2*1.12,mid+rng/2*1.12)
    # Viewpoint, settled 2026-09-08. History, because it is a case where the metric and the
    # eye disagreed and the eye won:
    #
    #   (24,-48)   original, never optimised at all -- only the Schlegel facet and eps were
    #              searched, the camera was fixed by hand.  Separation score 0.103.
    #   (31,-56)   optimum of a 1-degree sweep maximising the WORSE of the two panels'
    #              on-screen relative minimum vertex separation.  Score 0.161.
    #   (54,125)   CHOSEN BY JAN from the eight variants rendered by
    #              schlegel_viewpoint_variants.sage.  Score 0.137, i.e. lower than the sweep
    #              optimum.  He is right that it reads better: the separation score only asks
    #              whether vertices collide, and says nothing about whether the edge structure
    #              is legible.
    #
    # The two panels must share a viewpoint -- the figure exists to compare them.
    ax.view_init(elev=54,azim=125); ax.set_axis_off()
    try: ax.set_box_aspect((1,1,1))
    except Exception: pass
    fig.tight_layout(pad=0.1); fig.savefig("img/%s.png"%lab,dpi=200,bbox_inches='tight'); plt.close(fig)
