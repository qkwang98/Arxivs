# Changelog (reverse chronological):
# 2026-07-31 21:40 - Claude-Code (agent-shell session, attached from Emacs): created this file.
#   Jan asked for a different view of the n=4,d=1 parameter space (see parameter_space_n4d1.py /
#   parameter_space_n4d1_mesh.py / ../artefacts/extremal-matrix-general.tex Conjecture
#   conj:partition): slice the normalized simplex a1+a2+a3+a4=1 by planes of constant a1 (a1 never
#   enters the proven wall condition a2*a4=a3^2 at all -- see Lemma lem:n4d1-pair -- so slicing by
#   it is the natural axis to demonstrate that), 5 evenly spaced slices, each rendered as an SVG
#   triangle with the wall's intersection as an EXACT red curve (solved analytically via the
#   quadratic formula, not numerically extracted) and the nearest-in-a1 sample points (from the
#   already-saved, verified grid-scan data) as blue dots. Pure Python, hand-written SVG (no
#   plotting library needed for exact vector curves); no Sage needed either (reads the already
#   -verified runs/paramspace_n4_d1_grid_K10.json rather than recomputing anything).

"""
Slices the n=4, d=1 parameter simplex (a1+a2+a3+a4=1) by planes of constant a1 into 5 triangular
cross-sections, each showing the exact intersection curve with the wall a2*a4=a3^2 (red) and
nearby sample points from the verified grid-scan data (blue). See
../artefacts/extremal-matrix-general.tex's Lemma lem:n4d1-pair / Conjecture conj:partition.

Usage: python3 parameter_space_n4d1_slices.py   (from the code/ directory)
"""

import json
import math
import os

OUTDIR_RUNS = '../runs'
OUTDIR_ARTEFACTS = '../artefacts'

BG = '#0f1520'
PANEL_BG = '#161d2b'
LINE = '#3a4760'
CURVE = '#eb6834'
DOT = '#2a78d6'
TEXT = '#eef2f8'
TEXT_MUTED = '#9aa5b8'

SIDE = 240          # triangle side length in px
PAD = 34             # padding around each triangle
LABEL_H = 30         # space above triangle for the a1=... label


def simplex_to_xy(p, q, r):
    """
    Normalized barycentric (p,q,r), p+q+r=1, assigned to vertices
    V_p=(0,0) [a2], V_q=(0.5, sqrt(3)/2) [a3], V_r=(1,0) [a4].
    Returns (x,y) in the unit triangle (x in [0,1], y in [0, sqrt(3)/2]).
    """
    x = 0.5 * q + r
    y = (math.sqrt(3) / 2) * q
    return x, y


def wall_curve(s, n=140):
    """
    Exact points of {a2+a3+a4=s, a2*a4=a3^2, all >=0} via the quadratic formula (a2,a4 are the
    roots of t^2-(s-a3)t+a3^2=0), traced continuously from the a2-vertex through the centroid to
    the a4-vertex. Returns a list of normalized-barycentric (p,q,r) triples (p=a2/s etc).
    """
    if s <= 0:
        return []
    a3_max = s / 3.0
    pts = []
    # branch B: a2=hi root (large a2, small a4), a3 from 0 to a3_max
    for k in range(n + 1):
        a3 = a3_max * k / n
        sum_pair = s - a3
        disc = max(0.0, sum_pair * sum_pair - 4 * a3 * a3)
        sq = math.sqrt(disc)
        a2 = (sum_pair + sq) / 2
        a4 = sum_pair - a2
        pts.append((a2 / s, a3 / s, a4 / s))
    # branch A: a2=lo root, a3 from a3_max back to 0 (continues past the centroid to the a4-vertex)
    for k in range(n + 1):
        a3 = a3_max * (n - k) / n
        sum_pair = s - a3
        disc = max(0.0, sum_pair * sum_pair - 4 * a3 * a3)
        sq = math.sqrt(disc)
        a2 = (sum_pair - sq) / 2
        a4 = sum_pair - a2
        pts.append((a2 / s, a3 / s, a4 / s))
    return pts


def load_and_bin_points(slice_a1_values):
    """
    Reads the verified grid-scan data (paramspace_n4_d1_grid_K10.json), keeps only 'generic case'
    points (the wall itself is already shown exactly via wall_curve), normalizes each to
    barycentric coordinates, and assigns each to whichever slice_a1_values entry its a1 is
    nearest to. Returns {slice_a1: [(p,q,r), ...]} (p,q,r = normalized a2,a3,a4 WITHIN that
    point's own a2+a3+a4, i.e. its position in its assigned slice's cross-section).
    """
    path = os.path.join(OUTDIR_RUNS, 'paramspace_n4_d1_grid_K10.json')
    with open(path) as f:
        data = json.load(f)
    bins = {c: [] for c in slice_a1_values}
    for pt in data['points']:
        if pt['case'] != 'generic case':
            continue
        a1, a2, a3, a4 = pt['a']
        total = a1 + a2 + a3 + a4
        a1n = a1 / total
        nearest = min(slice_a1_values, key=lambda c: abs(c - a1n))
        s = a2 + a3 + a4
        if s <= 0:
            continue
        bins[nearest].append((a2 / s, a3 / s, a4 / s))
    return bins


def _svg_polyline(points_xy, color, width=2.4, opacity=1.0, closed=False):
    pts = ' '.join(f'{x:.2f},{y:.2f}' for x, y in points_xy)
    tag = 'polygon' if closed else 'polyline'
    return (f'<{tag} points="{pts}" fill="none" stroke="{color}" '
            f'stroke-width="{width}" stroke-opacity="{opacity}" '
            f'stroke-linejoin="round" stroke-linecap="round"/>')


def render_panel(a1_value, wall_pts, sample_pts, ox, oy):
    """Returns an SVG <g> string for one slice panel, translated to origin (ox,oy)."""
    scale = SIDE
    # triangle outline (a2 bottom-left, a3 top, a4 bottom-right)
    v2 = simplex_to_xy(1, 0, 0)
    v3 = simplex_to_xy(0, 1, 0)
    v4 = simplex_to_xy(0, 0, 1)
    to_px = lambda p: (ox + p[0] * scale, oy + LABEL_H + (math.sqrt(3) / 2 * scale - p[1] * scale))

    parts = []
    parts.append(f'<rect x="{ox - PAD/2:.1f}" y="{oy - PAD/2:.1f}" '
                 f'width="{scale + PAD:.1f}" height="{scale*math.sqrt(3)/2 + LABEL_H + PAD:.1f}" '
                 f'fill="{PANEL_BG}" stroke="{LINE}" stroke-width="1" rx="10"/>')
    parts.append(f'<text x="{ox + scale/2:.1f}" y="{oy + LABEL_H*0.62:.1f}" '
                 f'fill="{TEXT}" font-family="ui-monospace,Menlo,Consolas,monospace" '
                 f'font-size="15" font-weight="600" text-anchor="middle">a1 = {a1_value:.1f}</text>')

    tri_px = [to_px(v2), to_px(v3), to_px(v4)]
    parts.append(_svg_polyline(tri_px, LINE, width=1.6, opacity=0.9, closed=True))

    wall_px = [to_px(simplex_to_xy(*p)) for p in wall_pts]
    parts.append(_svg_polyline(wall_px, CURVE, width=2.6, opacity=0.95))

    for p in sample_pts:
        x, y = to_px(simplex_to_xy(*p))
        parts.append(f'<circle cx="{x:.2f}" cy="{y:.2f}" r="2.1" fill="{DOT}" fill-opacity="0.65"/>')

    labels = [('a2', v2, (-10, 14)), ('a3', v3, (0, -8)), ('a4', v4, (10, 14))]
    for name, v, (dx, dy) in labels:
        x, y = to_px(v)
        parts.append(f'<text x="{x+dx:.1f}" y="{y+dy:.1f}" fill="{TEXT_MUTED}" '
                     f'font-family="ui-monospace,Menlo,Consolas,monospace" font-size="12" '
                     f'text-anchor="middle">{name}</text>')

    return '\n  '.join(parts)


def render_all(slice_a1_values=(0.1, 0.3, 0.5, 0.7, 0.9)):
    os.makedirs(OUTDIR_ARTEFACTS, exist_ok=True)
    bins = load_and_bin_points(slice_a1_values)

    panel_w = SIDE + PAD
    panel_h = SIDE * math.sqrt(3) / 2 + LABEL_H + PAD
    gap = 18

    # individual SVG files
    individual_paths = []
    for c in slice_a1_values:
        s = 1 - c
        wall_pts = wall_curve(s)
        body = render_panel(c, wall_pts, bins[c], PAD / 2, PAD / 2)
        svg = (f'<svg xmlns="http://www.w3.org/2000/svg" '
               f'width="{panel_w:.1f}" height="{panel_h:.1f}" '
               f'viewBox="0 0 {panel_w:.1f} {panel_h:.1f}">\n'
               f'<rect width="100%" height="100%" fill="{BG}"/>\n  {body}\n</svg>\n')
        fname = f'paramspace_n4_d1_slice_a1_{c:.2f}.svg'
        path = os.path.join(OUTDIR_ARTEFACTS, fname)
        with open(path, 'w') as f:
            f.write(svg)
        individual_paths.append(path)
        print(f'wrote {path}')

    # combined one-row "table" SVG
    total_w = len(slice_a1_values) * panel_w + (len(slice_a1_values) - 1) * gap + gap
    total_h = panel_h + gap
    groups = []
    for i, c in enumerate(slice_a1_values):
        s = 1 - c
        wall_pts = wall_curve(s)
        ox = gap + i * (panel_w + gap) + PAD / 2
        oy = gap / 2 + PAD / 2
        groups.append(render_panel(c, wall_pts, bins[c], ox, oy))
    title = ('n=4, d=1: five slices at fixed a1 -- red = exact wall a2a4=a3^2, '
             'blue = nearest sample points')
    combined = (f'<svg xmlns="http://www.w3.org/2000/svg" '
                f'width="{total_w:.1f}" height="{total_h + 26:.1f}" '
                f'viewBox="0 0 {total_w:.1f} {total_h + 26:.1f}">\n'
                f'<rect width="100%" height="100%" fill="{BG}"/>\n'
                f'<text x="{total_w/2:.1f}" y="18" fill="{TEXT}" '
                f'font-family="ui-monospace,Menlo,Consolas,monospace" font-size="13" '
                f'text-anchor="middle">{title}</text>\n'
                f'<g transform="translate(0,26)">\n' + '\n'.join(groups) + '\n</g>\n</svg>\n')
    combined_path = os.path.join(OUTDIR_ARTEFACTS, 'paramspace_n4_d1_slices_row.svg')
    with open(combined_path, 'w') as f:
        f.write(combined)
    print(f'wrote {combined_path}')
    return individual_paths, combined_path


if __name__ == '__main__':
    render_all()
