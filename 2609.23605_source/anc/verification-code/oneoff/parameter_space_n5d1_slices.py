# Changelog (reverse chronological):
# 2026-08-01 - Claude: render_all/load_and_bin_points now take results_filename as a real
#   parameter (was hardcoded) so the plot can be regenerated against bigger runs without editing
#   the file.
# 2026-08-01 - Claude: created this file, adapting parameter_space_n4d1_slices.py's
#   triangular-slice technique to n=5, d=1. Dimension count forces a difference from the n=4
#   precedent: the n=4 parameter simplex has 3 free parameters (mod scaling), so fixing one
#   coordinate (a1) already leaves a 2D triangle. The n=5 simplex has 4 free parameters, so
#   fixing only one coordinate leaves a 3D tetrahedron, not a triangle -- getting down to a
#   genuine 2D triangle needs two coordinates removed. Rather than an arbitrary second fixed
#   coordinate, this bins by t = (a1+a5)/(a1+...+a5) -- the combined mass of the two "boundary"
#   indices -- and plots each point's (a2,a3,a4), renormalized to their own sum, inside that
#   t-bin's triangle. This is a projection (marginalizing how a1,a5 individually split within
#   their sum), not an exact codimension-2 slice, but it's the natural choice: a1 and a5 are the
#   two indices that play no role in the n=4 wall a2*a4=a3^2 (which lives entirely among
#   a2,a3,a4), so projecting them out this way puts (a2,a3,a4) on direct, visually comparable
#   footing with the known n=4 case. Same 5 target values (0.1,0.3,0.5,0.7,0.9), same
#   nearest-bin assignment, same SVG rendering approach and color scheme (blue #2a78d6
#   generic, orange #eb6834 special) as the n=4 precedent -- no known wall curve to overlay yet
#   here, so points only, no analytic curve.

"""
Bins the n=5, d=1 random-sample results (paramspace_n5_d1_results_sage_seed1_N500.json, from
parameter_space_n5d1.py) by t = (a1+a5)/(a1+...+a5) into 5 slices, each rendered as an SVG
triangle showing that slice's points positioned by their own (a2,a3,a4) (renormalized to sum 1),
colored by combinatorial type (generic/special). See this file's changelog for why t=(a1+a5) was
chosen as the binning coordinate instead of a literal second fixed coordinate.

Usage: python3 parameter_space_n5d1_slices.py   (from the code/ directory)
"""

import json
import math
import os

OUTDIR_RUNS = '../runs'
OUTDIR_ARTEFACTS = '../artefacts'

BG = '#0f1520'
PANEL_BG = '#161d2b'
LINE = '#3a4760'
GENERIC = '#2a78d6'
SPECIAL = '#eb6834'
TEXT = '#eef2f8'
TEXT_MUTED = '#9aa5b8'

SIDE = 200
PAD = 34
LABEL_H = 30


def simplex_to_xy(p, q, r):
    """
    Normalized barycentric (p,q,r), p+q+r=1, assigned to vertices
    V_p=(0,0) [a2], V_q=(0.5, sqrt(3)/2) [a3], V_r=(1,0) [a4] -- same convention as
    parameter_space_n4d1_slices.py.
    """
    x = 0.5 * q + r
    y = (math.sqrt(3) / 2) * q
    return x, y


def load_and_bin_points(slice_t_values, results_filename='paramspace_n5_d1_results_sage_seed1_N500.json'):
    """
    Reads a run_on_points results file (Sage or Julia -- both agree, see
    compare_n5d1_tandem.py), computes t=(a1+a5)/total for each point, assigns it to whichever
    slice_t_values entry is nearest, and within that bin records (a2/s, a3/s, a4/s, case) where
    s=a2+a3+a4. Returns {slice_t: [(p,q,r,case), ...]}.
    """
    path = os.path.join(OUTDIR_RUNS, results_filename)
    with open(path) as f:
        data = json.load(f)
    bins = {c: [] for c in slice_t_values}
    for pt in data['points']:
        a1, a2, a3, a4, a5 = pt['a']
        total = a1 + a2 + a3 + a4 + a5
        t = (a1 + a5) / total
        nearest = min(slice_t_values, key=lambda c: abs(c - t))
        s = a2 + a3 + a4
        if s <= 0:
            continue
        bins[nearest].append((a2 / s, a3 / s, a4 / s, pt['case']))
    return bins


def _svg_polygon(points_xy, color, width=1.6, opacity=0.9):
    pts = ' '.join(f'{x:.2f},{y:.2f}' for x, y in points_xy)
    return (f'<polygon points="{pts}" fill="none" stroke="{color}" '
            f'stroke-width="{width}" stroke-opacity="{opacity}" '
            f'stroke-linejoin="round" stroke-linecap="round"/>')


def render_panel(t_value, sample_pts, ox, oy):
    """Returns an SVG <g> string for one slice panel, translated to origin (ox,oy)."""
    scale = SIDE
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
                 f'font-size="15" font-weight="600" text-anchor="middle">a1+a5 = {t_value:.1f}</text>')

    tri_px = [to_px(v2), to_px(v3), to_px(v4)]
    parts.append(_svg_polygon(tri_px, LINE))

    for p, q, r, case in sample_pts:
        x, y = to_px(simplex_to_xy(p, q, r))
        color = GENERIC if case == 'generic case' else SPECIAL
        radius = 2.1 if case == 'generic case' else 2.8
        parts.append(f'<circle cx="{x:.2f}" cy="{y:.2f}" r="{radius}" fill="{color}" fill-opacity="0.75"/>')

    labels = [('a2', v2, (-10, 14)), ('a3', v3, (0, -8)), ('a4', v4, (10, 14))]
    for name, v, (dx, dy) in labels:
        x, y = to_px(v)
        parts.append(f'<text x="{x+dx:.1f}" y="{y+dy:.1f}" fill="{TEXT_MUTED}" '
                     f'font-family="ui-monospace,Menlo,Consolas,monospace" font-size="12" '
                     f'text-anchor="middle">{name}</text>')

    return '\n  '.join(parts)


def render_all(slice_t_values=(0.1, 0.3, 0.5, 0.7, 0.9), outname='paramspace_n5_d1_slices.svg',
               results_filename='paramspace_n5_d1_results_sage_seed1_N500.json'):
    os.makedirs(OUTDIR_ARTEFACTS, exist_ok=True)
    bins = load_and_bin_points(slice_t_values, results_filename=results_filename)
    for c in slice_t_values:
        n_generic = sum(1 for *_, case in bins[c] if case == 'generic case')
        n_special = len(bins[c]) - n_generic
        print(f't={c}: {len(bins[c])} points ({n_generic} generic, {n_special} special)')

    panel_w = SIDE + PAD
    panel_h = SIDE * math.sqrt(3) / 2 + LABEL_H + PAD
    gap = 18

    total_w = len(slice_t_values) * panel_w + (len(slice_t_values) - 1) * gap + PAD
    total_h = panel_h + PAD + 40  # extra headroom for a title + legend row

    body_parts = []
    for i, c in enumerate(slice_t_values):
        ox = PAD / 2 + i * (panel_w + gap)
        oy = PAD / 2 + 40
        body_parts.append(render_panel(c, bins[c], ox, oy))

    title = ('n=5, d=1 parameter-space exploration: 5 slices by t=(a1+a5)/sum(a), '
             'points positioned by (a2,a3,a4)')
    legend_y = 26
    legend = (
        f'<circle cx="{PAD}" cy="{legend_y}" r="3" fill="{GENERIC}"/>'
        f'<text x="{PAD+10}" y="{legend_y+4}" fill="{TEXT_MUTED}" font-family="ui-monospace,Menlo,Consolas,monospace" font-size="12">generic case</text>'
        f'<circle cx="{PAD+140}" cy="{legend_y}" r="3.5" fill="{SPECIAL}"/>'
        f'<text x="{PAD+150}" y="{legend_y+4}" fill="{TEXT_MUTED}" font-family="ui-monospace,Menlo,Consolas,monospace" font-size="12">special case</text>'
    )

    svg = (f'<svg xmlns="http://www.w3.org/2000/svg" '
           f'width="{total_w:.1f}" height="{total_h:.1f}" '
           f'viewBox="0 0 {total_w:.1f} {total_h:.1f}">\n'
           f'<rect width="100%" height="100%" fill="{BG}"/>\n'
           f'<text x="{total_w/2:.1f}" y="16" fill="{TEXT}" '
           f'font-family="ui-monospace,Menlo,Consolas,monospace" font-size="13" '
           f'text-anchor="middle">{title}</text>\n'
           f'{legend}\n'
           + '\n'.join(body_parts) +
           '\n</svg>\n')

    path = os.path.join(OUTDIR_ARTEFACTS, outname)
    with open(path, 'w') as f:
        f.write(svg)
    print(f'wrote {path}')
    return path


if __name__ == '__main__':
    render_all()
