#!/usr/bin/env python3
"""Build the support diagram: which assumptions and theorems hold up which.

Input:  docs/depgraph/deps.tsv   (produced by scripts/DepGraph.lean)
        docs/report.md           (Appendix A supplies the labels)
Output: docs/depgraph/support-<view>.svg

The node set is the report's principal results plus the assumptions of §4,
so the picture is the report's own claim structure rather than every lemma.
An edge A -> B means "A is used, directly or through unlabelled lemmas, in
the proof of B"; edges implied by longer paths are removed, so what remains
is the shortest honest account of each dependency.
"""

import os, re, sys, html, collections

# Layout must be deterministic so that regenerating produces a byte-identical
# diagram — the pre-merge check regenerates and diffs. Python randomises
# string hashing per process, which changes set iteration order and with it
# the barycentre sweeps' starting order; pin the seed and re-exec once.
if os.environ.get("PYTHONHASHSEED") != "0":
    os.environ["PYTHONHASHSEED"] = "0"
    os.execv(sys.executable, [sys.executable] + sys.argv)

ROOT = __file__.rsplit('/scripts/', 1)[0]
DEPS = f'{ROOT}/docs/depgraph/deps.tsv'
REPORT = f'{ROOT}/docs/report.md'

# ---------------------------------------------------------------- assumptions
# (label, lean name, group) — the trust boundary of report §4.
ASSUMPTIONS = [
    ('A1', 'LeanDag.Faults.card_validators', 'fault'),
    ('A2', 'LeanDag.Faults.card_byzantine', 'fault'),
    ('P1', 'LeanDag.ValidWrt.predecessor', 'protocol'),
    ('P2', 'LeanDag.ValidWrt.distinct_creators', 'protocol'),
    ('P3', 'LeanDag.ValidWrt.quorum', 'protocol'),
    ("P3'", 'LeanDag.ValidWrt.self_parent', 'protocol'),
    ('P4', 'LeanDag.BlockUniverse.complete', 'protocol'),
    ('P5', 'LeanDag.BlockUniverse.no_equivocation', 'protocol'),
    ('P7', 'LeanDag.Delivery.includes', 'protocol'),
    ('P8', 'LeanDag.Live.builds', 'protocol'),
    ('P9', 'LeanDag.Timing.waits', 'protocol'),
    ('P10', 'LeanDag.FairScheduleOn', 'protocol'),
    ('N2a', 'LeanDag.EventuallyDelivers', 'network'),
    ('N2b', 'LeanDag.Timing.covers', 'network'),
]

# Section of the report each label series belongs to, for colouring.
def series_group(label):
    if label.startswith('CQ'): return 'quality'
    if label.startswith('CU') or label.startswith('V'): return 'core'
    if label.startswith('RS'): return 'reactive'
    if label.startswith('SS'): return 'safeskip'
    if label.startswith('AL'): return 'adaptive'
    if label.startswith('NN'): return 'nemo'
    if label.startswith('MM'): return 'mahimahi'
    if label.startswith('BN'): return 'bn'
    if label.startswith('HZ'): return 'hydrozoan'
    if label.startswith('OH'): return 'optimal'
    if label.startswith('H'): return 'hybrid'
    if label.startswith('I'): return 'integration'
    if label.startswith('E'): return 'dos'
    if label.startswith(('D', 'C', 'B')) and label != 'D': return 'dos'
    if label.startswith('G'): return 'gc'
    if label.startswith('O'): return 'odo'
    return 'core'

GROUP_FILL = {
    'fault':    ('#f3e5d0', '#b08a4a'),
    'protocol': ('#e8e8ea', '#8a8a92'),
    'network':  ('#fbdcdc', '#c06a6a'),
    'core':     ('#dce8f7', '#5a7fa8'),
    'quality':  ('#dcf0e2', '#4f8a63'),
    'dos':      ('#fbe9d6', '#c0844a'),
    'gc':       ('#e9dff5', '#7d63a8'),
    'odo':      ('#fadce6', '#b05878'),
    'reactive': ('#d9eef2', '#4f8a98'),
    'safeskip': ('#eef0d8', '#8f9a4a'),
    'adaptive': ('#f4e3f0', '#a45a92'),
    'hybrid': ('#fdf0d5', '#b0894a'),
    'nemo': ('#d5efe9', '#3f8f7a'),
    'mahimahi': ('#e0ecf8', '#4a6fa5'),
    'bn': ('#fbe9d7', '#b5652a'),
    'hydrozoan': ('#dfeee8', '#3d7a66'),
    'optimal': ('#e6f0e2', '#5a8a3d'),
    'integration': ('#dbe7e0', '#5f8a76'),
}
GROUP_TITLE = {
    'fault': 'fault model (§4.2)', 'protocol': 'protocol clauses (§4.1)',
    'network': 'network (§4.3)', 'core': 'core: safety & liveness (§5–§6)',
    'quality': 'chain quality (§7)', 'dos': 'denial of service (§8)',
    'gc': 'garbage collection (§9)', 'odo': 'Odontoceti (§10)',
    'reactive': 'reactive schedule (§11)',
    'safeskip': 'safe skip (§12)',
    'adaptive': 'adaptive leaders (§13)',
    'hybrid': 'hybrid faults (§14)',
    'nemo': 'crash-fault consensus (§15)',
    'mahimahi': 'Mahi-Mahi (§17)',
    'bn': 'Barnacle (§21)',
    'hydrozoan': 'Hydrozoan (§22)',
    'optimal': 'Optimal-Hydrozoan (§23)',
    'integration': 'integration (§16)',
}

# ---------------------------------------------------------------- input
def load_graph():
    kind, module, deps = {}, {}, collections.defaultdict(set)
    for line in open(DEPS):
        p = line.rstrip('\n').split('\t')
        if p[0] == 'NODE':
            module[p[1]], kind[p[1]] = p[2], p[3]
        elif p[0] == 'EDGE':
            deps[p[1]].add(p[2])
    return kind, module, deps

def load_labels():
    """Appendix A: label -> (statement, [lean names])."""
    rep = open(REPORT).read()
    app = rep[rep.index('## Appendix A. Statement index'):]
    out = []
    for label, stmt, lean in re.findall(r'^\| ([^|]+?) \| ([^|]+?) \| (.+?) \|$',
                                        app, re.M):
        label, stmt = label.strip(), stmt.strip()
        if label in ('Label', '', '—', 'L1'):
            # L1 is the legacy quorum route's result (report §17); the
            # diagrams show the main line.
            continue
        names = re.findall(r"`([A-Za-z][A-Za-z0-9_.']*)`", lean)
        if names:
            out.append((label, stmt, names))
    return out

# ---------------------------------------------------------------- selection
def build(view):
    kind, module, deps = load_graph()
    all_names = set(module)

    def resolve(short):
        # library declarations only: witness-model labels index runs on
        # data, and the diagrams show the proof structure of the library
        exact = [n for n in all_names if (n == short or n.endswith('.' + short))
                 and not n.startswith('LeanDagTest.')]
        if not exact:
            return None
        return min(exact, key=len)

    # selected node -> (label, group, tooltip); plus alias map lean name -> node id
    sel, alias = {}, {}
    for label, lean, group in ASSUMPTIONS:
        sel[lean] = (label, group, lean.split('LeanDag.')[-1])
        alias[lean] = lean

    for label, stmt, names in load_labels():
        group = series_group(label)
        if view == 'core' and group != 'core':
            continue
        primary = None
        for short in names:
            full = resolve(short)
            if full is None:
                continue
            if primary is None:
                primary = full
                sel[full] = (label, group, stmt)
            alias[full] = primary
    return kind, module, deps, sel, alias

def induced_edges(deps, sel, alias):
    """A -> B when A is used in B's proof with no selected node in between."""
    edges = collections.defaultdict(set)
    for node in sel:
        seen, stack, found = set(), [node], set()
        while stack:
            cur = stack.pop()
            for d in deps.get(cur, ()):
                tgt = alias.get(d, d)
                if tgt in sel and tgt != node:
                    found.add(tgt)          # stop: a labelled support
                elif d not in seen:
                    seen.add(d)
                    stack.append(d)
        for f in found:
            edges[f].add(node)              # support -> supported
    return edges

def transitive_reduction(edges, nodes):
    reach = {n: set() for n in nodes}
    order = topo(edges, nodes)
    for n in reversed(order):
        for m in edges.get(n, ()):
            reach[n] |= {m} | reach[m]
    red = collections.defaultdict(set)
    for n in nodes:
        for m in edges.get(n, ()):
            if not any(m in reach[k] for k in edges.get(n, ()) if k != m):
                red[n].add(m)
    return red

def topo(edges, nodes):
    indeg = {n: 0 for n in nodes}
    for n in nodes:
        for m in edges.get(n, ()):
            indeg[m] += 1
    q = [n for n in nodes if indeg[n] == 0]
    out = []
    while q:
        q.sort()
        n = q.pop(0)
        out.append(n)
        for m in sorted(edges.get(n, ())):
            indeg[m] -= 1
            if indeg[m] == 0:
                q.append(m)
    out += [n for n in nodes if n not in out]
    return out

# ---------------------------------------------------------------- layout
def layer_assign(edges, nodes, assumptions):
    """Longest-path layering, with the trust boundary pinned to column 0.

    A result whose proof happens to reach no *labelled* support — it rests
    only on definitions and unlabelled lemmas — would otherwise land in
    column 0 beside the assumptions, which reads as a claim it is one. Such
    results are pushed to column 1 and simply have no incoming arrows."""
    lay = {n: 0 for n in nodes}
    for n in topo(edges, nodes):
        for m in edges.get(n, ()):
            lay[m] = max(lay[m], lay[n] + 1)
    for n in nodes:
        if n not in assumptions:
            lay[n] = max(lay[n], 1)
    return lay

def order_layers(edges, nodes, lay):
    layers = collections.defaultdict(list)
    for n in sorted(nodes):
        layers[lay[n]].append(n)
    up = collections.defaultdict(set)
    for n in nodes:
        for m in edges.get(n, ()):
            up[m].add(n)
    for _ in range(12):                    # barycentre sweeps, both directions
        for L in sorted(layers):
            if L == 0:
                continue
            pos = {n: i for i, n in enumerate(layers[L - 1])}
            layers[L].sort(key=lambda n: (
                sum(pos.get(p, 0) for p in up[n]) / max(1, len([p for p in up[n] if p in pos]))
                if any(p in pos for p in up[n]) else 1e9))
        for L in sorted(layers, reverse=True):
            if L + 1 not in layers:
                continue
            pos = {n: i for i, n in enumerate(layers[L + 1])}
            layers[L].sort(key=lambda n: (
                sum(pos.get(c, 0) for c in edges.get(n, ())) /
                max(1, len([c for c in edges.get(n, ()) if c in pos]))
                if any(c in pos for c in edges.get(n, ())) else 1e9))
    return layers

# ---------------------------------------------------------------- svg
def render(view, sel, edges, layers, lay, compact=False):
    """Left-to-right: each layer a column, so an arrow reads 'supports'."""
    if compact:
        # For inclusion in the report: label only, sized so that the whole
        # diagram stays legible when scaled to a text column.
        BW, BH, VGAP, HGAP, PAD, TOP = 62, 24, 9, 46, 26, 76
    else:
        BW, BH, VGAP, HGAP, PAD, TOP = 158, 36, 12, 96, 40, 100
    nlay = max(layers) + 1
    heights = {L: len(ns) * (BH + VGAP) - VGAP for L, ns in layers.items()}
    H = max(heights.values()) + 2 * PAD + TOP
    W = nlay * (BW + HGAP) - HGAP + 2 * PAD

    xy = {}
    for L, ns in layers.items():
        x = PAD + L * (BW + HGAP)
        y0 = TOP + PAD + (H - TOP - 2 * PAD - heights[L]) / 2
        for i, n in enumerate(ns):
            xy[n] = (x, y0 + i * (BH + VGAP))

    out = [f'<svg xmlns="http://www.w3.org/2000/svg" width="{W:.0f}" '
           f'height="{H:.0f}" viewBox="0 0 {W:.0f} {H:.0f}" '
           f'font-family="Helvetica,Arial,sans-serif">',
           '<style>text{dominant-baseline:middle}'
           f'.lbl{{font-size:{11 if compact else 13}px;font-weight:700}}'
           '.nm{font-size:8.5px;fill:#444}'
           f'.ttl{{font-size:{15 if compact else 20}px;font-weight:700}}'
           f'.sub{{font-size:{9.5 if compact else 11.5}px;fill:#555}}'
           f'.key{{font-size:{9 if compact else 11}px}}'
           f'.col{{font-size:{9 if compact else 10}px;fill:#888;font-weight:700}}'
           '</style>',
           f'<rect width="{W:.0f}" height="{H:.0f}" fill="#fff"/>',
           '<defs><marker id="a" viewBox="0 0 10 10" refX="9" refY="5" '
           'markerWidth="5.5" markerHeight="5.5" orient="auto-start-reverse">'
           '<path d="M0,0 L10,5 L0,10 z" fill="#8894a4"/></marker></defs>']

    title = ('The core account: what supports what' if view == 'core'
             else 'lean-dag: the support structure of the development')
    out.append(f'<text class="ttl" x="{PAD}" y="{26 if compact else 34}">{title}</text>')
    subtitle = ([
        'A → B: A is used in the proof of B. Assumptions on the left; implied '
        'arrows removed.'] if compact else [
        'An arrow A → B means A is used in the proof of B — directly, or through '
        'unlabelled lemmas. Assumptions on the left; each column is one step '
        'further from them.',
        'Extracted from the Lean environment; arrows implied by longer paths are '
        'removed. A box with no incoming arrow rests only on definitions and '
        'unlabelled lemmas.'])
    for i, line in enumerate(subtitle):
        out.append(f'<text class="sub" x="{PAD}" y="{(42 if compact else 54) + i * (13 if compact else 16)}">{line}</text>')

    kx = PAD
    for g in ['fault', 'protocol', 'network', 'core', 'quality', 'dos', 'gc', 'odo']:
        if not any(v[1] == g for v in sel.values()):
            continue
        f, st = GROUP_FILL[g]
        sw = 9 if compact else 11
        out.append(f'<rect x="{kx}" y="{TOP - 16}" width="{sw}" height="{sw}" '
                   f'rx="2" fill="{f}" stroke="{st}"/>')
        out.append(f'<text class="key" x="{kx + sw + 5}" y="{TOP - 11}">'
                   f'{html.escape(GROUP_TITLE[g])}</text>')
        kx += (16 + 5.0 * len(GROUP_TITLE[g])) if compact else (22 + 6.6 * len(GROUP_TITLE[g]))

    for L in sorted(layers):
        x = PAD + L * (BW + HGAP)
        cap = 'assumptions (§4)' if L == 0 else f'step {L}'
        out.append(f'<text class="col" x="{x + BW/2:.1f}" y="{TOP + (10 if compact else 14)}" '
                   f'text-anchor="middle">{cap}</text>')

    for src in edges:
        for dst in edges[src]:
            if src not in xy or dst not in xy:
                continue
            x1, y1 = xy[src][0] + BW, xy[src][1] + BH / 2
            x2, y2 = xy[dst][0], xy[dst][1] + BH / 2
            mx = (x1 + x2) / 2
            out.append(f'<path d="M{x1:.1f},{y1:.1f} C{mx:.1f},{y1:.1f} '
                       f'{mx:.1f},{y2:.1f} {x2:.1f},{y2:.1f}" fill="none" '
                       f'stroke="#8894a4" stroke-width="1" opacity="0.5" '
                       f'marker-end="url(#a)"/>')

    for n, (x, y) in xy.items():
        label, group, tip = sel[n]
        fill, stroke = GROUP_FILL[group]
        short = n.split('.')[-1]
        if len(short) > 25:
            short = short[:24] + '…'
        out.append(f'<g><title>{html.escape(n)} — {html.escape(tip)}</title>')
        out.append(f'<rect x="{x:.1f}" y="{y:.1f}" width="{BW}" height="{BH}" '
                   f'rx="5" fill="{fill}" stroke="{stroke}" stroke-width="1.2"/>')
        if compact:
            out.append(f'<text class="lbl" x="{x + BW/2:.1f}" y="{y + BH/2:.1f}" '
                       f'text-anchor="middle">{html.escape(label)}</text></g>')
        else:
            out.append(f'<text class="lbl" x="{x + BW/2:.1f}" y="{y + 12:.1f}" '
                       f'text-anchor="middle">{html.escape(label)}</text>')
            out.append(f'<text class="nm" x="{x + BW/2:.1f}" y="{y + 26:.1f}" '
                       f'text-anchor="middle">{html.escape(short)}</text></g>')
    out.append('</svg>')
    return '\n'.join(out)

def main():
    for view in ('core', 'full'):
        kind, module, deps, sel, alias = build(view)
        edges = induced_edges(deps, sel, alias)
        edges = transitive_reduction(edges, set(sel))
        assumption_names = {lean for _, lean, _ in ASSUMPTIONS}
        lay = layer_assign(edges, set(sel), assumption_names)
        layers = order_layers(edges, set(sel), lay)
        n_edges = sum(len(v) for v in edges.values())
        for compact in (False, True):
            svg = render(view, sel, edges, layers, lay, compact)
            suffix = f'{view}-compact' if compact else view
            path = f'{ROOT}/docs/depgraph/support-{suffix}.svg'
            open(path, 'w').write(svg)
            w = re.search(r'width="([0-9.]+)"', svg).group(1)
            h = re.search(r'height="([0-9.]+)"', svg).group(1)
            print(f'{path}: {len(sel)} nodes, {n_edges} edges, {w}x{h}')

if __name__ == '__main__':
    main()
