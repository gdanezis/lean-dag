"""Blocks a node processes after GST, with and without equivocation reports
(`docs/sync.md` §7).

setup(n, f): q = n - f; honest nodes 0..q-1; Byzantine q..n-1 (X, Y, Z the
first three). Each node runs one sync per peer: the target is the peer's
highest announced block not held, streamed in round order, k blocks a tick
from honest peers and kb from Byzantine ones. Honest nodes build above the
highest round at which they hold q authors. Blocks below top - L are
deleted. Honest links take 1..dmax ticks before GST and 1..Delta after;
Byzantine links take 1 tick.

Rules (honest):
  none   reference any held block, sync any target;
  dos    DoSValid: a block references no author with twins in its history
         (within L rounds); targets and arriving blocks must pass; twins on
         the disk detect their author, whose targets are dropped;
  rep    dos, with exposure = twins in the history or evidence carried by a
         block of the history; a node holding twins of X, or evidence
         against X, convicts X, reports it to every honest node and carries
         the evidence in its blocks; it builds nothing within Delta ticks of
         a conviction; from GST + Delta a target that exposes an author the
         node has not convicted ends the sync from that peer.

Processing counts every streamed block that arrives not held and above the
horizon. The slope is the processing per round between tick `mark` and the
end, for the honest node that processes most. Cells: rounds reached, blocks
processed (all, Byzantine), slope (all/Byzantine); a trailing ! marks a run
in which a node ended the sync from an honest peer.

Attacks (Byzantine blocks reference honest blocks of the round below):
  prefeed   every 40 rounds Y's block names a fresh X chain down to round 1,
            streamed to node 0 only;
  edge      every Y block names a fresh X chain of depth 13, to node 0 only;
  carrier   the same, streamed to every honest node;
  tree      each round Y announces a binary tree of X and Y twins of depth 5;
  split     X and Y keep a separate lineage for each honest node;
  splittree each round Y shows each honest node its own tree;
  filler    each round every Byzantine author shows each honest node a block
            carrying a fresh chain of its own of length D;
  twins     each round X shows each honest node its own twin, and Y's block
            references one of them;
  isolate   each honest node gets a block of every Byzantine author at its
            own top round, X's carrying a fresh X chain of length D.
"""
import random
import sys
from collections import defaultdict

blocks = []
EV = {}
CACHE = {}
N = F = Q = 0
HON, BYZ = [], []
X = Y = Z = W = S = 0


def setup(n, f):
    global N, F, Q, HON, BYZ, X, Y, Z, W, S
    N, F, Q = n, f, n - f
    HON, BYZ = list(range(Q)), list(range(Q, N))
    X, Y = BYZ[0], BYZ[1]
    Z = BYZ[2] if len(BYZ) > 2 else BYZ[1]
    W, S = 0, Q - 1


def new_block(a, r, refs, ev=frozenset()):
    blocks.append((a, r, tuple(refs)))
    EV[len(blocks) - 1] = ev
    return len(blocks) - 1


def analyze(refs, rnd, L, ev_root, evidence):
    """Exposed authors and unvouched count of a block at round `rnd` with references
    `refs` carrying `ev_root`, within L rounds."""
    lo = rnd - L
    cone, stack = set(), [x for x in refs if blocks[x][1] >= lo]
    while stack:
        x = stack.pop()
        if x in cone:
            continue
        cone.add(x)
        stack.extend(r for r in blocks[x][2] if blocks[r][1] >= lo)
    slots = defaultdict(int)
    exposed = set(ev_root) if evidence else set()
    for x in cone:
        slots[blocks[x][:2]] += 1
        if evidence:
            exposed |= EV[x]
    exposed |= {a for (a, r), c in slots.items() if c > 1}
    return exposed, len(cone)


def exposed_of(b, L, evidence):
    key = (b, evidence)
    if key not in CACHE:
        a, r, refs = blocks[b]
        CACHE[key] = analyze(refs, r, L, EV[b], evidence)
    return CACHE[key]


def valid(rule, b, L):
    if rule == 'none':
        return True
    ex, _ = exposed_of(b, L, rule == 'rep')
    return not any(blocks[r][0] in ex for r in blocks[b][2])


def missing_from(t, have, source, hz):
    out, seen, stack = [], {t}, [t]
    while stack:
        x = stack.pop()
        if x in have or blocks[x][1] < hz or (source is not None and x not in source):
            continue
        out.append(x)
        for r in blocks[x][2]:
            if r not in seen:
                seen.add(r)
                stack.append(r)
    out.sort(key=lambda x: (blocks[x][1], x))
    return out


def run(attack, rule='none', ticks=600, k=8, kb=64, d=5, L=20, depth=13, D=5, gst=200,
        seed=1, dmax=10, Delta=3, n=None, f=None, mark=None):
    if n is not None:
        setup(n, f)
    blocks.clear()
    EV.clear()
    CACHE.clear()
    rng = random.Random(seed)
    evid = rule == 'rep'
    gen = {a: new_block(a, 0, []) for a in range(N)}
    builders = list(HON)
    disk = {v: set(gen.values()) for v in builders}
    diskr = {v: defaultdict(set) for v in builders}
    twins = {v: defaultdict(lambda: defaultdict(list)) for v in builders}
    for v in builders:
        diskr[v][0] = set(gen.values())
        for a in range(N):
            twins[v][0][a].append(gen[a])
    hz = {v: 0 for v in builders}
    top = {v: 0 for v in builders}
    own = {v: gen[v] for v in builders}
    target = {v: {} for v in builders}
    conv = {v: {} for v in builders}
    bad = {v: set() for v in builders}
    proc = {v: 0 for v in builders}
    procB = {v: 0 for v in builders}
    series = []
    inbox = defaultdict(list)
    honest_at = defaultdict(dict)
    for a in HON:
        honest_at[0][a] = gen[a]
    byz_at = defaultdict(dict)
    for a in BYZ:
        byz_at[0][a] = gen[a]
    y_last = gen[Y]
    made = set()
    lin = {}
    if mark is None:
        mark = max(gst + 100, ticks - 500)
    mark = min(mark, ticks - 1)

    def hdelay(t):
        return rng.randint(1, dmax) if t < gst else rng.randint(1, Delta)

    def delay(t, a, b):
        return hdelay(t) if a in HON and b in HON else 1

    def send(t, u, v, kind, b):
        inbox[t + delay(t, u, v)].append((v, kind, u, b))

    def mk(a, j, byz):
        hb = honest_at[j - 1]
        refs = list(byz) + [hb[h] for h in sorted(hb)][:Q - len(byz)]
        have = {blocks[x][0] for x in refs}
        for o in [a] + [o for o in BYZ if o != a]:
            if len(refs) < Q and o not in have and o in byz_at[j - 1]:
                refs.append(byz_at[j - 1][o])
                have.add(o)
        b = new_block(a, j, refs)
        byz_at[j].setdefault(a, b)
        return b

    def tree(a, j, dep):
        if dep == 0:
            return mk(a, j, [])
        return mk(a, j, [tree(X, j - 1, dep - 1), tree(Y, j - 1, dep - 1)])

    def chain(a, frm, to):
        tip = None
        for j in range(frm, to + 1):
            tip = mk(a, j, [] if tip is None else [tip])
        return tip

    def convict(t, v, a):
        if rule == 'none' or a in conv[v]:
            return
        conv[v][a] = t
        target[v].pop(a, None)
        if evid:
            for w in HON:
                if w != v:
                    inbox[t + hdelay(t)].append((w, 'rep', v, a))

    def put(t, v, b):
        a, r, _ = blocks[b]
        disk[v].add(b)
        diskr[v][r].add(b)
        twins[v][r][a].append(b)
        if len(twins[v][r][a]) > 1:
            convict(t, v, a)
        if evid:
            for e in EV[b]:
                convict(t, v, e)

    def choose(v, base, keep_own):
        tw = twins[v][base]
        refs = [own[v]] if keep_own else []
        if rule == 'none':
            for a in sorted(tw):
                if a != v:
                    refs.append(tw[a][0])
            return refs
        evr = frozenset(conv[v]) if evid else frozenset()
        pool = {a: [j for j in tw[a] if valid(rule, j, L)] for a in tw
                if a != v and a not in conv[v]}
        while True:
            best = None
            for a, js in pool.items():
                for j in js:
                    ex, size = analyze(refs + [j], base + 1, L, evr, evid)
                    if a not in ex and (best is None or size < best[0]):
                        best = (size, a, j, ex)
            if best is None:
                return refs
            refs.append(best[2])
            del pool[best[1]]
            ex = best[3]
            kept = [x for x in refs if blocks[x][0] not in ex]
            if len(kept) < len(refs):
                refs[:] = kept
            for a2 in list(pool):
                if a2 in ex:
                    del pool[a2]

    for t in range(ticks):
        for v, kind, u, b in inbox.pop(t, []):
            if kind == 'rep':
                convict(t, v, b)
                continue
            if b in disk[v] or blocks[b][1] < hz[v]:
                continue
            if kind == 'ann':
                if u in conv[v] or u in bad[v]:
                    continue
                if blocks[b][1] - L > hz[v]:
                    nh = blocks[b][1] - L
                    for rd in range(hz[v], nh):
                        disk[v] -= diskr[v].pop(rd, set())
                        twins[v].pop(rd, None)
                    hz[v] = nh
                    top[v] = max(top[v], nh)
                cur = target[v].get(u)
                if cur is None or blocks[cur][1] < blocks[b][1]:
                    target[v][u] = b
                continue
            proc[v] += 1
            if blocks[b][0] in BYZ:
                procB[v] += 1
            if all(r in disk[v] or blocks[r][1] < hz[v] for r in blocks[b][2]):
                if rule != 'none' and not valid(rule, b, L):
                    continue
                put(t, v, b)
        for v in builders:
            for u in list(target[v]):
                if target[v][u] in disk[v] or blocks[target[v][u]][1] < hz[v]:
                    del target[v][u]
        for v in builders:
            if evid and any(c > t - Delta for c in conv[v].values()):
                continue
            while True:
                base = top[v]
                hi = [rd for rd in twins[v] if rd > base and
                      sum(1 for a in twins[v][rd] if a != v) >= Q]
                if hi:
                    base = max(hi)
                if sum(1 for a in twins[v][base] if a != v) < Q - 1:
                    break
                refs = choose(v, base, base == top[v] and blocks[own[v]][1] == base)
                if len(refs) < Q:
                    break
                r = base + 1
                b = new_block(v, r, refs, frozenset(conv[v]) if evid else frozenset())
                put(t, v, b)
                own[v], top[v] = b, r
                honest_at[r][v] = b
                for w in builders:
                    if w != v:
                        send(t, v, w, 'ann', b)
                nh = max(0, top[v] - L)
                for rd in range(hz[v], nh):
                    disk[v] -= diskr[v].pop(rd, set())
                    twins[v].pop(rd, None)
                hz[v] = nh
        series.append((min(top.values()), dict(proc), dict(procB)))
        # attackers (X, Y, Z stream from everything they made)
        if attack == 'isolate':
            for h in HON:
                rr = top[h]
                if rr < 1 or (h, rr) in made or len(honest_at[rr - 1]) < 3:
                    continue
                made.add((h, rr))
                for a in BYZ:
                    xs = [chain(a, max(1, rr - D), rr - 1)] if a == X and rr > 2 else []
                    send(t, a, h, 'ann', mk(a, rr, xs))
        elif attack != 'none':
            r = blocks[y_last][1] + 1
            if len(honest_at[r - 1]) >= len(HON):
                only = HON
                if attack == 'tree' and r > d + 1:
                    y = tree(Y, r, d)
                elif attack == 'split' and r > 1:
                    for h in HON:
                        ly = mk(Y, r, [lin[h][Y], lin[h][X]])
                        lx = mk(X, r, [lin[h][X], lin[h][Y]])
                        lin[h] = {X: lx, Y: ly}
                        send(t, Y, h, 'ann', ly)
                        send(t, X, h, 'ann', lx)
                    y = ly
                    only = []
                elif attack == 'splittree' and r > d + 1:
                    for h in HON:
                        send(t, Y, h, 'ann', tree(Y, r, d))
                    y = new_block(Y, r, [])
                    only = []
                elif attack == 'filler' and r > 2:
                    for h in HON:
                        for a in BYZ:
                            send(t, a, h, 'ann', mk(a, r, [chain(a, max(1, r - D), r - 1)]))
                    y = new_block(Y, r, [])
                    only = []
                elif attack == 'carrier' and r > depth + 2:
                    # Y's block carries a fresh X chain each round, shown to every node
                    y = mk(Y, r, [y_last, chain(X, r - depth, r - 1)])
                elif attack == 'twins' and r > 1:
                    # X shows each honest node its own twin each round; Y relays them all
                    xs = [mk(X, r - 1, []) for h in HON]
                    for h, x in zip(HON, xs):
                        send(t, X, h, 'ann', x)
                    y = mk(Y, r, [y_last] + xs[:1])
                elif attack == 'prefeed' and r % 40 == 0:
                    y = mk(Y, r, [y_last, chain(X, 1, r - 1)])
                    only = [W]
                elif attack == 'edge' and r > depth + 2:
                    y = mk(Y, r, [y_last, chain(X, r - depth, r - 1)])
                    only = [W]
                else:
                    y = mk(Y, r, [y_last] if r > 1 else [])
                    if attack in ('prefeed', 'edge'):
                        only = [W]
                    if attack == 'split':
                        lin = {h: {X: gen[X], Y: y} for h in HON}
                y_last = y
                for h in only:
                    send(t, Y, h, 'ann', y)
        for v in builders:
            for u, tg in list(target[v].items()):
                if rule != 'none' and not valid(rule, tg, L):
                    del target[v][u]
                    continue
                if evid and t >= gst + Delta:
                    ex, _ = exposed_of(tg, L, True)
                    if ex - set(conv[v]):
                        bad[v].add(u)
                        del target[v][u]
                        continue
                if u in builders:
                    miss = missing_from(tg, disk[v], disk[u], hz[v])
                else:
                    miss = missing_from(tg, disk[v], None, hz[v])
                for b in miss[:k if u in builders else kb]:
                    send(t, u, v, 'blk', b)
    r_m, p_m, pb_m = series[mark]
    r_e, p_e, pb_e = series[-1]
    dr = max(1, r_e - r_m)
    slope = max(p_e[v] - p_m[v] for v in HON) / dr
    slopeB = max(pb_e[v] - pb_m[v] for v in HON) / dr
    return {'rounds': r_e, 'proc': max(p_e.values()), 'procB': max(pb_e.values()),
            'slope': slope, 'slopeB': slopeB, 'conv': {v: sorted(conv[v]) for v in HON},
            'bad': {v: sorted(bad[v]) for v in HON},
            'badH': sum(len(bad[v] & set(HON)) for v in HON)}


ATTACKS = ['none', 'prefeed', 'edge', 'carrier', 'tree', 'split', 'splittree', 'filler',
           'twins', 'isolate']


def cell(res):
    return (f"{res['rounds']}r P{res['proc']} B{res['procB']} "
            f"s{res['slope']:.1f}/{res['slopeB']:.1f}" + ('!' if res['badH'] else ''))


if __name__ == '__main__':
    n, f = int(sys.argv[1]), int(sys.argv[2])
    ticks = int(sys.argv[3]) if len(sys.argv) > 3 else 900
    rules = sys.argv[4].split(',') if len(sys.argv) > 4 else ['none', 'dos', 'rep']
    setup(n, f)
    print(f"n={n} f={f} ticks={ticks}")
    print(f"{'attack':10}" + ''.join(f"{r:>30}" for r in rules))
    for attack in ATTACKS:
        cells = [cell(run(attack, rule, ticks=ticks)) for rule in rules]
        print(f"{attack:10}" + ''.join(f"{c:>30}" for c in cells), flush=True)
