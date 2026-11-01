"""Fair causal-stream sync under a prefeed attack (`docs/sync.md` §5).

n = 7, f = 2, q = 5. Honest nodes 0..4; X = 5 makes junk (fresh chains of
its own blocks), Y = 6 relays. Each honest node runs one sync per peer:
target = highest announced block of that peer not held; the peer streams
the target's missing history in round order, k blocks per tick, one tick
latency. Y streams only to its client w = 0.

Prefeed: every `every` rounds Y's block also references the tip of a
fresh X chain reaching down to round 1. Y's blocks reference Y's previous
one, so the chain is in the history of each later Y block; w downloads
it in the background and references the first Y block whose history it
holds whole, so w's next block carries the whole chain. The other honest
nodes fetch it through w's stream at k per tick, and need w's block for
a quorum.

Modes: 'none'; 'prefeed'; 'budget': prefeed, but an honest node
references a block only if its history adds at most `tau` blocks to the
history of the node's own last block.
"""
import sys
from collections import defaultdict

N, F, Q = 7, 2, 5
HON = list(range(5))
X, Y = 5, 6
W = 0

blocks = []                # id -> (author, round, refs)


def new_block(author, rnd, refs):
    blocks.append((author, rnd, tuple(refs)))
    return len(blocks) - 1


def missing_from(t, have, source):
    """Blocks of t's history outside `have`, inside `source` (None: all), by round."""
    out, seen, stack = [], {t}, [t]
    while stack:
        x = stack.pop()
        if x in have or (source is not None and x not in source):
            continue
        out.append(x)
        for r in blocks[x][2]:
            if r not in seen:
                seen.add(r)
                stack.append(r)
    out.sort(key=lambda x: (blocks[x][1], x))
    return out


def novelty(b, published):
    out, seen, stack = 0, {b}, [b]
    while stack:
        x = stack.pop()
        if x in published:
            continue
        out += 1
        for r in blocks[x][2]:
            if r not in seen:
                seen.add(r)
                stack.append(r)
    return out


def run(mode, ticks=600, k=8, every=40, tau=None):
    blocks.clear()
    gen = {a: new_block(a, 0, []) for a in range(N)}
    disk = {v: set(gen.values()) for v in HON}
    slot = {v: {(a, 0): gen[a] for a in range(N)} for v in HON}   # (author, round) -> id
    byround = {v: defaultdict(dict) for v in HON}                   # round -> author -> id
    for v in HON:
        for a in range(N):
            byround[v][0][a] = gen[a]
    top = {v: 0 for v in HON}
    own = {v: gen[v] for v in HON}
    published = {v: {gen[v]} for v in HON}
    target = {v: {} for v in HON}
    detected = {v: set() for v in HON}
    inbox = defaultdict(list)          # tick -> [(v, kind, payload)]
    honest_at = defaultdict(dict)      # round -> author -> id
    for a in HON:
        honest_at[0][a] = gen[a]
    y_last = gen[Y]
    first_reach = {}                   # round -> tick when every honest node reached it
    next_attack = every
    releases = []

    def send(t, v, kind, p):
        inbox[t + 1].append((v, kind, p))

    def announce(t, u, b, only=None):
        for v in (HON if only is None else [only]):
            if v != u:
                send(t, v, 'ann', (u, b))

    def chain(tip, frm, to):
        """Extend an X chain from `tip` (round frm - 1) to round `to`."""
        for j in range(frm, to + 1):
            hb = honest_at[j - 1]
            tip = new_block(X, j, [tip] + [hb[a] for a in sorted(hb)[:Q - 1]])
        return tip

    for t in range(ticks):
        for v, kind, p in inbox.pop(t, []):
            u, b = p
            if b in disk[v]:
                continue
            if kind == 'ann':
                if u in detected[v]:
                    continue
                cur = target[v].get(u)
                if cur is None or blocks[cur][1] < blocks[b][1]:
                    target[v][u] = b
                continue
            if all(r in disk[v] for r in blocks[b][2]):
                a, rd, _ = blocks[b]
                if (a, rd) in slot[v] and slot[v][(a, rd)] != b:
                    detected[v].add(a)
                    target[v].pop(a, None)
                else:
                    slot[v][(a, rd)] = b
                disk[v].add(b)
                byround[v][rd].setdefault(a, b)
        for v in HON:
            for u in list(target[v]):
                if target[v][u] in disk[v]:
                    del target[v][u]
        # honest builds
        for v in HON:
            while True:
                at_r = byround[v][top[v]]
                if len(at_r) < Q:
                    break
                refs = [own[v]]
                for a, j in sorted(at_r.items()):
                    if a == v or a in detected[v]:
                        continue
                    if tau is not None and novelty(j, published[v]) > tau:
                        continue
                    refs.append(j)
                if len(refs) < Q:
                    break
                r = top[v] + 1
                b = new_block(v, r, refs)
                disk[v].add(b)
                slot[v][(v, r)] = b
                byround[v][r][v] = b
                own[v], top[v] = b, r
                stack = [b]
                while stack:
                    x = stack.pop()
                    if x not in published[v]:
                        published[v].add(x)
                        stack.extend(blocks[x][2])
                honest_at[r][v] = b
                announce(t, v, b)
        m = min(top.values())
        for r in range(m + 1):
            first_reach.setdefault(r, t)
        # Y's block of the next round, once four honest blocks of the round below exist
        r = blocks[y_last][1] + 1
        hb = honest_at[r - 1]
        if len(hb) >= 4:
            hs = [hb[a] for a in sorted(hb)[:4]]
            if mode != 'none' and r >= next_attack:
                tip = chain(gen[X], 1, r - 1)
                y = new_block(Y, r, [y_last, tip] + hs[:3])
                next_attack = r + every
                releases.append(r)
            else:
                y = new_block(Y, r, [y_last] + hs)
            y_last = y
            announce(t, Y, y)
        # streams
        for v in HON:
            for u, tg in list(target[v].items()):
                if u in HON:
                    miss = missing_from(tg, disk[v], disk[u])
                elif u == Y and v == W:
                    miss = missing_from(tg, disk[v], None)
                else:
                    miss = []
                for b in miss[:k]:
                    send(t, v, 'blk', (u, b))
    rs = sorted(first_reach)
    gaps = [(first_reach[r] - first_reach[r - 1], r) for r in rs[1:]]
    worst = max(gaps)
    stalls = [(r, first_reach[r + 1] - first_reach[r]) for r in rs[:-1]
              if first_reach[r + 1] - first_reach[r] > 5]
    return {'mode': mode, 'tau': tau, 'k': k, 'rounds(min top)': min(top.values()),
            'worst round (ticks, round)': worst, 'releases': len(releases),
            'disk w': len(disk[W]), 'disk 1': len(disk[1]), 'stalls': stalls}


if __name__ == '__main__':
    ticks = int(sys.argv[1]) if len(sys.argv) > 1 else 3000
    for mode, tau in [('none', None), ('prefeed', None), ('budget', 2 * N)]:
        r = run(mode, ticks=ticks, tau=tau)
        print(f"{mode:8} tau={tau}: rounds {r['rounds(min top)']}, "
              f"longest round {r['worst round (ticks, round)'][0]} ticks, "
              f"disk of w {r['disk w']}, disk of node 1 {r['disk 1']}")
        if r['stalls']:
            print('  stalls (round, ticks):', r['stalls'])
