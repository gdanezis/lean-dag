"""Reference budgets under attack and under honest catch-up (`docs/sync.md` §6).

n = 7, f = 2, q = 5. Honest nodes 0..4; X = 5 makes chains of its own
blocks, Y = 6 builds and relays. Each node runs one sync per peer: the
target is the highest announced block of that peer not held, and the peer
streams the target's missing history in round order, k blocks a tick,
after `delay` ticks. A node builds the round above its top once it holds
q authors of its top round, referencing one held block per author that
passes the rule. Rules, for a candidate block b against the history of
the node's own last block:

  plain       at most tau new blocks;
  per-author  at most tau new blocks of each author;
  vouched     at most tau new blocks reached by held blocks of at most f
              authors.

Scenarios:

  none        no attack; Y builds like an honest node and streams to all;
  prefeed     every 40 rounds Y's block names a fresh X chain down to
              round 1; Y streams only to node 0;
  edge        every Y block names a fresh X chain of depth `depth`
              hanging off honest blocks; Y streams only to node 0;
  two-tops    X and Y each build a private chain of depth `depth` and
              stream it only to node 0, which may reference both;
  slow        node 4's links take 20 ticks until tick 200; Y builds like
              an honest node (applying the rule if `y_rule`) and streams
              to all, so nodes 0-3 and Y build without node 4, which then
              catches up by building every round it missed.
"""
import sys
from collections import defaultdict

N, F, Q = 7, 2, 5
HON = list(range(5))
X, Y, W, S = 5, 6, 0, 4

blocks = []


def new_block(a, r, refs):
    blocks.append((a, r, tuple(refs)))
    return len(blocks) - 1


def missing_from(t, have, source):
    """t's history outside `have`, inside `source` (None: everything), by round."""
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


def new_part(b, published):
    out, seen, stack = [], {b}, [b]
    while stack:
        x = stack.pop()
        if x in published:
            continue
        out.append(x)
        for r in blocks[x][2]:
            if r not in seen:
                seen.add(r)
                stack.append(r)
    return out


def plain(b, published, reach, tau):
    return len(new_part(b, published)) <= tau


def per_author(b, published, reach, tau):
    count = defaultdict(int)
    for x in new_part(b, published):
        count[blocks[x][0]] += 1
    return max(count.values()) <= tau


def vouched(b, published, reach, tau):
    return sum(1 for x in new_part(b, published) if len(reach[x]) <= F) <= tau


RULES = {'none': None, 'plain': plain, 'per-author': per_author, 'vouched': vouched}


def run(scenario, rule, tau=14, ticks=600, k=8, depth=13, y_rule=False):
    blocks.clear()
    builders = HON + ([Y] if scenario in ('none', 'slow') else [])
    gen = {a: new_block(a, 0, []) for a in range(N)}
    disk = {v: set(gen.values()) for v in builders}
    byround = {v: defaultdict(dict) for v in builders}
    reach = {v: defaultdict(set) for v in builders}
    for v in builders:
        for a in range(N):
            byround[v][0][a] = gen[a]
            reach[v][gen[a]].add(a)
    top = {v: 0 for v in builders}
    own = {v: gen[v] for v in builders}
    published = {v: {gen[v]} for v in builders}
    target = {v: {} for v in builders}
    inbox = defaultdict(list)
    honest_at = defaultdict(dict)
    for a in HON:
        honest_at[0][a] = gen[a]
    y_last, x_last = gen[Y], gen[X]
    reached = {}
    refs_to_slow = 0

    def delay(t, a, b):
        return 20 if scenario == 'slow' and t < 200 and S in (a, b) else 1

    def send(t, u, v, kind, b):
        inbox[t + delay(t, u, v)].append((v, kind, u, b))

    def announce(t, u, b, only=None):
        for v in (builders if only is None else [only]):
            if v != u:
                send(t, u, v, 'ann', b)

    def chain(author, frm, to, tip=None):
        for j in range(frm, to + 1):
            hb = honest_at[j - 1]
            others = [hb[a] for a in sorted(hb)[:Q - (0 if tip is None else 1)]]
            tip = new_block(author, j, ([] if tip is None else [tip]) + others)
        return tip

    for t in range(ticks):
        for v, kind, u, b in inbox.pop(t, []):
            if b in disk[v]:
                continue
            if kind == 'ann':
                cur = target[v].get(u)
                if cur is None or blocks[cur][1] < blocks[b][1]:
                    target[v][u] = b
                continue
            if all(r in disk[v] for r in blocks[b][2]):
                a, rd, _ = blocks[b]
                disk[v].add(b)
                byround[v][rd].setdefault(a, b)
                stack, seen = [b], {b}
                while stack:
                    x = stack.pop()
                    reach[v][x].add(a)
                    for r in blocks[x][2]:
                        if r not in seen and a not in reach[v][r]:
                            seen.add(r)
                            stack.append(r)
        for v in builders:
            for u in list(target[v]):
                if target[v][u] in disk[v]:
                    del target[v][u]
        for v in builders:
            checked = RULES[rule] if (v in HON or y_rule) else None
            while True:
                at = byround[v][top[v]]
                if len(at) < Q:
                    break
                refs = [own[v]]
                for a, j in sorted(at.items()):
                    if a == v:
                        continue
                    if checked is not None and not checked(j, published[v], reach[v], tau):
                        continue
                    refs.append(j)
                if len(refs) < Q:
                    break
                r = top[v] + 1
                b = new_block(v, r, refs)
                if v != S and t >= 250 and any(blocks[j][0] == S for j in refs):
                    refs_to_slow += 1
                disk[v].add(b)
                byround[v][r][v] = b
                reach[v][b].add(v)
                own[v], top[v] = b, r
                stack = [b]
                while stack:
                    x = stack.pop()
                    if x not in published[v]:
                        published[v].add(x)
                        stack.extend(blocks[x][2])
                if v in HON:
                    honest_at[r][v] = b
                announce(t, v, b)
        for r in range(min(top[v] for v in HON) + 1):
            reached.setdefault(r, t)
        # the Byzantine builders of the attacks
        r = blocks[y_last][1] + 1
        hb = honest_at[r - 1]
        if scenario in ('prefeed', 'edge', 'two-tops') and len(hb) >= 4:
            hs = [hb[a] for a in sorted(hb)[:4]]
            if scenario == 'prefeed' and r % 40 == 0:
                y = new_block(Y, r, [y_last, chain(X, 1, r - 1)] + hs[:3])
            elif scenario == 'edge' and r > depth + 2:
                y = new_block(Y, r, [y_last, chain(X, r - depth, r - 1)] + hs[:3])
            elif scenario == 'two-tops' and r > depth + 2 and r % 20 == 0:
                y = new_block(Y, r, [chain(Y, r - depth, r - 1)] + hs)
                x = new_block(X, r, [chain(X, r - depth, r - 1)] + hs)
                announce(t, X, x, only=W)
            else:
                y = new_block(Y, r, [y_last] + hs)
            y_last = y
            announce(t, Y, y, only=W)
        # streams: honest nodes and the Byzantine builders from what they hold;
        # X and Y otherwise from everything that exists, to node 0 only
        for v in builders:
            for u, tg in list(target[v].items()):
                if u in builders:
                    miss = missing_from(tg, disk[v], disk[u])
                elif v == W:
                    miss = missing_from(tg, disk[v], None)
                else:
                    miss = []
                for b in miss[:k]:
                    send(t, u, v, 'blk', b)
    rs = sorted(reached)
    longest = max(reached[r] - reached[r - 1] for r in rs[1:])
    return {'rounds': min(top[v] for v in HON), 'longest': longest, 'refs_to_slow': refs_to_slow}


if __name__ == '__main__':
    ticks = int(sys.argv[1]) if len(sys.argv) > 1 else 600
    cases = [('none', {}), ('prefeed', {}), ('edge', {'depth': 13}), ('two-tops', {'depth': 13}),
             ('slow', {'y_rule': True}), ('slow', {'y_rule': False})]
    print(f"{'scenario':24}" + ''.join(f"{r:>22}" for r in RULES))
    for scenario, kw in cases:
        name = scenario + (' (Y applies rule)' if kw.get('y_rule') else
                           ' (Y relays)' if scenario == 'slow' else '')
        cells = []
        for rule in RULES:
            res = run(scenario, rule, ticks=ticks, **kw)
            cell = f"{res['rounds']} r, {res['longest']} t"
            if scenario == 'slow':
                cell += f", {res['refs_to_slow']} ref"
            cells.append(cell)
        print(f"{name:24}" + ''.join(f"{c:>22}" for c in cells))
