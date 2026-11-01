"""Certified joins of twins (`docs/sync-auth.md`).

The network and rules of `sync-wait.py`. With `auth`, a block joins a twin pair
when both blocks are in its history and in the history of no single reference;
a block that joins pairs is valid only with a certificate for its round whose
set E holds them, signed by at least q nodes, and the certificate is evidence
against the authors of E. An honest node prefers references that join nothing;
when it must join, it sends (round, E) to every node and builds once q have
signed. A signer learns E and convicts its authors. Under `sign='clean'` it
refuses, and sends the block, when it holds a block of that round whose history
holds no pair of E; under `sign='built'` it refuses when it has built that
round. With `cap`, it refuses when E has more than `cap` pairs; with `reuse`, a
node cites certificates of the round it holds instead of requesting. Byzantine
nodes refuse honest requests, and request only when they would succeed.

Attacks beyond those of `sync-wait.py`: `bulk`, two back-dated X chains carried
by fresh chains of Z and Y and joined by Y's block at round 40; `oldjoin`, the
same joined `depth` rounds below 40 and carried up by a chain of Y; `force`, X
shows twins to two honest nodes and Y and Z feed one honest node only.

`python3 sync-auth.py table rule` prints, at n = 10, f = 3 with no horizon over
300 ticks, rounds, blocks of Byzantine authors in honest histories (all /
largest in a round), the least share, the most failed requests of a node, and
the largest E, under evidence checks, twin checks, and certificates.
"""
import random
import sys
from collections import defaultdict

blocks = []
EV = {}
CACHE = {}
CERT = {}
BC = {}
PAIRS = {}
JOK = {}
AUTH = [False]
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
    if evidence is not True:
        exposed |= {a for (a, r), c in slots.items() if c > 1}
    return exposed, len(cone)


def exposed_of(b, L, evidence):
    key = (b, evidence)
    if key not in CACHE:
        a, r, refs = blocks[b]
        CACHE[key] = analyze(refs, r, L, EV[b], evidence)
    return CACHE[key]


def byz_cone(b):
    if b not in BC:
        c = set()
        for r in blocks[b][2]:
            c |= byz_cone(r)
        if blocks[b][0] in BYZ:
            c.add(b)
        BC[b] = frozenset(c)
    return BC[b]


def pairs_in(c):
    sl = defaultdict(list)
    for x in c:
        sl[blocks[x][:2]].append(x)
    return {frozenset((xs[i], xs[j])) for xs in sl.values() if len(xs) > 1
            for i in range(len(xs)) for j in range(i + 1, len(xs))}


def pairs(b):
    if b not in PAIRS:
        PAIRS[b] = frozenset(pairs_in(byz_cone(b)))
    return PAIRS[b]


def joins(refs):
    """The twin pairs a block with references `refs` joins: in its history, and in the
    history of no single reference."""
    c = set()
    for r in refs:
        c |= byz_cone(r)
    old = set()
    for r in refs:
        old |= pairs(r)
    return pairs_in(c) - old


def authors(E):
    return {blocks[x][0] for e in E for x in e}


def certified(b):
    if b not in JOK:
        J = joins(blocks[b][2])
        c = CERT.get(b)
        JOK[b] = not J or (c is not None and J <= c[0] and len(c[1]) >= Q)
    return JOK[b]


def valid(rule, b, L):
    if rule == 'none':
        return True
    if AUTH[0] and not certified(b):
        return False
    ex, _ = exposed_of(b, L, 'both' if rule == 'both' else rule == 'rep')
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


def run(attack, rule='react', ticks=600, k=8, kb=64, d=5, L=20, depth=13, D=5, gst=0,
        seed=1, dmax=10, Delta=3, n=None, f=None, mark=None, twin=False, tau=None,
        w=None, auth=False, cap=None, byzsign=False, sign='clean', reuse=False):
    if n is not None:
        setup(n, f)
    blocks.clear()
    EV.clear()
    CACHE.clear()
    for c in (CERT, BC, PAIRS, JOK):
        c.clear()
    AUTH[0] = auth
    clock = [0]
    req = {}
    fails = defaultdict(int)
    ncert = [0, 0]
    maxE = [0]
    rng = random.Random(seed)
    evid = True
    tau = 2 * N if tau is None else tau
    w = 2 * Delta if w is None else w
    chk = 'both' if twin else 'rep'
    mode = 'both' if twin else True
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
    R0 = 40

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
        cert = None
        if auth:
            J = joins(refs)
            if J:
                sig = certify(frozenset(J), j, a)
                if sig is not None:
                    cert = (frozenset(J), sig)
        b = new_block(a, j, refs, authors(cert[0]) if cert else frozenset())
        if cert:
            CERT[b] = cert
            ncert[1] += 1
        byz_at[j].setdefault(a, b)
        return b

    def tree(a, j, dep):
        if dep == 0:
            return mk(a, j, [])
        return mk(a, j, [tree(X, j - 1, dep - 1), tree(Y, j - 1, dep - 1)])

    def treeX(j, dep):
        if dep == 0:
            return mk(X, j, [])
        return mk(X, j, [treeX(j - 1, dep - 1), treeX(j - 1, dep - 1)])

    def chain_list(a, frm, to):
        out = []
        for j in range(frm, to + 1):
            out.append(mk(a, j, out[-1:]))
        return out

    def chain(a, frm, to):
        tip = None
        for j in range(frm, to + 1):
            tip = mk(a, j, [] if tip is None else [tip])
        return tip

    def fam(k, lo, hi):
        # a chain of BYZ[k] over rounds lo..hi that adopts, in its last k rounds, a
        # fresh family of each BYZ[i], i < k, in increasing order: 2^k chains
        subs = {hi - k + 1 + i: fam(i, lo, hi - k + i) for i in range(k)}
        tip = None
        for j in range(lo, hi + 1):
            tip = mk(BYZ[k], j, ([tip] if tip is not None else [])
                     + ([subs[j]] if j in subs else []))
        return tip

    def nest(s, lo, top):
        # stage s: the family of BYZ[s] below round top, its chain extended to top + s
        tip = fam(s, lo, top - 1)
        for j in range(top, top + s + 1):
            tip = mk(BYZ[s], j, [tip])
        return tip

    def signs(u, r, E, rq):
        if cap is not None and len(E) > cap:
            return False
        if rq in conv[u]:
            return False
        if sign == 'built':
            return top[u] < r
        return not any(not (pairs(x) & E) for x in diskr[u].get(r, ()))

    def certify(E, r, rq):
        # a Byzantine request, made only when it succeeds; it reaches every node
        sig = set(BYZ) | {u for u in HON if signs(u, r, E, rq)}
        if len(sig) < Q:
            return None
        maxE[0] = max(maxE[0], len(E))
        for u in HON:
            for e in authors(E):
                inbox[clock[0] + 1].append((u, 'rep', None, e))
        return frozenset(sig)

    def convict(t, v, a):
        if rule == 'none' or a in conv[v]:
            return
        conv[v][a] = t
        target[v].pop(a, None)
        if evid:
            for w in HON:
                if w != v:
                    inbox[t + hdelay(t)].append((w, 'rep', v, a))

    own_hist = {v: {gen[v]} for v in builders}
    slots = {v: defaultdict(set) for v in builders}
    for v in builders:
        slots[v][blocks[gen[v]][:2]].add(gen[v])
    waited = {v: set() for v in builders}
    wait_until = {v: -1 for v in builders}
    post = {v: False for v in builders}
    waits = {v: 0 for v in builders}
    maxnov = [0]

    def novelty(v, refs, extra=frozenset()):
        out, stack = set(), list(refs)
        while stack:
            x = stack.pop()
            if x in own_hist[v] or x in out or x in extra:
                continue
            out.add(x)
            stack.extend(blocks[x][2])
        return out

    def equivocating(v, nov):
        sl = defaultdict(set)
        for x in nov:
            sl[blocks[x][:2]].add(x)
        return {x for x in nov if len(sl[blocks[x][:2]] | slots[v][blocks[x][:2]]) > 1}

    def pick(v, base, keep_own, least):
        refs = [own[v]] if keep_own else []
        evr = frozenset(conv[v])
        tw = twins[v][base]
        pool = {a: [j for j in tw[a] if valid(chk, j, L)] for a in tw
                if a != v and a not in conv[v]}
        cur = novelty(v, refs)
        # react under auth takes join-free blocks first, and joining ones only to
        # reach a quorum
        for relax in ((False, True) if auth and not least else (True,)):
            while pool and (not least or len(refs) < Q):
                best = None
                for a in sorted(pool):
                    cands = pool[a] if least else pool[a][:1]
                    if auth and not least:
                        free = [j for j in pool[a] if not joins(refs + [j])]
                        cands = free[:1] or (pool[a][:1] if relax else [])
                    for j in cands:
                        ex, _ = analyze(refs + [j], base + 1, L, evr, mode)
                        if a in ex:
                            continue
                        size = (1 if auth and joins(refs + [j]) else 0,
                                len(novelty(v, [j], cur)) if least else 0)
                        if best is None or size < best[0]:
                            best = (size, a, j)
                    if best is not None and not least:
                        break
                if best is None:
                    break
                refs.append(best[2])
                cur |= novelty(v, [best[2]], cur)
                del pool[best[1]]
                if relax and auth and not least and len(refs) >= Q:
                    break
            if len(refs) >= Q:
                break
        return refs

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

    for t in range(ticks):
        clock[0] = t
        for v, kind, u, b in inbox.pop(t, []):
            if kind == 'rep':
                convict(t, v, b)
                continue
            if kind == 'auth':
                r, E = b
                for e in authors(E):
                    convict(t, v, e)
                if signs(v, r, E, u):
                    send(t, v, u, 'sig', b)
                else:
                    send(t, v, u, 'nosig', b)
                    for x in diskr[v].get(r, ()):
                        if sign == 'built' and blocks[x][0] == v or not pairs(x) & E:
                            send(t, v, u, 'ann', x)
                            break
                continue
            if kind in ('sig', 'nosig'):
                rq = req.get(v)
                if rq and (rq['r'], rq['E']) == b:
                    rq['sig' if kind == 'sig' else 'no'].add(u)
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
                if rule != 'none' and not valid(chk, b, L):
                    continue
                put(t, v, b)
        for v in builders:
            for u in list(target[v]):
                if target[v][u] in disk[v] or blocks[target[v][u]][1] < hz[v]:
                    del target[v][u]
        for v in builders:
            if t < wait_until[v]:
                continue
            while True:
                base = top[v]
                hi = [rd for rd in twins[v] if rd > base and
                      sum(1 for a in twins[v][rd] if a != v) >= Q]
                if hi:
                    base = max(hi)
                if sum(1 for a in twins[v][base] if a != v) < Q - 1:
                    break
                keep = base == top[v] and blocks[own[v]][1] == base
                least = rule in ('min', 'size') or (rule == 'wait' and post[v])
                refs = pick(v, base, keep, least)
                if rule == 'size':
                    new = novelty(v, refs) - waited[v]
                    if not post[v] and len(new) > tau:
                        waited[v] |= new
                        waits[v] += 1
                        wait_until[v] = t + w
                        post[v] = True
                        break
                    post[v] = False
                if rule == 'wait':
                    new = equivocating(v, novelty(v, refs)) - waited[v]
                    if new:
                        waited[v] |= new
                        waits[v] += 1
                        wait_until[v] = t + Delta
                        post[v] = True
                        break
                    post[v] = False
                if len(refs) < Q:
                    break
                cert = None
                if auth:
                    J = joins(refs)
                    cov = set()
                    if J and reuse:
                        # the certificates of round base + 1 held, cited without a request
                        for x in diskr[v].get(base + 1, ()):
                            if x in CERT:
                                cov |= CERT[x][0]
                    if J and J <= cov:
                        cert = (frozenset(J), frozenset(range(Q)))
                    elif J:
                        rq = req.get(v)
                        ok = rq is not None and rq['r'] == base + 1 and J <= rq['E']
                        if ok and len(rq['sig']) >= Q:
                            cert = (rq['E'], frozenset(rq['sig']))
                            req[v] = None
                            ncert[0] += 1
                        elif ok and len(rq['no']) <= N - Q:
                            break
                        elif ok:
                            fails[v] += 1
                            req[v] = None
                            wait_until[v] = t + Delta
                            break
                        else:
                            E = frozenset(J)
                            maxE[0] = max(maxE[0], len(E))
                            req[v] = {'r': base + 1, 'E': E, 'sig': {v},
                                      'no': set() if byzsign else set(BYZ)}
                            if byzsign:
                                req[v]['sig'] |= set(BYZ)
                            for o in HON:
                                if o != v:
                                    send(t, v, o, 'auth', (base + 1, E))
                            break
                nov = novelty(v, refs)
                maxnov[0] = max(maxnov[0], len(nov) + 1)
                r = base + 1
                b = new_block(v, r, refs, frozenset(conv[v]) if evid else frozenset())
                if cert:
                    CERT[b] = cert
                    EV[b] = EV[b] | authors(cert[0])
                put(t, v, b)
                for x in nov | {b}:
                    own_hist[v].add(x)
                    slots[v][blocks[x][:2]].add(x)
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
                elif attack == 'inject' and r in (20, 40):
                    if r == 20:
                        # X shows two honest nodes different blocks: X is detected
                        xa, xb = mk(X, r - 1, []), mk(X, r - 1, [])
                        send(t, X, HON[0], 'ann', xa)
                        send(t, X, HON[1], 'ann', xb)
                        y = mk(Y, r, [y_last])
                    else:
                        # back-dated: a tree of X twins below round 16, carried up by a
                        # fresh chain of Z to Y's block, shown to every honest node
                        x = treeX(15, d)
                        z = mk(Z, 16, [x])
                        for j in range(17, r):
                            z = mk(Z, j, [z])
                        y = mk(Y, r, [y_last, z])
                elif attack == 'bulk' and r == R0:
                    # two back-dated X chains, carried by fresh chains of Z and Y, joined
                    # at round R0 by Y's block, which must be certified
                    lo = max(1, r - depth)
                    xa, xb = chain_list(X, lo, r - 2), chain_list(X, lo, r - 2)
                    z = yb = None
                    for j in range(lo + 1, r):
                        z = mk(Z, j, ([z] if z else []) + [xa[j - 1 - lo]])
                        yb = mk(Y, j, ([yb] if yb else []) + [xb[j - 1 - lo]])
                    y = mk(Y, r, [yb, z])
                    for h in HON:
                        send(t, Y, h, 'ann', y)
                    only = []
                elif attack == 'oldjoin' and r == R0:
                    # as bulk, but Y joins at round R0 - depth, below an honest horizon
                    # of fewer rounds, and its chain carries the join up to round R0
                    jr = r - depth
                    lo = max(1, jr - 10)
                    xa, xb = chain_list(X, lo, jr - 2), chain_list(X, lo, jr - 2)
                    z = yb = None
                    for j in range(lo + 1, jr):
                        z = mk(Z, j, ([z] if z else []) + [xa[j - 1 - lo]])
                        yb = mk(Y, j, ([yb] if yb else []) + [xb[j - 1 - lo]])
                    y = mk(Y, jr, [yb, z])
                    for j in range(jr + 1, r + 1):
                        y = mk(Y, j, [y])
                    for h in HON:
                        send(t, Y, h, 'ann', y)
                    only = []
                elif attack == 'force' and R0 <= r < R0 + depth:
                    # X shows twins to two honest nodes; Y and Z feed only HON[0]
                    x1, x2 = mk(X, r, []), mk(X, r, [])
                    send(t, X, HON[1], 'ann', x1)
                    send(t, X, HON[2], 'ann', x2)
                    y = mk(Y, r, [y_last])
                    send(t, Z, HON[0], 'ann', mk(Z, r, []))
                    only = [HON[0]]
                elif attack == 'nest' and R0 <= r < R0 + F:
                    # stage r - R0: each honest node is shown its own nested family,
                    # back-dated `depth` rounds below R0, its top by BYZ[r - R0]
                    for h in HON:
                        b = nest(r - R0, max(1, R0 - max(depth, F)), R0)
                        send(t, BYZ[r - R0], h, 'ann', b)
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
                    if attack in ('nest', 'bulk', 'oldjoin', 'force'):
                        only = []
                    if attack == 'split':
                        lin = {h: {X: gen[X], Y: y} for h in HON}
                y_last = y
                for h in only:
                    send(t, Y, h, 'ann', y)
        for v in builders:
            for u, tg in list(target[v].items()):
                if rule != 'none' and not valid(chk, tg, L):
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
    hist, stack = set(), [b for rd in honest_at.values() for b in rd.values()]
    while stack:
        x = stack.pop()
        if x in hist:
            continue
        hist.add(x)
        stack.extend(blocks[x][2])
    per = defaultdict(int)
    for x in hist:
        if blocks[x][0] in BYZ:
            per[blocks[x][1]] += 1
    rounds = min(top.values())
    dB = max(sum(1 for x in disk[v] if blocks[x][0] in BYZ) for v in HON)
    late = [b for rd, hb in honest_at.items() if rd >= 30 for b in hb.values()]
    share = 1.0
    for u in HON:
        others = [b for b in late if blocks[b][0] != u]
        if others:
            share = min(share, sum(1 for b in others if any(blocks[x][0] == u
                                                            for x in blocks[b][2]))
                        / len(others))
    return {'rounds': rounds, 'byz': sum(per.values()) / max(1, rounds),
            'byzmax': max(per.values(), default=0), 'nov': maxnov[0],
            'waits': max(waits.values()), 'hist': sum(per.values()), 'disk': dB,
            'share': share, 'fails': max(fails.values(), default=0),
            'hcert': ncert[0], 'bcert': ncert[1], 'maxE': maxE[0], 'tops': dict(top),
            'req': {v: (q['r'], len(q['E']), sorted(q['sig']), sorted(q['no']))
                    for v, q in req.items() if q}}


ATTACKS = ['none', 'prefeed', 'edge', 'carrier', 'tree', 'split', 'splittree', 'filler',
           'twins', 'isolate', 'inject', 'nest', 'bulk', 'oldjoin', 'force']


def cell(res):
    return (f"{res['rounds']}r B{res['byz']:.1f}/{res['byzmax']} "
            f"N{res['nov']} W{res['waits']} S{res['share']:.2f}")


def inject_table(n, f, ticks=300):
    setup(n, f)
    print(f"inject n={n} f={f} ticks={ticks}, no horizon")
    for d in (4, 6, 8):
        for twin in (False, True):
            cells = []
            for rule in ('react', 'min', 'wait', 'size'):
                r = run('inject', rule, ticks=ticks, L=1000, d=d, twin=twin)
                cells.append(f"{r['rounds']}r H{r['hist']}/{r['byzmax']} N{r['nov']} "
                             f"D{r['disk']} W{r['waits']} S{r['share']:.2f}")
            print(f"d={d} {'twin' if twin else 'ev  '} " + ''.join(f"{c:>34}" for c in cells),
                  flush=True)


def nest_table(n, f, ticks=300):
    setup(n, f)
    print(f"nest n={n} f={f} ticks={ticks}")
    for L in (1000, 20):
        for depth in (5, 13, 39):
            for twin in (False, True):
                cells = []
                for rule in ('react', 'min', 'size'):
                    r = run('nest', rule, ticks=ticks, L=L, depth=depth, twin=twin)
                    cells.append(f"{r['rounds']}r H{r['hist']}/{r['byzmax']} N{r['nov']} "
                                 f"D{r['disk']} W{r['waits']} S{r['share']:.2f}")
                print(f"L={L:<4} depth={depth:<2} {'twin' if twin else 'ev  '} "
                      + ''.join(f"{c:>34}" for c in cells), flush=True)


def auth_table(rule, ticks=300):
    setup(10, 3)
    cfgs = [dict(), dict(twin=True), dict(auth=True)]
    atts = [('none', {}), ('prefeed', {}), ('edge', {}), ('carrier', {}), ('tree', {}),
            ('split', {}), ('splittree', {}), ('filler', {}), ('twins', {}), ('isolate', {}),
            ('inject', dict(d=8)), ('nest', dict(depth=13)), ('nest', dict(depth=39)),
            ('bulk', dict(depth=39)), ('force', dict(depth=13))]
    print(f"{rule} n=10 f=3 ticks={ticks}, no horizon: evidence, twins, certificates")
    for a, kw in atts:
        cells = []
        for ck in cfgs:
            r = run(a, rule, ticks=ticks, L=1000, **kw, **ck)
            cells.append(f"{r['rounds']}r {r['hist']}/{r['byzmax']} S{r['share']:.2f} "
                         f"F{r['fails']} E{r['maxE']}")
        print(f"{a:10}" + ''.join(f"{c:>30}" for c in cells), flush=True)


if __name__ == '__main__':
    sys.setrecursionlimit(100000)
    if sys.argv[1] == 'table':
        auth_table(sys.argv[2])
        sys.exit()
    if sys.argv[1] == 'nest':
        nest_table(int(sys.argv[2]), int(sys.argv[3]))
        sys.exit()
    if sys.argv[1] == 'inject':
        inject_table(int(sys.argv[2]), int(sys.argv[3]))
        sys.exit()
    n, f = int(sys.argv[1]), int(sys.argv[2])
    ticks = int(sys.argv[3]) if len(sys.argv) > 3 else 600
    rules = sys.argv[4].split(',') if len(sys.argv) > 4 else ['react', 'min', 'wait', 'size']
    setup(n, f)
    print(f"n={n} f={f} ticks={ticks}")
    print(f"{'attack':10}" + ''.join(f"{r:>30}" for r in rules))
    for attack in ATTACKS:
        cells = [cell(run(attack, rule, ticks=ticks)) for rule in rules]
        print(f"{attack:10}" + ''.join(f"{c:>30}" for c in cells), flush=True)
