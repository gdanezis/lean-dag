"""Phase 1 of `docs/dos-bounds.md`: the node of Stage 5 of `docs/node-sync.md`.

Each honest node decides the slots on the blocks it holds, orders each commit under
bypass below its decided horizon, keeps its ordered blocks and a proof of each
verdict, and drops every other bypassed block.

**Decisions.** Slot `s` is round `s`, led by author `s mod n`. A block of round
`s + 1` votes for a leader block it references, and a block of round `s + 2`
certifies it when it references votes of q authors. The slot commits directly on
certificates of q authors, and is skipped directly on blocks of q authors at `s + 1`
that reference no block of the leader's author. Otherwise the anchor is the first
slot from `s + 3` up that commits, the slots between skipped: the slot commits if the
anchor's history holds a certificate, and is skipped if not. The proof of a verdict
is the history, down to round `s - 1`, of the blocks that decide it.

**Bypass.** The horizon `H` of a node is its next undecided slot, and its cut is
`G = H - 1`. A block `x` of round `r` with `r + 1 < H` is bypassed when the ordered
blocks of round `r + 1` that do not reference it come from q authors. A commit orders
the leader's history from the top down, without bypassed blocks. Below the cut the
node keeps the ordered blocks, the proofs, and the blocks not bypassed.

**Admission.** A node takes a block in once each reference is held or bypassed and
the block is valid: the shape; above the cut, no reference to an author exposed by
evidence in its history within `WX` rounds; and, at any round, a certificate for the
twins it joins among the blocks the node follows, held and not bypassed (with `JOIN =
'cut'`, among the blocks at or above the cut). The builder prefers references that
join nothing, and asks every node to sign the twins it must join. A signer convicts
their authors, and refuses at or below its cut and when it holds a block of the round
whose history holds no pair of the twins; it then sends that block.

**Network.** Synchronous: a message between honest nodes takes 1 to `Delta` ticks,
and every message to the last honest node `Delta` ticks; a Byzantine message takes 1.
A node takes a broadcast block in on arrival if it can, and otherwise syncs it from
its sender, one sync a peer: the sender streams the history the node lacks and does
not find bypassed, and the node keeps the piece only if it takes in the target. A
node whose top has not moved for `STUCK` ticks asks its peers for the proof of the
verdict of its next undecided slot and, for a commit, the blocks the commit orders,
decides on the proof, and takes the blocks in with the commit (D16).

**Attacks.** `none`: each Byzantine node builds one block a round on q honest
blocks. `silent`. `lead`: as `none`, with each Byzantine leader block shown to f + 1
honest nodes only, so that its slot is decided indirectly. `twins`: as `none`, and X
shows each honest node its own block each round. `carrier`: as `none`, and Y carries
a fresh X chain `depth` rounds deep each round. `nest`: the nested families of
`sync-auth.py`, back-dated `depth` rounds. `late`: as `lead`, and when two honest
horizons differ, X builds a chain from just below the lower one up to the frontier, Y
carries it, and its lowest block is served to no node.

`python3 dos-sim.py n f [ticks]` prints, for each attack, the least top and horizon,
whether the ledgers agree, the authors every node convicted (`D`), the largest lag
`top - H`, memory (blocks from `min(G, top - 2)` up), store of a round at the end,
blocks taken in at a round, rounds where some node took in more than `n + |D|`, piece,
piece per round of its target above the cut, history of a built block at a round
above the cut, the blocks kept below the cut a round (ordered, in a proof only,
other), the blocks dropped, and the catch-ups. `nest cut` runs with `JOIN = 'cut'`;
`late deaf` cuts the last honest node off from ticks 60 to 160, outside synchrony.
"""
import random
import sys
from collections import defaultdict

blocks = []
EV = {}
CERT = {}
BC = {}
BI = {}
BIB = []
SLOT = defaultdict(list)
TWM = [0]
HIS = {}
EXP = {}
WITHHELD = set()
N = F = Q = 0
HON, BYZ = [], []
X = Y = Z = 0
WX = 10


def setup(n, f):
    global N, F, Q, HON, BYZ, X, Y, Z
    N, F, Q = n, f, n - f
    HON, BYZ = list(range(Q)), list(range(Q, N))
    X, Y, Z = BYZ[0], BYZ[1], BYZ[2 % F]


def reset():
    blocks.clear()
    for c in (EV, CERT, BC, BI, SLOT, HIS, EXP):
        c.clear()
    BIB.clear()
    TWM[0] = 0
    WITHHELD.clear()


def new_block(a, r, refs, ev=frozenset(), cert=None):
    b = len(blocks)
    blocks.append((a, r, tuple(refs)))
    EV[b] = ev
    if cert:
        CERT[b] = cert
    m = 0
    for x in refs:
        m |= BC[x]
    if a in BYZ:
        BI[b] = len(BIB)
        BIB.append(b)
        m |= 1 << BI[b]
        sl = SLOT[(a, r)]
        sl.append(b)
        if len(sl) > 1:
            for x in sl:
                TWM[0] |= 1 << BI[x]
    BC[b] = m
    return b


def twins_in(m):
    """The Byzantine blocks of the mask `m` whose slot holds a twin."""
    m &= TWM[0]
    while m:
        low = m & -m
        yield BIB[low.bit_length() - 1]
        m ^= low


def in_history(b, x):
    return (BC[b] >> BI[x]) & 1


def joins(refs, lo, keep=None):
    """The twins at or above round `lo` that a block with references `refs` joins: pairs
    of twins in its history and in the history of no single reference. With `keep`, only
    twins that pass it."""
    m = 0
    for x in refs:
        m |= BC[x]
    groups = defaultdict(list)
    for x in twins_in(m):
        if blocks[x][1] >= lo and (keep is None or keep(x)):
            groups[blocks[x][:2]].append(x)
    out = set()
    for g in groups.values():
        for i, x in enumerate(g):
            for y in g[i + 1:]:
                if not any(in_history(r, x) and in_history(r, y) for r in refs):
                    out |= {x, y}
    return frozenset(out)


def holds_pair(b, E):
    """The history of `b` holds two twins of `E`."""
    seen = set()
    for x in E:
        if in_history(b, x):
            if blocks[x][:2] in seen:
                return True
            seen.add(blocks[x][:2])
    return False


def authors(E):
    return {blocks[x][0] for x in E}


def history(b, lo):
    key = (b, lo)
    if key not in HIS:
        out, stack = set(), [b]
        while stack:
            x = stack.pop()
            if x in out or blocks[x][1] < lo:
                continue
            out.add(x)
            stack.extend(blocks[x][2])
        HIS[key] = frozenset(out)
    return HIS[key]


def exposure(b, lo):
    """The authors that `b` exposes: its evidence and that of its history at or above
    round `lo`."""
    key = (b, lo)
    if key not in EXP:
        out, seen, stack = set(EV[b]), set(), list(blocks[b][2])
        while stack:
            x = stack.pop()
            if x in seen or blocks[x][1] < lo:
                continue
            seen.add(x)
            out |= EV[x]
            stack.extend(blocks[x][2])
        EXP[key] = frozenset(out)
    return EXP[key]


# decisions, on a view given by its blocks of each round

def votes_for(byr, L, s):
    return {y for y in byr.get(s + 1, ()) if L in blocks[y][2]}


def certifies(z, vs):
    return len({blocks[y][0] for y in blocks[z][2] if y in vs}) >= Q


def direct(byr, s):
    for L in sorted(b for b in byr.get(s, ()) if blocks[b][0] == s % N):
        vs = votes_for(byr, L, s)
        cs, au = [], set()
        for z in sorted(byr.get(s + 2, ())):
            if blocks[z][0] not in au and certifies(z, vs):
                cs.append(z)
                au.add(blocks[z][0])
        if len(au) >= Q:
            return L, frozenset([L] + cs[:Q])
    nv, au = [], set()
    for y in sorted(byr.get(s + 1, ())):
        if blocks[y][0] not in au and not any(blocks[x][0] == s % N for x in blocks[y][2]):
            nv.append(y)
            au.add(blocks[y][0])
    if len(au) >= Q:
        return None, frozenset(nv[:Q])
    return False


def decide(byr, lo, top):
    """The verdicts of the slots from `lo` decided on the view `byr`, each with the
    blocks that decide it."""
    ver = {}
    for s in range(top, lo - 1, -1):
        d = direct(byr, s)
        if d is not False:
            ver[s] = d
            continue
        trig = set()
        for s2 in range(s + 3, top + 1):
            if s2 not in ver:
                break
            L2, t2 = ver[s2]
            trig |= t2
            if L2 is None:
                continue
            h = history(L2, s + 2)
            cs = [L for L in sorted(byr.get(s, ())) if blocks[L][0] == s % N and any(
                blocks[z][1] == s + 2 and certifies(z, votes_for(byr, L, s)) for z in h)]
            ver[s] = (cs[0] if cs else None, frozenset(trig | set(cs[:1])))
            break
    return ver


def by_round(bs):
    byr = defaultdict(set)
    for b in bs:
        byr[blocks[b][1]].add(b)
    return byr


def missing(tg, node, src):
    """The history of `tg` that `node` lacks and does not find bypassed, as far as
    the source holds it."""
    out, seen, stack = [], {tg}, [tg]
    while stack:
        x = stack.pop()
        if x in node.disk or node.bypassed(x) or not src(x):
            continue
        out.append(x)
        for r in blocks[x][2]:
            if r not in seen:
                seen.add(r)
                stack.append(r)
    return out


class Node:
    def __init__(self, sim, v, gen):
        self.sim, self.v = sim, v
        self.disk, self.at = set(), defaultdict(lambda: defaultdict(list))
        self.proof, self.pf = set(), {}
        self.C, self.Crnd = set(gen), defaultdict(set)
        self.Crnd[0] = set(gen)
        self.byp, self.notb = set(), {}
        self.conv = {}
        self.lo, self.g, self.ledger = 1, {}, {}
        self.below, self.dp = set(), 0
        self.top = 0
        self.target, self.pending, self.backoff = {}, {}, {}
        self.req, self.wait_until, self.qt = None, -1, {}
        self.moved, self.mtop, self.asked = 0, 0, -10 ** 9
        self.dirty = True
        self.taken = defaultdict(int)
        self.mem = self.piece = self.pratio = self.fetched = self.hist = 0
        self.lag = self.ndrop = self.ncu = self.cubad = 0
        for b in gen:
            self.add(b)
            self.effects(b)

    def has(self, x):
        return x in self.disk or x in self.proof

    def bypassed(self, x):
        if x in self.byp:
            return True
        r = blocks[x][1]
        if r + 1 >= self.lo or x in self.C:
            return False
        above = self.Crnd.get(r + 1, ())
        if self.notb.get(x) == len(above):
            return False
        if len({blocks[y][0] for y in above if x not in blocks[y][2]}) >= Q:
            self.byp.add(x)
            return True
        self.notb[x] = len(above)
        return False

    def ready(self, b):
        return all(x in self.disk or self.bypassed(x) for x in blocks[b][2])

    def valid(self, b):
        a, r, refs = blocks[b]
        if r == 0:
            return True
        au = {blocks[x][0] for x in refs}
        if len(au) != len(refs) or len(au) < Q or any(blocks[x][1] != r - 1 for x in refs):
            return False
        G = self.lo - 1
        if r > G and au & exposure(b, max(G, r - WX)):
            return False
        J = self.joins(refs)
        if J:
            c = CERT.get(b)
            if c is None or not J <= c[0] or len(c[1]) < Q:
                return False
        return True

    def add(self, b):
        a, r, _ = blocks[b]
        self.disk.add(b)
        self.at[r][a].append(b)
        self.dirty = True

    def remove(self, b):
        a, r, _ = blocks[b]
        self.disk.discard(b)
        self.at[r][a].remove(b)
        if not self.at[r][a]:
            del self.at[r][a]

    def effects(self, b):
        a, r, _ = blocks[b]
        self.taken[r] += 1
        if r + 1 < self.lo:
            self.below.add(b)
        if len(self.at[r][a]) > 1:
            self.convict(a)
        for e in EV[b]:
            self.convict(e)

    def convict(self, a):
        if a in self.conv:
            return
        self.conv[a] = self.sim.t
        self.target.pop(a, None)
        for u in HON:
            if u != self.v:
                self.sim.send(self.v, u, 'rep', a)

    def follows(self, x):
        return x in self.disk and not self.bypassed(x)

    def joins(self, refs):
        """The twins a block with references `refs` joins, of blocks the node follows;
        with `JOIN = 'cut'`, of blocks at or above its cut."""
        if JOIN == 'cut':
            return joins(refs, self.lo - 1)
        return joins(refs, 0, self.follows)

    def nauth(self, r):
        return sum(1 for a in self.at.get(r, {}) if a not in self.conv)

    def blocks_at(self, r):
        return [b for bs in self.at.get(r, {}).values() for b in bs]

    # decisions and the ledger

    def flush(self, L, s, extra=frozenset()):
        if L in self.C:
            return []
        out, layer = [L], [L]
        while layer:
            r = blocks[layer[0]][1] - 1
            wit = self.Crnd.get(r + 1, set()) | set(layer)
            nxt = set()
            for y in layer:
                for x in blocks[y][2]:
                    if x in self.C or x in nxt:
                        continue
                    if r + 1 < s and len({blocks[w][0] for w in wit
                                          if x not in blocks[w][2]}) >= Q:
                        continue
                    nxt.add(x)
            assert all(x in self.disk or x in extra for x in nxt), "a commit reads a block not held"
            layer = sorted(nxt)
            out += layer
        return out

    def apply(self, s, L, proof, extra=frozenset()):
        self.proof |= proof
        self.pf[s] = proof
        fl = []
        if L is not None:
            fl = self.flush(L, s, extra)
            for x in fl:
                if x not in self.disk:
                    self.add(x)
                    self.effects(x)
                self.C.add(x)
                self.Crnd[blocks[x][1]].add(x)
        self.ledger[s] = (L, frozenset(fl))
        self.g[s] = L
        self.lo = s + 1
        self.drop()

    def advance(self):
        if not self.dirty:
            return
        self.dirty = False
        lo = self.lo
        byr = {r: set(b for bs in self.at[r].values() for b in bs)
               for r in list(self.at) if r >= lo - 1}
        if not byr:
            return
        ver = decide(byr, lo, max(byr))
        while self.lo in ver:
            s = self.lo
            L, trig = ver[s]
            proof = set()
            for b in trig:
                proof |= history(b, s - 1)
            self.apply(s, L, frozenset(proof))

    def drop(self):
        for r in range(self.dp, self.lo - 1):
            for bs in self.at.get(r, {}).values():
                self.below.update(bs)
        self.dp = max(self.dp, self.lo - 1)
        for x in list(self.below):
            if x in self.C or x in self.proof or x not in self.disk:
                self.below.discard(x)
            elif self.bypassed(x):
                self.remove(x)
                self.below.discard(x)
                self.ndrop += 1

    # messages

    def receive(self, kind, u, p):
        sim = self.sim
        if kind == 'rep':
            self.convict(p)
        elif kind == 'ann':
            if u in self.conv or self.has(p) or self.bypassed(p):
                return
            if self.ready(p) and self.valid(p):
                self.add(p)
                self.effects(p)
            else:
                cur = self.target.get(u)
                if cur is None or blocks[cur][1] < blocks[p][1]:
                    self.target[u] = p
        elif kind == 'piece':
            self.pending.pop(u, None)
            self.take(*p, u)
        elif kind == 'auth':
            r, E = p
            for a in authors(E):
                self.convict(a)
            if self.signs(r, E, u):
                sim.send(self.v, u, 'sig', p)
            else:
                sim.send(self.v, u, 'nosig', p)
                for x in self.blocks_at(r):
                    if not holds_pair(x, E):
                        sim.send(self.v, u, 'ann', x)
                        break
        elif kind in ('sig', 'nosig'):
            rq = self.req
            if rq and (rq['r'], rq['E']) == p:
                rq['sig' if kind == 'sig' else 'no'].add(u)
        elif kind == 'cu':
            if p in self.ledger:
                L, fl = self.ledger[p]
                sim.send(self.v, u, 'cur', (p, L, self.pf[p], fl))
        elif kind == 'cur':
            s, L, P, fl = p
            if s != self.lo:
                return
            ver = decide(by_round(P), s, max(blocks[b][1] for b in P))
            if s not in ver or ver[s][0] != L:
                self.cubad += 1
                return
            self.ncu += 1
            self.apply(s, L, P, fl)
            assert set(self.ledger[s][1]) == set(fl), "catch-up orders other blocks"
            self.dirty = True

    def signs(self, r, E, u):
        return (r > self.lo - 1 and u not in self.conv
                and all(holds_pair(x, E) for x in self.blocks_at(r)))

    def take(self, tg, piece, u):
        """Header first: keep the piece only if the target is then held."""
        self.fetched += len(piece)
        added = []
        for b in sorted(piece, key=lambda x: (blocks[x][1], x)):
            if b in self.disk:
                continue
            if self.ready(b) and self.valid(b):
                self.add(b)
                added.append(b)
        if tg in self.disk:
            for b in added:
                self.effects(b)
            self.piece = max(self.piece, len(piece))
            self.pratio = max(self.pratio,
                              len(piece) / max(1, blocks[tg][1] - (self.lo - 1) + 1))
        else:
            for b in added:
                self.remove(b)
            self.backoff[u] = self.sim.t + DELTA

    def sync(self):
        sim = self.sim
        for u, tg in list(self.target.items()):
            if self.has(tg) or self.bypassed(tg) or u in self.conv:
                del self.target[u]
                continue
            if sim.t < self.pending.get(u, -1) + 2 * DELTA + 1 or sim.t < self.backoff.get(u, 0):
                continue
            src = sim.nodes[u].has if u in HON else (lambda x: x not in WITHHELD)
            self.pending[u] = sim.t
            sim.send(u, self.v, 'piece', (tg, missing(tg, self, src)))

    def build(self):
        sim, t = self.sim, self.sim.t
        if t < self.wait_until:
            return
        base = self.top
        hi = [r for r in list(self.at) if r > base and self.nauth(r) >= Q]
        if hi:
            base = max(hi)
        if self.nauth(base) < Q:
            return
        self.qt.setdefault(base, t)
        if not self.at[base].get(base % N) and t < self.qt[base] + DELTA:
            return
        G = self.lo - 1
        refs, au = [], set()
        for relax in (False, True):
            for a in sorted(self.at[base], key=lambda a: (a != self.v, a)):
                if a in au or a in self.conv or (relax and len(au) >= Q):
                    continue
                for j in self.at[base][a]:
                    if relax or not self.joins(refs + [j]):
                        refs.append(j)
                        au.add(a)
                        break
            if len(au) >= Q:
                break
        if len(au) < Q:
            return
        cert = None
        J = self.joins(refs)
        if J:
            r, rq = base + 1, self.req
            if rq and rq['r'] == r and J <= rq['E']:
                if len(rq['sig']) >= Q:
                    cert = (rq['E'], frozenset(rq['sig']))
                    self.req = None
                elif len(rq['no']) > N - Q:
                    self.req = None
                    self.wait_until = t + DELTA
                    return
                else:
                    return
            else:
                E = frozenset(J)
                self.req = {'r': r, 'E': E, 'sig': {self.v}, 'no': set(BYZ)}
                for a in authors(E):
                    self.convict(a)
                for u in HON:
                    if u != self.v:
                        sim.send(self.v, u, 'auth', (r, E))
                return
        b = new_block(self.v, base + 1, refs, frozenset(self.conv), cert)
        self.add(b)
        self.effects(b)
        self.top = base + 1
        sim.honest_at[base + 1][self.v] = b
        hb = defaultdict(int)
        for x in history(b, G):
            hb[blocks[x][1]] += 1
        self.hist = max(self.hist, max(hb.values()))
        for u in HON:
            if u != self.v:
                sim.send(self.v, u, 'ann', b)

    def catchup(self):
        t = self.sim.t
        if self.top > self.mtop:
            self.mtop, self.moved = self.top, t
        elif t - self.moved >= STUCK and t - self.asked >= STUCK:
            self.asked = t
            for u in HON:
                if u != self.v:
                    self.sim.send(self.v, u, 'cu', self.lo)

    def measure(self):
        floor = min(self.lo - 1, self.top - 2)
        self.mem = max(self.mem, sum(len(bs) for r in self.at if r >= floor
                                     for bs in self.at[r].values()))
        self.lag = max(self.lag, self.top - self.lo)


DELTA = 3
STUCK = 12
JOIN = 'follow'


class Sim:
    def __init__(self, attack, ticks, depth, seed, deaf=None):
        reset()
        self.deaf = deaf
        self.attack, self.ticks, self.depth = attack, ticks, depth
        self.rng = random.Random(seed)
        self.t = 0
        self.inbox = defaultdict(list)
        gen = [new_block(a, 0, []) for a in range(N)]
        self.honest_at = defaultdict(dict)
        self.honest_at[0] = {a: gen[a] for a in HON}
        self.byz_at = defaultdict(dict)
        self.nodes = {v: Node(self, v, gen) for v in HON}
        self.r = 1
        self.xlast = 0
        self.nlate = 0

    def send(self, u, v, kind, p):
        if v not in HON:
            return
        if u in BYZ:
            d = 1
        elif v == HON[-1]:
            d = DELTA
        else:
            d = self.rng.randint(1, DELTA)
        self.inbox[self.t + d].append((v, kind, u, p))

    # the attacker sees every block

    def certify(self, E, r, a):
        sig = set(BYZ) | {u for u in HON if self.nodes[u].signs(r, E, a)}
        for u in HON:
            for e in authors(E):
                self.inbox[self.t + 1].append((u, 'rep', a, e))
        return frozenset(sig) if len(sig) >= Q else None

    def mk(self, a, j, extra):
        hb = self.honest_at[j - 1]
        have = {blocks[x][0] for x in extra}
        refs = list(extra) + [hb[h] for h in sorted(hb) if h not in have][:Q - len(extra)]
        have = {blocks[x][0] for x in refs}
        for o in [a] + BYZ:
            if len(refs) < Q and o not in have and o in self.byz_at[j - 1]:
                refs.append(self.byz_at[j - 1][o])
                have.add(o)
        cert = None
        J = joins(refs, 0)
        if J:
            sig = self.certify(frozenset(J), j, a)
            if sig is not None:
                cert = (frozenset(J), sig)
        b = new_block(a, j, refs, authors(cert[0]) if cert else frozenset(), cert)
        self.byz_at[j].setdefault(a, b)
        return b

    def chain(self, a, frm, to):
        out = []
        for j in range(frm, to + 1):
            out.append(self.mk(a, j, out[-1:]))
        return out

    def fam(self, k, lo, hi):
        subs = {hi - k + 1 + i: self.fam(i, lo, hi - k + i) for i in range(k)}
        tip = None
        for j in range(lo, hi + 1):
            tip = self.mk(BYZ[k], j, ([tip] if tip is not None else [])
                          + ([subs[j]] if j in subs else []))
        return tip

    def nest(self, s, lo, top):
        tip = self.fam(s, lo, top - 1)
        for j in range(top, top + s + 1):
            tip = self.mk(BYZ[s], j, [tip])
        return tip

    def show(self, a, b, to=None):
        for h in HON if to is None else to:
            self.send(a, h, 'ann', b)

    def adversary(self):
        r, att = self.r, self.attack
        if att == 'late':
            # a chain of X from just below the lowest horizon up to the frontier, carried
            # by Y; its lowest block is served to no node
            los = [self.nodes[h].lo for h in HON]
            lo, R = min(los) - 1, max(nd.top for nd in self.nodes.values())
            if (max(los) - 2 >= lo >= 1 and lo > self.xlast and R - 1 > lo
                    and len(self.honest_at[R - 1]) >= Q - 1 and Y not in self.byz_at[R]):
                xs = self.chain(X, lo, R - 1)
                WITHHELD.add(xs[0])
                self.xlast = R - 1
                self.nlate += 1
                self.show(Y, self.mk(Y, R, [xs[-1]]))
        if len(self.honest_at[r - 1]) < (Q - 1 if self.deaf else Q):
            return
        self.r += 1
        if att == 'silent':
            return
        R0 = 40
        if att == 'nest':
            if R0 <= r < R0 + F:
                for h in HON:
                    self.show(BYZ[r - R0], self.nest(r - R0, max(1, R0 - self.depth), R0), [h])
            return
        busy = set()
        if att == 'twins' and r > 1:
            for h in HON:
                self.show(X, self.mk(X, r, []), [h])
            busy.add(X)
        if att == 'carrier' and r > self.depth + 2:
            self.show(Y, self.mk(Y, r, [self.chain(X, r - self.depth, r - 1)[-1]]))
            busy |= {X, Y}
        if att == 'late':
            busy |= {X, Y}
        for a in BYZ:
            if a in busy:
                continue
            b = self.mk(a, r, [])
            lead = att in ('lead', 'late') and r % N == a
            self.show(a, b, HON[:F + 1] if lead else None)

    def run(self):
        for t in range(self.ticks):
            self.t = t
            for v, kind, u, p in self.inbox.pop(t, []):
                if self.deaf and v == HON[-1] and self.deaf[0] <= t < self.deaf[1]:
                    continue
                self.nodes[v].receive(kind, u, p)
            for nd in self.nodes.values():
                nd.advance()
                nd.sync()
                nd.build()
                nd.advance()
                nd.catchup()
                nd.measure()
            self.adversary()
        return self.report()

    def report(self):
        nds = list(self.nodes.values())
        agree = all(a.ledger[s] == b.ledger[s] for a in nds for b in nds
                    for s in a.ledger if s in b.ledger)
        D = set.intersection(*(set(nd.conv) for nd in nds))
        kept = [0, 0, 0]
        rounds = 0
        for nd in nds:
            for r in range(1, nd.lo - 1):
                bs = set(b for b in nd.blocks_at(r)) | {b for b in nd.proof if blocks[b][1] == r}
                kept[0] += sum(1 for b in bs if b in nd.C)
                kept[1] += sum(1 for b in bs if b not in nd.C and b in nd.proof)
                kept[2] += sum(1 for b in bs if b not in nd.C and b not in nd.proof)
                rounds += 1
        over = 0
        for r in range(1, min(nd.top for nd in nds) + 1):
            if max(nd.taken[r] for nd in nds) > N + len(D):
                over += 1
        store = max(max((sum(1 for b in nd.disk | nd.proof if blocks[b][1] == r)
                         for r in range(1, nd.top + 1)), default=0) for nd in nds)
        return {'top': min(nd.top for nd in nds), 'lo': min(nd.lo for nd in nds),
                'agree': agree, 'D': len(D),
                'lag': max(nd.lag for nd in nds), 'mem': max(nd.mem for nd in nds),
                'store': store, 'taken': max(max(nd.taken.values()) for nd in nds),
                'piece': max(nd.piece for nd in nds),
                'pratio': max(nd.pratio for nd in nds), 'hist': max(nd.hist for nd in nds),
                'kept': [k / max(1, rounds) for k in kept],
                'drop': sum(nd.ndrop for nd in nds), 'cu': sum(nd.ncu for nd in nds),
                'cubad': sum(nd.cubad for nd in nds), 'late': self.nlate, 'over': over,
                'certs': sum(1 for b in CERT if blocks[b][0] in HON),
                'bcerts': sum(1 for b in CERT if blocks[b][0] in BYZ)}


ATTACKS = [('none', {}), ('silent', {}), ('lead', {}), ('twins', {}), ('carrier', dict(depth=8)),
           ('nest', dict(depth=13)), ('nest', dict(depth=39)), ('late', {}),
           ('nest', dict(depth=13, join='cut')), ('nest', dict(depth=39, join='cut')),
           ('late', dict(deaf=(60, 160)))]


def table(n, f, ticks):
    global JOIN
    setup(n, f)
    print(f"n={n} f={f} ticks={ticks} Delta={DELTA}: n + f = {n + f}, "
          f"n + f(f+1)/2 = {n + f * (f + 1) // 2}")
    print(f"{'attack':16}{'top':>5}{'H':>5}{'agree':>6}{'D':>3}{'lag':>4}{'mem':>5}"
          f"{'store':>6}{'taken':>6}{'over':>5}{'piece':>6}{'p/r':>6}{'hist':>5}"
          f"{'kept o/p/x':>15}{'drop':>6}{'cu':>3}")
    for a, kw in ATTACKS:
        JOIN = kw.get('join', 'follow')
        res = Sim(a, ticks, kw.get('depth', 8), 1, kw.get('deaf')).run()
        JOIN = 'follow'
        k = res['kept']
        name = a + (f"/{kw['depth']}" if 'depth' in kw else '') + (
            ' cut' if 'join' in kw else '') + (' deaf' if 'deaf' in kw else '')
        print(f"{name:16}{res['top']:>5}{res['lo']:>5}{str(res['agree']):>6}{res['D']:>3}"
              f"{res['lag']:>4}{res['mem']:>5}{res['store']:>6}{res['taken']:>6}"
              f"{res['over']:>5}{res['piece']:>6}{res['pratio']:>6.1f}{res['hist']:>5}"
              f"{k[0]:>6.1f}/{k[1]:.1f}/{k[2]:.1f}{res['drop']:>6}{res['cu']:>3}",
              flush=True)


if __name__ == '__main__':
    sys.setrecursionlimit(100000)
    table(int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]) if len(sys.argv) > 3 else 300)
