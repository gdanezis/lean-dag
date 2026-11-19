"""Discrete-event simulator of the sparse K-partial DAG synchroniser.

Honest case: every validator is correct and none equivocates. The network
delays each packet by a base one-way latency, a random jitter (which reorders
packets) and the sender's uplink queue, and drops each packet independently.

Consensus follows rules R2--R4 of the paper, simplified to the honest case:

* a block is admitted once all its fragments are held, its references are
  admitted, a quorum of the round below is admitted, and for each leader block
  it claims, that block and votes for it from t_v = q authors are admitted
  (R2);
* a validator at highest quorum round r builds at r + 1 once it holds the
  leader block of r and votes from a quorum for the leader block of r - 1,
  after a grace period; or after a timeout from the quorum; or at once when
  f + 1 others hold blocks of r + 1 (R3);
* a leader's block, or a block after a gap, is dense; others are sparse and
  reference the author's latest block and the leader block (R4);
* a leader block L of round r commits at a validator once it admits a quorum
  of round r + 2 blocks that claim L, and a block of round r + 2 claims L when
  its author held votes from a quorum for L.

Synchroniser strategies (all push every block, fragmented, to every peer):

* ``pull``  : when a validator holds a block whose references it lacks, or part
  of a block, it waits ``pull_timer`` (no wait when it holds blocks from f + 1
  authors two rounds above its quorum round) and asks that block's author for every
  block of the block's window that the requester lacks, in one request, and
  retries (R2);
* ``coded`` : as ``pull``, and each receiver gets ``symbols`` coded symbols per
  round, each the XOR of a random subset of the sender's fragments of the last
  ``span`` rounds, decoded by Gaussian elimination over GF(2). A validator sends
  them when it first holds a quorum of a round (``trigger = "quorum"``), or
  when it builds, over the rounds below its new block (``trigger = "build"``);
* ``relay`` : as ``coded``, but each symbol is one random fragment, uncoded.

Fragments are indexed globally; a set of fragments is a Python int bitmask,
and a coded symbol is the bitmask of the fragments it XORs.
"""

from __future__ import annotations

import heapq
import math
import random
from dataclasses import dataclass, field

WIRE = 80  # IPv6 + UDP + authenticated-encryption framing, bytes per packet
FRAG_HEADER = 19
SYM_HEADER = 40
REQ_BYTES = 64


@dataclass
class Config:
    n: int = 50
    rounds: int = 40  # leader rounds measured end at this round
    warmup: int = 5  # rounds excluded from the statistics
    payload: int = 10_000  # mean payload bytes per block
    payload_sigma: float = 0.5  # lognormal spread of payloads (0 = fixed)
    frag: int = 1380  # fragment size F
    ref_bytes: int = 44  # digest + length
    header: int = 150  # author, round, signature, claims
    uplink_bps: float = 1e9
    lat_min: float = 0.005  # one-way base latency range, seconds
    lat_max: float = 0.120
    jitter: float = 0.005  # mean of exponential per-packet jitter
    loss: float = 0.01  # per-packet drop probability
    bad_links: float = 0.0  # fraction of directed links with loss bad_loss
    bad_loss: float = 0.2
    strategy: str = "coded"  # pull | coded | relay
    pull_timer: float = 0.5
    retry_timer: float = 0.5
    symbols: int | None = None  # per receiver per round; None = auto
    density: int = 1  # each fragment in a symbol with probability 2^-density
    span: int = 2  # rounds below the new block that symbols cover
    size_class: int = 0  # a symbol XORs fragments of one size class, rounded up to this (0: one class, F)
    early: float | None = None  # also send symbols over the current round this long after building
    trigger: str = "quorum"  # send symbols on a new quorum round, or on building (rounds below)
    trigger_delay: float = 0.0  # with trigger = quorum, wait this long after the quorum
    grace: float = 0.0
    round_timeout: float = 1.0
    K: int = 6  # window depth
    window_pull: bool = True  # a pull asks for the whole window to depth K, not one block
    behind_pull: bool = True  # pull at once when f + 1 others are two rounds ahead
    check_claims: bool = True  # R2: admit a block only when holding the votes behind its claims
    outage: tuple | None = None  # (validator, start, duration): it receives nothing meanwhile
    seed: int = 1

    @property
    def f(self) -> int:
        return (self.n - 1) // 3

    @property
    def q(self) -> int:
        return self.n - self.f


def poisson_quantile(lam: float, prob: float) -> int:
    k, term = 0, math.exp(-lam)
    cdf = term
    while cdf < prob:
        k += 1
        term *= lam / k
        cdf += term
    return k


def auto_symbols(cfg: Config) -> int:
    """d_f at the 99.9th percentile plus 3, over the rounds symbols cover."""
    mean_size = cfg.header + cfg.payload + 2 * cfg.ref_bytes
    frags = cfg.span * cfg.n * math.ceil(mean_size / cfg.frag)
    p = cfg.loss * (1 - cfg.bad_links) + cfg.bad_loss * cfg.bad_links
    return poisson_quantile(p * frags, 0.999) + 3


@dataclass
class Block:
    bid: int
    author: int
    rnd: int
    refs: list[int]
    claims: list[int]
    size: int
    nfrag: int
    base: int
    built: float
    leader: bool

    @property
    def mask(self) -> int:
        return ((1 << self.nfrag) - 1) << self.base


@dataclass
class Node:
    vid: int
    frags: int = 0
    known: set = field(default_factory=set)
    complete: set = field(default_factory=set)
    pending: set = field(default_factory=set)
    admitted: set = field(default_factory=set)
    by_round: dict = field(default_factory=dict)  # round -> set of authors
    votes: dict = field(default_factory=dict)  # leader bid -> count
    claims: dict = field(default_factory=dict)  # leader bid -> count
    leader_at: dict = field(default_factory=dict)  # round -> admitted leader bid
    committed: set = field(default_factory=set)
    next_undecided: int = 1
    pulling: set = field(default_factory=set)
    newest: int = 0  # highest round of a block seen
    held_by_round: dict = field(default_factory=dict)  # round -> authors of complete blocks
    ahead: int = 0  # highest round with complete blocks from f + 1 authors
    asked: dict = field(default_factory=dict)  # bid -> time an outstanding request covering it expires
    qround: int = 0
    latest: int = 0
    own: int | None = None
    timers: set = field(default_factory=set)
    rows: list = field(default_factory=list)  # (round tag, mask)
    rowunion: int = 0


class Sim:
    def __init__(self, cfg: Config):
        self.cfg = cfg
        self.rng = random.Random(cfg.seed)
        n = cfg.n
        self.s = cfg.symbols if cfg.symbols is not None else auto_symbols(cfg)
        pts = [(self.rng.random(), self.rng.random()) for _ in range(n)]
        self.lat = [[0.0] * n for _ in range(n)]
        self.lossp = [[cfg.loss] * n for _ in range(n)]
        for i in range(n):
            for j in range(n):
                if i != j:
                    d = math.dist(pts[i], pts[j]) / math.sqrt(2)
                    self.lat[i][j] = cfg.lat_min + (cfg.lat_max - cfg.lat_min) * d
                    if self.rng.random() < cfg.bad_links:
                        self.lossp[i][j] = cfg.bad_loss
        self.nodes = [Node(v) for v in range(n)]
        self.up_free = [0.0] * n
        self.blocks: list[Block] = []
        self.owner: list[int] = []  # fragment index -> bid
        self.round_mask: dict[int, int] = {}
        self.windows: dict[int, list[int]] = {}
        self.fsize: list[int] = []  # fragment index -> data bytes
        self.class_mask: dict[int, dict[int, int]] = {}  # round -> size class -> fragments
        self.leader_bid: dict[int, int] = {}
        self.q: list = []
        self.seq = 0
        self.now = 0.0
        self.stop_round = cfg.rounds + 6
        # statistics
        self.bytes = {"push": 0, "sym": 0, "pullreq": 0, "pullresp": 0}
        self.dup_frags = 0
        self.decoded = 0
        self.pulls = 0
        self.deliver: list[float] = []
        self.commit: list[float] = []  # decision latency of each leader at each node
        self.direct = 0
        self.symbols_sent = 0
        self.caught_up: float | None = None
        self.round_start: dict[int, list[float]] = {}

    # ------------------------------------------------------------ events
    def at(self, t: float, kind: str, *args) -> None:
        self.seq += 1
        heapq.heappush(self.q, (t, self.seq, kind, args))

    def run(self, horizon: float = 600.0) -> None:
        for v in range(self.cfg.n):
            self.build(self.nodes[v], 1)
        while self.q:
            t, _, kind, args = heapq.heappop(self.q)
            if t > horizon:
                break
            self.now = t
            getattr(self, "on_" + kind)(*args)

    # ------------------------------------------------------------ network
    def transmit(self, src: int, dst: int, size: int) -> float | None:
        """Queue one packet on src's uplink; its arrival time, or None if lost."""
        start = max(self.now, self.up_free[src])
        done = start + (size + WIRE) * 8 / self.cfg.uplink_bps
        self.up_free[src] = done
        if self.rng.random() < self.lossp[src][dst]:
            return None
        o = self.cfg.outage
        if o is not None and dst == o[0] and o[1] <= self.now < o[1] + o[2]:
            return None
        return done + self.lat[src][dst] + self.rng.expovariate(1 / self.cfg.jitter)

    def send_frags(self, src: int, dst: int, blk: Block, mask: int, kind: str) -> None:
        """Send the fragments of blk in mask, one packet each, back to back on
        src's uplink; deliver the ones not lost together at the last arrival (a
        block is usable only when complete). Drawn at once: the lost fragments
        by geometric gaps, the last arrival as the uplink finishing time plus the
        latency plus the largest of the jitters."""
        cfg = self.cfg
        js = [j for j in range(blk.nfrag) if mask >> (blk.base + j) & 1]
        if not js:
            return
        sizes = sum(FRAG_HEADER + min(cfg.frag, blk.size - j * cfg.frag) + WIRE for j in js)
        self.bytes[kind] += sizes
        start = max(self.now, self.up_free[src])
        done = start + sizes * 8 / cfg.uplink_bps
        self.up_free[src] = done
        o = cfg.outage
        if o is not None and dst == o[0] and o[1] <= self.now < o[1] + o[2]:
            return
        p = self.lossp[src][dst]
        lost = set()
        if p > 0:
            i = -1
            lg = math.log(1 - p)
            while True:
                i += int(math.log(1 - self.rng.random()) / lg) + 1
                if i >= len(js):
                    break
                lost.add(i)
        got = 0
        for i, j in enumerate(js):
            if i not in lost:
                got |= 1 << (blk.base + j)
        k = len(js) - len(lost)
        if k:
            jit = -cfg.jitter * math.log(1 - self.rng.random() ** (1 / k))
            self.at(done + self.lat[src][dst] + jit, "frags", dst, got, blk.bid)

    # ------------------------------------------------------------ building
    def build(self, u: Node, R: int) -> None:
        cfg = self.cfg
        if R > self.stop_round or u.latest >= R:
            return
        r = R - 1
        lead = u.leader_at.get(r)
        is_leader = R % cfg.n == u.vid
        if R == 1:
            refs = []
        elif is_leader or u.latest < r or lead is None:
            refs = [b for b in self.round_blocks(u, r)]
            if u.own is not None and self.blocks[u.own].rnd != r:
                refs.append(u.own)
        else:
            refs = [u.own, lead]
        claims = []
        Lp = u.leader_at.get(R - 2)
        if Lp is not None and u.votes.get(Lp, 0) >= cfg.q:
            claims = [Lp]
        pay = cfg.payload
        if cfg.payload_sigma > 0 and cfg.payload > 0:
            mu = math.log(cfg.payload) - cfg.payload_sigma ** 2 / 2
            pay = int(self.rng.lognormvariate(mu, cfg.payload_sigma))
        size = cfg.header + len(refs) * cfg.ref_bytes + pay
        nfrag = max(1, math.ceil(size / cfg.frag))
        blk = Block(len(self.blocks), u.vid, R, refs, claims, size, nfrag,
                    len(self.owner), self.now, is_leader)
        self.blocks.append(blk)
        self.owner.extend([blk.bid] * nfrag)
        self.round_mask[R] = self.round_mask.get(R, 0) | blk.mask
        for j in range(nfrag):
            data = min(cfg.frag, size - j * cfg.frag)
            self.fsize.append(data)
            cm = self.class_mask.setdefault(R, {})
            c = self.size_class(data)
            cm[c] = cm.get(c, 0) | 1 << (blk.base + j)
        if is_leader:
            self.leader_bid[R] = blk.bid
        self.round_start.setdefault(R, []).append(self.now)
        o = cfg.outage
        if (o is not None and u.vid == o[0] and self.caught_up is None
                and self.now > o[1] + o[2]):
            others = sorted(w.latest for w in self.nodes if w.vid != u.vid)
            if R >= others[len(others) // 2]:
                self.caught_up = self.now - (o[1] + o[2])
        u.latest = R
        u.own = blk.bid
        u.frags |= blk.mask
        u.known.add(blk.bid)
        u.complete.add(blk.bid)
        self.admit(u, blk, own=True)
        # push to every peer, in random order
        peers = [w for w in range(cfg.n) if w != u.vid]
        self.rng.shuffle(peers)
        for w in peers:
            self.send_frags(u.vid, w, blk, blk.mask, "push")
        if cfg.strategy in ("coded", "relay") and cfg.trigger == "build" and R > cfg.span:
            self.send_symbols(u, R, range(R - cfg.span, R))
        if cfg.strategy in ("coded", "relay") and cfg.early is not None:
            self.at(self.now + cfg.early, "early", u.vid, R)
        self.after_change(u)

    def round_blocks(self, u: Node, r: int) -> list[int]:
        return [b for b in u.admitted if self.blocks[b].rnd == r]

    def on_quorum_symbols(self, v: int, r: int) -> None:
        self.send_symbols(self.nodes[v], r + 1, range(r + 1 - self.cfg.span, r + 1))

    def on_early(self, v: int, R: int) -> None:
        self.send_symbols(self.nodes[v], R + 1, [R], salt=1)

    def size_class(self, data: int) -> int:
        c = self.cfg.size_class
        return self.cfg.frag if c <= 0 else min(self.cfg.frag, -(-data // c) * c)

    def send_symbols(self, u: Node, R: int, rounds, salt: int = 0) -> None:
        """Coded symbols over ``rounds``. Each size class of fragments is its own
        code: a symbol XORs a random subset of the sender's fragments of one
        class and is as long as the class. A class with m held fragments gets
        d at its 99.9th percentile plus 3 symbols per receiver on average, d
        Poisson with mean p * m; a fixed ``symbols`` is shared by fragment count.
        Distinct receivers when the count is below n."""
        cfg = self.cfg
        held: dict[int, int] = {}
        for k in rounds:
            for c, m in self.class_mask.get(k, {}).items():
                if u.frags & m:
                    held[c] = held.get(c, 0) | (u.frags & m)
        if not held:
            return
        p = cfg.loss * (1 - cfg.bad_links) + cfg.bad_loss * cfg.bad_links
        total = sum(h.bit_count() for h in held.values())
        plan = []
        for c, h in held.items():
            if cfg.symbols is None:
                k = poisson_quantile(p * h.bit_count(), 0.999) + 3
            else:
                k = round(cfg.symbols * h.bit_count() / total)
            plan += [c] * k
        off = R + salt * 7
        for i, c in enumerate(plan):
            w = (u.vid + 1 + (off + i) % (cfg.n - 1)) % cfg.n
            h = held[c]
            if cfg.strategy == "relay":
                x = h
                for _ in range(self.rng.randrange(h.bit_count())):
                    x &= x - 1
                mask = x & -x
            else:
                lo = (h & -h).bit_length() - 1
                rnd = self.rng.getrandbits(h.bit_length() - lo)
                for _ in range(cfg.density - 1):
                    rnd &= self.rng.getrandbits(h.bit_length() - lo)
                mask = h & (rnd << lo)
                if not mask:
                    continue
            size = SYM_HEADER + c
            self.symbols_sent += 1
            self.bytes["sym"] += size + WIRE
            t = self.transmit(u.vid, w, size)
            if t is not None:
                self.at(t, "sym", w, R, mask)

    def check_build(self, u: Node) -> None:
        cfg = self.cfg
        r = u.qround
        if u.latest >= r + 1:
            return
        # behind: f + 1 others hold blocks of round r + 1
        ahead = u.by_round.get(r + 1, set()) - {u.vid}
        if len(ahead) >= cfg.f + 1:
            self.build(u, r + 1)
            return
        lead = u.leader_at.get(r)
        voted = r < 2 or (
            (Lp := u.leader_at.get(r - 1)) is not None and u.votes.get(Lp, 0) >= cfg.q)
        if lead is not None and voted:
            if cfg.grace <= 0:
                self.build(u, r + 1)
            elif ("grace", r) not in u.timers:
                u.timers.add(("grace", r))
                self.at(self.now + cfg.grace, "build_timer", u.vid)

    def on_build_timer(self, v: int) -> None:
        u = self.nodes[v]
        if u.latest < u.qround + 1:
            self.build(u, u.qround + 1)

    # ------------------------------------------------------------ admission
    def admit(self, u: Node, blk: Block, own: bool = False) -> None:
        cfg = self.cfg
        u.pending.discard(blk.bid)
        u.admitted.add(blk.bid)
        authors = u.by_round.setdefault(blk.rnd, set())
        authors.add(blk.author)
        if len(authors) >= cfg.q and blk.rnd > u.qround:
            u.qround = blk.rnd
            if cfg.strategy in ("coded", "relay") and cfg.trigger == "quorum" and blk.rnd >= cfg.span:
                self.at(self.now + cfg.trigger_delay, "quorum_symbols", u.vid, blk.rnd)
            if ("timeout", blk.rnd) not in u.timers:
                u.timers.add(("timeout", blk.rnd))
                self.at(self.now + cfg.round_timeout, "build_timer", u.vid)
        if blk.leader:
            u.leader_at[blk.rnd] = blk.bid
        for ref in blk.refs:
            if self.blocks[ref].leader and self.blocks[ref].rnd + 1 == blk.rnd:
                u.votes[ref] = u.votes.get(ref, 0) + 1
        for L in blk.claims:
            u.claims[L] = u.claims.get(L, 0) + 1
            if u.claims[L] >= cfg.q and L not in u.committed:
                u.committed.add(L)
                lb = self.blocks[L]
                if cfg.warmup <= lb.rnd <= cfg.rounds:
                    self.direct += 1
                # a direct commit decides every earlier undecided leader
                for rho in range(u.next_undecided, lb.rnd + 1):
                    if cfg.warmup <= rho <= cfg.rounds and rho in self.leader_bid:
                        self.commit.append(self.now - self.blocks[self.leader_bid[rho]].built)
                u.next_undecided = max(u.next_undecided, lb.rnd + 1)
        if not own and cfg.warmup <= blk.rnd <= cfg.rounds:
            self.deliver.append(self.now - blk.built)

    def admissible(self, u: Node, blk: Block) -> bool:
        if any(ref not in u.admitted for ref in blk.refs):
            return False
        # R2: hold each claimed leader block with votes from t_v = q authors
        if self.cfg.check_claims and any(
                L not in u.admitted or u.votes.get(L, 0) < self.cfg.q for L in blk.claims):
            return False
        return blk.rnd <= 1 or len(u.by_round.get(blk.rnd - 1, ())) >= self.cfg.q

    def after_change(self, u: Node) -> None:
        progress = True
        while progress:
            progress = False
            for bid in sorted(u.pending, key=lambda b: self.blocks[b].rnd):
                blk = self.blocks[bid]
                if self.admissible(u, blk):
                    self.admit(u, blk)
                    progress = True
            if progress:
                self.check_build(u)
        self.check_build(u)

    # ------------------------------------------------------------ receiving
    def learn(self, u: Node, bits: int, bid: int | None = None) -> None:
        """Add fragments; bid names their block when they all come from one."""
        new = bits & ~u.frags
        self.dup_frags += (bits & u.frags).bit_count()
        while new:
            u.frags |= new
            if bid is not None:
                touched = {bid}
                bid = None
            else:
                touched = set()
                x = new
                while x:
                    low = x & -x
                    touched.add(self.owner[low.bit_length() - 1])
                    x ^= low
            for b in touched:
                self.notice(u, b)
            if u.rows and new & u.rowunion:
                dec = self.solve(u)
                self.decoded += dec.bit_count()
                new = dec & ~u.frags
            else:
                new = 0
        self.after_change(u)

    def notice(self, u: Node, bid: int, via_ref: bool = False) -> None:
        blk = self.blocks[bid]
        u.known.add(bid)
        u.newest = max(u.newest, blk.rnd)
        if bid in u.complete:
            return
        if u.frags & blk.mask == blk.mask:
            u.complete.add(bid)
            u.pending.add(bid)
            hb = u.held_by_round.setdefault(blk.rnd, set())
            hb.add(blk.author)
            if len(hb) >= self.cfg.f + 1:
                u.ahead = max(u.ahead, blk.rnd)
            gap = False
            for ref in blk.refs:
                if ref not in u.complete:
                    gap = True
                    self.notice(u, ref, via_ref=True)
            if gap:  # pull the window of this block from its author
                self.start_pull(u, bid)
        elif not via_ref:  # part of the block arrived: pull it from its author
            self.start_pull(u, bid)

    def on_frags(self, v: int, bits: int, bid: int) -> None:
        self.learn(self.nodes[v], bits, bid)

    def on_sym(self, v: int, R: int, mask: int) -> None:
        u = self.nodes[v]
        row = mask & ~u.frags
        if not row:
            return
        u.rows = [(t, m) for t, m in u.rows if t >= u.latest - self.cfg.span - 1]
        u.rows.append((R, row))
        u.rowunion |= row
        bits = self.solve(u)
        if bits:
            self.decoded += bits.bit_count()
            self.learn(u, bits)

    def solve(self, u: Node) -> int:
        """Gaussian elimination over GF(2); the fragments it determines."""
        pivots: dict[int, tuple[int, int]] = {}
        for tag, row in u.rows:
            row &= ~u.frags
            for p, (_, prow) in pivots.items():
                if row >> p & 1:
                    row ^= prow
            if not row:
                continue
            p = (row & -row).bit_length() - 1
            for k, (t2, r2) in list(pivots.items()):
                if r2 >> p & 1:
                    pivots[k] = (t2, r2 ^ row)
            pivots[p] = (tag, row)
        out = 0
        rows = []
        union = 0
        for tag, row in pivots.values():
            if row & (row - 1) == 0:
                out |= row
            else:
                rows.append((tag, row))
                union |= row
        u.rows, u.rowunion = rows, union
        return out

    # ------------------------------------------------------------ pulling
    def start_pull(self, u: Node, bid: int) -> None:
        if bid in u.pulling:
            return
        u.pulling.add(bid)
        # a validator holding blocks from f + 1 authors two rounds above its
        # quorum round is behind: what it lacks is not in flight
        late = self.cfg.behind_pull and u.qround + 2 <= u.ahead
        self.at(self.now + (0.0 if late else self.cfg.pull_timer), "pull_timer", u.vid, bid)

    def window(self, bid: int) -> list[int]:
        """The block and what admitting it needs: the windows to depth K of its
        references, so blocks at most K + 1 rounds below it. Blocks never
        change, so windows are cached."""
        w = self.windows.get(bid)
        if w is None:
            w = self.windows[bid] = self.compute_window(bid)
        return w

    def compute_window(self, bid: int) -> list[int]:
        lo = self.blocks[bid].rnd - self.cfg.K - 1
        seen, stack = {bid}, [bid]
        while stack:
            for r in self.blocks[stack.pop()].refs:
                if r not in seen and self.blocks[r].rnd >= lo:
                    seen.add(r)
                    stack.append(r)
        return list(seen)

    def on_pull_timer(self, v: int, root: int) -> None:
        """Ask root's author for every block of root's window the requester lacks,
        in one request; the author sends them all at once."""
        cfg = self.cfg
        u = self.nodes[v]
        blk = self.blocks[root]
        want = self.window(root) if cfg.window_pull else [root]
        missing = [b for b in want if b not in u.complete]
        if not missing:
            return
        fresh = [b for b in missing if u.asked.get(b, 0) <= self.now]
        if not fresh:  # outstanding requests cover them all
            self.at(min(u.asked[b] for b in missing), "pull_timer", v, root)
            return
        if cfg.warmup <= blk.rnd <= cfg.rounds:
            self.pulls += 1
        # the request's bitmap marks the slots held or already asked for, so the
        # author sends only the fresh blocks
        size = REQ_BYTES + (cfg.n * (cfg.K + 2) // 8 if cfg.window_pull else 0)
        for b in fresh:
            u.asked[b] = self.now + cfg.retry_timer
        self.bytes["pullreq"] += size + WIRE
        t = self.transmit(v, blk.author, size)
        if t is not None:
            self.at(t, "pull_req", blk.author, v, fresh)
        self.at(self.now + cfg.retry_timer, "pull_timer", v, root)

    def on_pull_req(self, h: int, v: int, fresh: list[int]) -> None:
        hold, want = self.nodes[h], self.nodes[v]
        for b in fresh:
            if b not in hold.complete or b in want.complete:
                continue
            blk = self.blocks[b]
            missing = blk.mask & ~want.frags
            if missing:
                self.send_frags(h, v, blk, missing, "pullresp")

    # ------------------------------------------------------------ report
    def report(self) -> dict:
        cfg = self.cfg

        def pct(xs, p):
            if not xs:
                return float("nan")
            xs = sorted(xs)
            return xs[min(len(xs) - 1, int(p * len(xs)))]

        starts = {r: sorted(ts)[len(ts) // 2] for r, ts in self.round_start.items()
                  if len(ts) >= cfg.q}
        span = cfg.rounds - cfg.warmup
        round_time = ((starts[cfg.rounds] - starts[cfg.warmup]) / span
                      if cfg.rounds in starts and cfg.warmup in starts else float("nan"))
        rounds_run = max(self.round_start) if self.round_start else 0
        per_node_round = cfg.n * max(rounds_run, 1)
        expected_commits = cfg.n * (cfg.rounds - cfg.warmup + 1)
        return {
            "strategy": cfg.strategy,
            "loss": cfg.loss,
            "symbols": self.symbols_sent / max(1, cfg.n * max(self.round_start, default=1)),
            "deliver_p50": pct(self.deliver, 0.5),
            "deliver_p99": pct(self.deliver, 0.99),
            "deliver_p999": pct(self.deliver, 0.999),
            "deliver_max": max(self.deliver) if self.deliver else float("nan"),
            "commit_p50": pct(self.commit, 0.5),
            "commit_p99": pct(self.commit, 0.99),
            "commit_max": max(self.commit) if self.commit else float("nan"),
            "decided": len(self.commit) / expected_commits,
            "direct": self.direct / expected_commits,
            "delivered": len(self.deliver) / max(1, (cfg.n - 1) * sum(
                1 for b in self.blocks if cfg.warmup <= b.rnd <= cfg.rounds)),
            "round_time": round_time,
            "push_kb": self.bytes["push"] / per_node_round / 1000,
            "sym_kb": self.bytes["sym"] / per_node_round / 1000,
            "pull_kb": (self.bytes["pullreq"] + self.bytes["pullresp"]) / per_node_round / 1000,
            "pulls": self.pulls / (cfg.n * (cfg.rounds - cfg.warmup + 1)),
            "decoded": self.decoded / per_node_round,
            "dup": self.dup_frags / per_node_round,
            "caught_up": self.caught_up if self.caught_up is not None else float("nan"),
        }


def simulate(**kw) -> dict:
    sim = Sim(Config(**kw))
    sim.run()
    out = sim.report()
    out["_deliver"] = sim.deliver
    out["_commit"] = sim.commit
    return out
