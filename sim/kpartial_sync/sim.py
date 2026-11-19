"""Discrete-event simulator of the sparse K-partial DAG synchroniser.

Honest case: every validator is correct and none equivocates. The network
delays each packet by a base one-way latency, a random jitter (which reorders
packets) and the sender's uplink queue, and drops each packet independently.

Consensus follows rules R2--R4 of the paper, simplified to the honest case:

* a block is admitted once all its fragments are held, its references are
  admitted and a quorum of the round below is admitted (R2);
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

* ``pull``  : request missing fragments after ``pull_timer`` and retry;
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
    early: float | None = None  # also send symbols over the current round this long after building
    trigger: str = "quorum"  # send symbols on a new quorum round, or on building (rounds below)
    trigger_delay: float = 0.0  # with trigger = quorum, wait this long after the quorum
    grace: float = 0.0
    round_timeout: float = 1.0
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
    ref_by: dict = field(default_factory=dict)  # bid -> author referencing it
    pulling: set = field(default_factory=set)
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
        return done + self.lat[src][dst] + self.rng.expovariate(1 / self.cfg.jitter)

    def send_frags(self, src: int, dst: int, blk: Block, mask: int, kind: str) -> None:
        """Send the fragments of blk in mask, one packet each; deliver together
        at the last arrival (a block is usable only when complete)."""
        got, last = 0, None
        for j in range(blk.nfrag):
            bit = 1 << (blk.base + j)
            if not mask & bit:
                continue
            data = min(self.cfg.frag, blk.size - j * self.cfg.frag)  # last one shorter
            size = FRAG_HEADER + data
            self.bytes[kind] += size + WIRE
            t = self.transmit(src, dst, size)
            if t is not None:
                got |= bit
                last = t if last is None else max(last, t)
        if got:
            self.at(last, "frags", dst, got)

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
        if cfg.payload_sigma > 0:
            mu = math.log(cfg.payload) - cfg.payload_sigma ** 2 / 2
            pay = int(self.rng.lognormvariate(mu, cfg.payload_sigma))
        size = cfg.header + len(refs) * cfg.ref_bytes + pay
        nfrag = max(1, math.ceil(size / cfg.frag))
        blk = Block(len(self.blocks), u.vid, R, refs, claims, size, nfrag,
                    len(self.owner), self.now, is_leader)
        self.blocks.append(blk)
        self.owner.extend([blk.bid] * nfrag)
        self.round_mask[R] = self.round_mask.get(R, 0) | blk.mask
        if is_leader:
            self.leader_bid[R] = blk.bid
        self.round_start.setdefault(R, []).append(self.now)
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

    def send_symbols(self, u: Node, R: int, rounds, salt: int = 0) -> None:
        cfg = self.cfg
        rng_mask = 0
        for k in rounds:
            rng_mask |= self.round_mask.get(k, 0)
        held = u.frags & rng_mask
        if not held:
            return
        lo = (held & -held).bit_length() - 1
        width = held.bit_length() - lo
        bits = None
        if cfg.strategy == "relay":
            bits = []
            x = held
            while x:
                low = x & -x
                bits.append(low)
                x ^= low
        s = min(self.s, cfg.n - 1)
        off = 1 + ((R + salt * 7) % (cfg.n - s)) if cfg.n - s > 0 else 1
        for i in range(s):
            w = (u.vid + off + i) % cfg.n
            if cfg.strategy == "relay":
                mask = self.rng.choice(bits)
            else:
                rnd = self.rng.getrandbits(width)
                for _ in range(cfg.density - 1):
                    rnd &= self.rng.getrandbits(width)
                mask = held & (rnd << lo)
                if not mask:
                    continue
            size = SYM_HEADER + cfg.frag
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
    def learn(self, u: Node, bits: int) -> None:
        new = bits & ~u.frags
        self.dup_frags += (bits & u.frags).bit_count()
        while new:
            u.frags |= new
            touched = set()
            x = new
            while x:
                low = x & -x
                touched.add(self.owner[low.bit_length() - 1])
                x ^= low
            for bid in touched:
                self.notice(u, bid)
            if u.rows and new & u.rowunion:
                dec = self.solve(u)
                self.decoded += dec.bit_count()
                new = dec & ~u.frags
            else:
                new = 0
        self.after_change(u)

    def notice(self, u: Node, bid: int) -> None:
        blk = self.blocks[bid]
        u.known.add(bid)
        if bid in u.complete:
            return
        if u.frags & blk.mask == blk.mask:
            u.complete.add(bid)
            u.pending.add(bid)
            for ref in blk.refs:
                u.ref_by.setdefault(ref, blk.author)
                if ref not in u.complete:
                    self.notice(u, ref)
        else:
            self.start_pull(u, bid)

    def on_frags(self, v: int, bits: int) -> None:
        self.learn(self.nodes[v], bits)

    def on_sym(self, v: int, R: int, mask: int) -> None:
        u = self.nodes[v]
        row = mask & ~u.frags
        if not row:
            return
        u.rows = [(t, m) for t, m in u.rows if t >= u.latest - 3]
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
        self.at(self.now + self.cfg.pull_timer, "pull_timer", u.vid, bid)

    def on_pull_timer(self, v: int, bid: int) -> None:
        u = self.nodes[v]
        blk = self.blocks[bid]
        missing = blk.mask & ~u.frags
        if not missing:
            return
        holder = u.ref_by.get(bid, blk.author)
        if holder == u.vid:
            holder = blk.author
        if self.cfg.warmup <= blk.rnd <= self.cfg.rounds:
            self.pulls += 1
        self.bytes["pullreq"] += REQ_BYTES + WIRE
        t = self.transmit(v, holder, REQ_BYTES)
        if t is not None:
            self.at(t, "pull_req", holder, v, bid, missing)
        self.at(self.now + self.cfg.retry_timer, "pull_timer", v, bid)

    def on_pull_req(self, h: int, v: int, bid: int, missing: int) -> None:
        held = missing & self.nodes[h].frags
        if held:
            self.send_frags(h, v, self.blocks[bid], held, "pullresp")

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
            "symbols": self.s if cfg.strategy != "pull" else 0,
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
        }


def simulate(**kw) -> dict:
    sim = Sim(Config(**kw))
    sim.run()
    out = sim.report()
    out["_deliver"] = sim.deliver
    out["_commit"] = sim.commit
    return out
