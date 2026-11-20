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
  them when it first holds complete blocks of a round from ``trigger_count``
  others (``trigger = "held"``, default f + 1), when it first holds a quorum of
  a round (``trigger = "quorum"``), or when it builds, over the rounds below its
  new block (``trigger = "build"``). By default a pull response carries repair
  symbols (``pull_fec``); ``tail`` also sends a few symbols over older rounds;
* ``relay`` : as ``coded``, but each symbol is one random fragment, uncoded.

Fragments are indexed globally; a set of fragments is a Python int bitmask,
and a coded symbol is the bitmask of the fragments it XORs.
"""

from __future__ import annotations

import heapq
import math
import random
from dataclasses import dataclass, field
from functools import lru_cache

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
    stretch: float = 0.0  # sigma of a per-link routing stretch exp(|N(0, sigma)|) >= 1; > 0 breaks the triangle inequality
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
    idle: float = 0.15  # > 0: a validator that has sent no symbols for this long, or 1.5 rounds if longer, sends a batch
    recent: float = 0.1  # > 0: symbols also cover blocks of older rounds completed this recently (s)
    tail: tuple | None = None  # (rounds, symbols): also this many symbols per receiver over the older rounds
    pull_fec: int = 3  # >= 0 (coded only): a pull response adds d at its 99.9th percentile plus this many symbols
    margin: tuple = (3,)  # symbols above the quantile, per class from the smallest (last value repeats)
    cuts: tuple = ()  # nested classes: a symbol of class L covers held fragments of at most L bytes
    early: float | None = None  # also send symbols over the current round this long after building
    trigger: str = "held"  # send symbols on f + 1 held blocks of a round, a new quorum round, or on building
    trigger_count: int = 0  # with trigger = "held": complete blocks of this many others in a round (0: f + 1)
    trigger_delay: float = 0.0  # with trigger = quorum, wait this long after the quorum
    vote_wait: str = "included"  # await votes for the leader of r - 1 only if own block at r references it; "always"
    grace: float = 0.0
    round_timeout: float = 1.0
    K: int = 6  # window depth
    pull_mode: str = "bitmap"  # what a requester can ask for: "oracle" (the window, known globally),
    # "refs" (blocks it has seen referenced), "bitmap" (each block carries a bitmap of its window's slots)
    window_pull: bool = True  # a pull asks for the whole window to depth K, not one block
    behind_pull: bool = True  # pull at once when f + 1 others are two rounds ahead
    check_claims: bool = True  # R2: admit a block only when holding the votes behind its claims
    adapt: bool = False  # validators estimate loss, margin and timers locally (see ``Adaptive``)
    assumed_loss: float | None = None  # without adapt: the loss the budget assumes (None: the true loss)
    loss_steps: tuple = ()  # ((time, loss), ...): the loss of every link that is not bad changes then
    est_tau: tuple = (0.1, 2.0)  # adapt: time constants of a fast and a slow loss estimate (the larger is used), s
    est_prior: tuple = (0.2, 19.8)  # adapt: Beta prior (lost, received) of the loss estimate
    own_floor: bool = True  # adapt: a sender plans for at least its own loss estimate at every receiver
    margin_ctl: tuple = (2.0, 0.05, 1.0, 30.0)  # adapt: margin times this after a round with a miss, minus this after one without, min, max
    crash: tuple | None = None  # (validators, time): from then on they build and send nothing
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


@lru_cache(maxsize=None)
def q999(lam20: int) -> int:
    """The 99.9th percentile of a Poisson variable of mean lam20 / 20."""
    return poisson_quantile(lam20 / 20, 0.999)


def assumed(cfg: Config) -> float:
    """The loss a validator without estimates assumes: assumed_loss, or the true mean."""
    if cfg.assumed_loss is not None:
        return cfg.assumed_loss
    return cfg.loss * (1 - cfg.bad_links) + cfg.bad_loss * cfg.bad_links


def auto_symbols(cfg: Config) -> int:
    """d_f at the 99.9th percentile plus 3, over the rounds symbols cover."""
    mean_size = cfg.header + cfg.payload + 2 * cfg.ref_bytes
    frags = cfg.span * cfg.n * math.ceil(mean_size / cfg.frag)
    return poisson_quantile(assumed(cfg) * frags, 0.999) + 3


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
    report: tuple = ()  # adapt: the author's (time, loss estimate, margin) when it built the block

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
    pulling: dict = field(default_factory=dict)  # root -> token of its live pull timer
    deferred: set = field(default_factory=set)  # roots whose first pull waits pull_timer
    newest: int = 0  # highest round of a block seen
    held_by_round: dict = field(default_factory=dict)  # round -> authors of complete blocks
    ahead: int = 0  # highest round with complete blocks from f + 1 authors
    asked: dict = field(default_factory=dict)  # bid -> time an outstanding request covering it expires
    qround: int = 0
    latest: int = 0
    own: int | None = None
    timers: set = field(default_factory=set)
    rows: list = field(default_factory=list)  # (round tag, mask)
    round_avg: float = 0.1  # running average of the time between quorum rounds
    qround_at: float = 0.0  # when the quorum round last advanced
    sym_seq: int = 0  # symbol batches sent; an idle timer is live only for the latest
    arrivals: list = field(default_factory=list)  # (time, bid) of blocks completed
    rowunion: int = 0
    basis: dict | None = None  # reduced rows in a local frame: pivot -> (tag, row); None when stale
    boff: int = 0  # the local frame: bit offset and width
    bwidth: int = 0
    bknown: int = -1  # the held fragments in the frame when the basis was built
    est_lost: list = field(default_factory=lambda: [0.0, 0.0])  # adapt: fragments lost and sent on
    est_sent: list = field(default_factory=lambda: [0.0, 0.0])  # incoming links, decayed with each est_tau
    est_at: float = 0.0
    margin: float = 3.0  # adapt: symbols asked above the quantile
    missed: bool = False  # adapt: a repair deadline passed since the quorum round last advanced
    reports: dict = field(default_factory=dict)  # adapt: peer -> (time, loss, margin), the newest it sent
    owd: dict = field(default_factory=dict)  # adapt: author -> [mean, deviation] of its blocks' delay


class Sim:
    def __init__(self, cfg: Config):
        self.cfg = cfg
        self.rng = random.Random(cfg.seed)
        n = cfg.n
        self.bitmap_bytes = -(-cfg.n * (cfg.K + 2) // 8) if cfg.pull_mode == "bitmap" else 0
        self.keep = max(cfg.span, cfg.tail[0] if cfg.tail else 0, cfg.K + 2 if cfg.recent > 0 else 0,
                        cfg.K + 2 if cfg.pull_fec >= 0 and cfg.strategy == "coded" else 0) + 1  # rounds of symbol rows kept
        self.s = cfg.symbols if cfg.symbols is not None else auto_symbols(cfg)
        pts = [(self.rng.random(), self.rng.random()) for _ in range(n)]
        self.lat = [[0.0] * n for _ in range(n)]
        self.lossp = [[cfg.loss] * n for _ in range(n)]
        srng = random.Random(cfg.seed * 7919 + 1)  # its own stream, so stretch = 0 changes nothing
        stretch = [[1.0] * n for _ in range(n)]
        if cfg.stretch > 0:
            for i in range(n):
                for j in range(i + 1, n):
                    stretch[i][j] = stretch[j][i] = math.exp(abs(srng.gauss(0, cfg.stretch)))
        for i in range(n):
            for j in range(n):
                if i != j:
                    d = math.dist(pts[i], pts[j]) / math.sqrt(2)
                    self.lat[i][j] = (cfg.lat_min + (cfg.lat_max - cfg.lat_min) * d) * stretch[i][j]
                    if self.rng.random() < cfg.bad_links:
                        self.lossp[i][j] = cfg.bad_loss
        self.bad = {(i, j) for i in range(n) for j in range(n) if self.lossp[i][j] != cfg.loss}
        self.nodes = [Node(v, margin=float(cfg.margin[0])) for v in range(n)]
        self.misses = 0
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
        # per validator, by kind: bytes sent, and bytes received (packets delivered)
        self.out = {k: [0] * n for k in self.bytes}
        self.inb = {k: [0] * n for k in self.bytes}
        self.dup_frags = 0
        self.why: dict[str, int] = {}  # reason -> blocks built in the measured rounds
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
        for t, p in self.cfg.loss_steps:
            self.at(t, "set_loss", p)
        for v in range(self.cfg.n):
            self.build(self.nodes[v], 1)
        while self.q:
            t, _, kind, args = heapq.heappop(self.q)
            if t > horizon:
                break
            self.now = t
            getattr(self, "on_" + kind)(*args)

    def on_set_loss(self, p: float) -> None:
        n = self.cfg.n
        for i in range(n):
            for j in range(n):
                if i != j and (i, j) not in self.bad:
                    self.lossp[i][j] = p

    # ------------------------------------------------------------ adaptive
    # A validator estimates the loss on its incoming links from the fragments
    # missing from each block delivery (the fragment count is in every
    # fragment's header), and reports the estimate and its margin in its
    # blocks, symbols and pull requests (2 B each), so reports still flow when
    # rounds stall. A sender sizes the symbols for each receiver from that
    # receiver's report. A receiver raises its margin after a round in which a
    # partial block outlived its repair deadline, and lowers it slowly
    # otherwise. Timers follow the measured round time and block delays.
    def p_hat(self, u: Node) -> float:
        a, b = self.cfg.est_prior
        return max((u.est_lost[i] + a) / (u.est_sent[i] + a + b) for i in range(2))

    def observe(self, u: Node, sent: int, lost: int) -> None:
        for i, tau in enumerate(self.cfg.est_tau):
            w = math.exp(-(self.now - u.est_at) / tau)
            u.est_lost[i] = u.est_lost[i] * w + lost
            u.est_sent[i] = u.est_sent[i] * w + sent
        u.est_at = self.now

    def my_report(self, u: Node) -> tuple:
        return (self.now, self.p_hat(u), u.margin) if self.cfg.adapt else ()

    def hear(self, u: Node, w: int, rep: tuple) -> None:
        if rep and (w not in u.reports or u.reports[w][0] < rep[0]):
            u.reports[w] = rep

    def report_of(self, u: Node, w: int) -> tuple:
        """The loss and margin u plans for at w: w's newest report, with u's own
        estimate as a floor on the loss, since a change of loss across the
        network reaches u's estimate before w's report reaches u."""
        r = u.reports.get(w)
        if r is None:
            a, b = self.cfg.est_prior
            r = (0.0, a / (a + b), float(self.cfg.margin[0]))
        p = max(r[1], self.p_hat(u)) if self.cfg.own_floor else r[1]
        return p, r[2]

    def loss_for(self, u: Node, w: int) -> float:
        return self.report_of(u, w)[0] if self.cfg.adapt else assumed(self.cfg)

    def repair_delay(self, u: Node) -> float:
        """How long a partial block waits for symbols before it is pulled."""
        if not self.cfg.adapt:
            return self.cfg.pull_timer
        return min(self.cfg.pull_timer, max(0.05, 2 * u.round_avg))

    def retry_delay(self, u: Node, w: int) -> float:
        """When a pull to w is retried: twice the delay of w's blocks plus four deviations."""
        if not self.cfg.adapt or w not in u.owd:
            return self.cfg.retry_timer
        m, d = u.owd[w]
        return min(self.cfg.retry_timer, max(0.03, 2 * m + 4 * d))

    def recent_window(self, u: Node) -> float:
        return u.round_avg if self.cfg.adapt and self.cfg.recent > 0 else self.cfg.recent

    # ------------------------------------------------------------ network
    def crashed(self, v: int) -> bool:
        c = self.cfg.crash
        return c is not None and v in c[0] and self.now >= c[1]

    def transmit(self, src: int, dst: int, size: int, kind: str | None = None) -> float | None:
        """Queue one packet on src's uplink; its arrival time, or None if lost."""
        if self.crashed(src):
            return None
        if kind is not None:
            self.out[kind][src] += size + WIRE
        start = max(self.now, self.up_free[src])
        done = start + (size + WIRE) * 8 / self.cfg.uplink_bps
        self.up_free[src] = done
        if self.rng.random() < self.lossp[src][dst]:
            return None
        o = self.cfg.outage
        if o is not None and dst == o[0] and o[1] <= self.now < o[1] + o[2]:
            return None
        if kind is not None:
            self.inb[kind][dst] += size + WIRE
        return done + self.lat[src][dst] + self.rng.expovariate(1 / self.cfg.jitter)

    def send_frags(self, src: int, dst: int, blk: Block, mask: int, kind: str) -> None:
        """Send the fragments of blk in mask, one packet each, back to back on
        src's uplink; deliver the ones not lost together at the last arrival (a
        block is usable only when complete). Drawn at once: the lost fragments
        by geometric gaps, the last arrival as the uplink finishing time plus the
        latency plus the largest of the jitters."""
        cfg = self.cfg
        if mask == blk.mask:  # the whole block, the common case
            js = range(blk.nfrag)
            sizes = blk.size + blk.nfrag * (FRAG_HEADER + WIRE)
        else:
            js = [j for j in range(blk.nfrag) if mask >> (blk.base + j) & 1]
            if not js:
                return
            sizes = sum(FRAG_HEADER + min(cfg.frag, blk.size - j * cfg.frag) + WIRE for j in js)
        self.bytes[kind] += sizes
        if self.crashed(src):
            return None
        self.out[kind][src] += sizes
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
        got = mask
        for i in lost:
            got &= ~(1 << (blk.base + js[i]))
        k = len(js) - len(lost)
        if k:
            self.inb[kind][dst] += sizes - sum(
                FRAG_HEADER + min(cfg.frag, blk.size - js[i] * cfg.frag) + WIRE for i in lost)
            jit = -cfg.jitter * math.log(1 - self.rng.random() ** (1 / k))
            self.at(done + self.lat[src][dst] + jit, "frags", dst, got, blk.bid, len(lost), len(js), kind)

    # ------------------------------------------------------------ building
    def build(self, u: Node, R: int, why: str = "leader") -> None:
        cfg = self.cfg
        if R > self.stop_round or u.latest >= R or self.crashed(u.vid):
            return
        if cfg.warmup <= R <= cfg.rounds:
            self.why[why] = self.why.get(why, 0) + 1
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
        size = cfg.header + len(refs) * cfg.ref_bytes + pay + self.bitmap_bytes + (2 if cfg.adapt else 0)
        nfrag = max(1, math.ceil(size / cfg.frag))
        blk = Block(len(self.blocks), u.vid, R, refs, claims, size, nfrag,
                    len(self.owner), self.now, is_leader)
        blk.report = self.my_report(u)
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
        cfg = self.cfg
        self.send_symbols(self.nodes[v], r + 1, range(r + 1 - cfg.span, r + 1))
        self.arm_idle(self.nodes[v])
        if cfg.tail is not None:
            lo = max(1, r + 1 - cfg.tail[0])
            self.send_symbols(self.nodes[v], r + 1, range(lo, r + 1 - cfg.span),
                              salt=3, count=cfg.tail[1])

    def arm_idle(self, u: Node, delay: float | None = None) -> None:
        """Arm the idle timer; it doubles after each idle batch."""
        u.sym_seq += 1
        if self.cfg.idle > 0:
            floor = 0.03 if self.cfg.adapt else self.cfg.idle
            d = max(floor, 1.5 * u.round_avg) if delay is None else delay
            self.at(self.now + d, "sym_idle", u.vid, u.sym_seq, d)

    def on_sym_idle(self, v: int, seq: int, delay: float) -> None:
        """No symbols for ``idle``: a batch over the quorum round and the round
        above, and recent arrivals, so a late block is covered even when no
        round reaches the trigger."""
        u = self.nodes[v]
        if seq != u.sym_seq or self.crashed(v) or u.latest > self.stop_round - 2:
            return
        r = u.qround
        self.send_symbols(u, r + 1, range(max(1, r), r + 2), salt=5 + seq)
        self.arm_idle(u, 2 * delay)

    def on_early(self, v: int, R: int) -> None:
        self.send_symbols(self.nodes[v], R + 1, [R], salt=1)

    def size_class(self, data: int) -> int:
        cfg = self.cfg
        if cfg.cuts:
            return next((L for L in cfg.cuts if data <= L), cfg.frag)
        c = cfg.size_class
        return cfg.frag if c <= 0 else min(cfg.frag, -(-data // c) * c)

    def code_mask(self, h: int) -> int:
        """A random subset of h, each fragment with probability 2^-density."""
        lo = (h & -h).bit_length() - 1
        rnd = self.rng.getrandbits(h.bit_length() - lo)
        for _ in range(self.cfg.density - 1):
            rnd &= self.rng.getrandbits(h.bit_length() - lo)
        return h & (rnd << lo)

    def send_symbols(self, u: Node, R: int, rounds, salt: int = 0, count: int | None = None) -> None:
        """Coded symbols over ``rounds``. Each size class of fragments is its own
        code: a symbol XORs a random subset of the sender's fragments of one
        class and is as long as the class. A class with m held fragments gets
        d at its 99.9th percentile plus 3 symbols per receiver on average, d
        Poisson with mean p * m; a fixed ``symbols`` is shared by fragment count.
        Distinct receivers when the count is below n. With ``cuts`` the classes
        nest: a symbol of class L covers every held fragment of at most L bytes,
        and class L's budget counts the fragments above the next smaller cut.
        ``count`` fixes the total, shared by fragment count."""
        cfg = self.cfg
        held: dict[int, int] = {}
        for k in rounds:
            for c, m in self.class_mask.get(k, {}).items():
                if u.frags & m:
                    held[c] = held.get(c, 0) | (u.frags & m)
        if cfg.recent > 0 and (salt == 0 or salt >= 5):
            # late blocks of older rounds, completed recently
            lo = min(rounds)
            u.arrivals = [(t, b) for t, b in u.arrivals if t >= self.now - self.recent_window(u)]
            for _, b in u.arrivals:
                blk = self.blocks[b]
                if blk.rnd < lo:
                    for c, m in self.class_mask[blk.rnd].items():
                        if m & blk.mask:
                            held[c] = held.get(c, 0) | (m & blk.mask & u.frags)
        if not held:
            return
        p = assumed(cfg)
        total = sum(h.bit_count() for h in held.values())
        fixed = count if count is not None else cfg.symbols
        plan = []
        off = R + salt * 7
        n1 = cfg.n - 1
        for i, c in enumerate(sorted(held)):
            h = held[c]
            if fixed is None and cfg.adapt:
                # receiver w needs need_w symbols in all, from n - 1 senders: each
                # sends floor(need_w / (n - 1)), and one more from a rotating
                # share of senders, so w gets need_w whatever the rounding
                m = h.bit_count()
                for j in range(n1):
                    w = (u.vid + 1 + j) % cfg.n
                    pw, mw = self.report_of(u, w)
                    if i:
                        mw = cfg.margin[min(i, len(cfg.margin) - 1)]
                    x = (q999(round(20 * pw * m)) + mw) / (1 - pw) / n1
                    k = int(x) + (1 if (j - off - i) % n1 < (x - int(x)) * n1 else 0)
                    plan += [(c, w)] * k
                continue
            if fixed is None:
                extra = cfg.margin[min(i, len(cfg.margin) - 1)]
                k = poisson_quantile(p * h.bit_count(), 0.999) + extra
            else:
                k = round(fixed * h.bit_count() / total)
            plan += [(c, None)] * k
        if cfg.cuts:  # class L covers every class up to L
            acc = {}
            run = 0
            for c in sorted(held):
                run |= held[c]
                acc[c] = run
            held = acc
        for i, (c, w) in enumerate(plan):
            if w is None:
                w = (u.vid + 1 + (off + i) % (cfg.n - 1)) % cfg.n
            h = held[c]
            if cfg.strategy == "relay":
                x = h
                for _ in range(self.rng.randrange(h.bit_count())):
                    x &= x - 1
                mask = x & -x
            else:
                mask = self.code_mask(h)
                if not mask:
                    continue
            size = SYM_HEADER + c + (2 if cfg.adapt else 0)
            self.symbols_sent += 1
            self.bytes["sym"] += size + WIRE
            t = self.transmit(u.vid, w, size, "sym")
            if t is not None:
                self.at(t, "sym", w, R, mask, u.vid, self.my_report(u))

    def check_build(self, u: Node) -> None:
        cfg = self.cfg
        r = u.qround
        if u.latest >= r + 1:
            return
        # behind: f + 1 others hold blocks of round r + 1
        ahead = u.by_round.get(r + 1, set()) - {u.vid}
        if len(ahead) >= cfg.f + 1:
            self.build(u, r + 1, "behind")
            return
        lead = u.leader_at.get(r)
        # votes for the leader of r - 1 are awaited only if the validator's own
        # block at r references it; otherwise a quorum at r is enough
        Lp = u.leader_at.get(r - 1)
        mine = u.own if u.own is not None and self.blocks[u.own].rnd == r else None
        included = mine is not None and Lp is not None and Lp in self.blocks[mine].refs
        if cfg.vote_wait == "always":
            included = True
        voted = r < 2 or not included or u.votes.get(Lp, 0) >= cfg.q
        if lead is not None and voted:
            if cfg.grace <= 0:
                self.build(u, r + 1)
            elif ("grace", r) not in u.timers:
                u.timers.add(("grace", r))
                self.at(self.now + cfg.grace, "build_timer", u.vid, r, "grace")

    def on_build_timer(self, v: int, r: int, why: str) -> None:
        """A timer armed at quorum round r: it builds only if the validator is
        still at quorum round r and has not built r + 1."""
        u = self.nodes[v]
        if u.qround == r and u.latest < r + 1:
            self.build(u, r + 1, why)

    # ------------------------------------------------------------ admission
    def admit(self, u: Node, blk: Block, own: bool = False) -> None:
        cfg = self.cfg
        u.pending.discard(blk.bid)
        u.admitted.add(blk.bid)
        authors = u.by_round.setdefault(blk.rnd, set())
        authors.add(blk.author)
        if len(authors) >= cfg.q and blk.rnd > u.qround:
            step = (self.now - u.qround_at) / (blk.rnd - u.qround)
            u.round_avg = 0.8 * u.round_avg + 0.2 * step
            u.qround_at = self.now
            if cfg.adapt:
                up, down, lo, hi = cfg.margin_ctl
                u.margin = min(hi, u.margin * up) if u.missed else max(lo, u.margin - down)
                u.missed = False
            u.qround = blk.rnd
            if cfg.strategy in ("coded", "relay") and cfg.trigger == "quorum" and blk.rnd >= cfg.span:
                self.at(self.now + cfg.trigger_delay, "quorum_symbols", u.vid, blk.rnd)
            if ("timeout", blk.rnd) not in u.timers:
                u.timers.add(("timeout", blk.rnd))
                self.at(self.now + cfg.round_timeout, "build_timer", u.vid, blk.rnd, "timer")
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
                if bid not in u.pending:  # admitted by a nested call
                    continue
                blk = self.blocks[bid]
                if self.admissible(u, blk):
                    self.admit(u, blk)
                    progress = True
                    # a node checks its build rule on each admission, so it does
                    # not skip a round it could have built
                    self.check_build(u)
        self.check_build(u)

    # ------------------------------------------------------------ receiving
    def learn(self, u: Node, bits: int, bid: int | None = None) -> None:
        """Add fragments; bid names their block when they all come from one."""
        new = bits ^ (bits & u.frags)
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
                new = dec ^ (dec & u.frags)
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
            self.hear(u, blk.author, blk.report)
            if self.cfg.recent > 0:
                u.arrivals.append((self.now, bid))
            u.pending.add(bid)
            hb = u.held_by_round.setdefault(blk.rnd, set())
            hb.add(blk.author)
            if len(hb) >= self.cfg.f + 1 and blk.rnd > u.ahead:
                u.ahead = blk.rnd
                self.promote(u)
            cfg = self.cfg
            if (cfg.trigger == "held" and len(hb) == (cfg.trigger_count or cfg.f + 1)
                    and cfg.strategy in ("coded", "relay") and blk.rnd >= cfg.span):
                self.at(self.now + cfg.trigger_delay, "quorum_symbols", u.vid, blk.rnd)
            gap = False
            for ref in blk.refs:
                if ref not in u.complete:
                    gap = True
                    self.notice(u, ref, via_ref=True)
            if gap:  # pull the window of this block from its author; at once if
                # the block itself came from a pull, as what it lacks is old
                self.start_pull(u, bid, urgent=bid in u.asked and self.cfg.pull_mode != "oracle")
        elif not via_ref:  # part of the block arrived: pull it from its author
            self.start_pull(u, bid)

    def on_frags(self, v: int, bits: int, bid: int, lost: int = 0, sent: int = 0,
                 kind: str | None = None) -> None:
        u = self.nodes[v]
        if self.cfg.adapt:
            self.observe(u, sent, lost)
            blk = self.blocks[bid]
            if kind == "push":
                d = self.now - blk.built
                e = u.owd.get(blk.author)
                if e is None:
                    u.owd[blk.author] = [d, d / 2]
                else:
                    e[1] += (abs(d - e[0]) - e[1]) / 4
                    e[0] += (d - e[0]) / 8
        self.learn(u, bits, bid)

    def on_sym(self, v: int, R: int, mask: int, src: int = -1, rep: tuple = ()) -> None:
        u = self.nodes[v]
        self.hear(u, src, rep)
        row = mask ^ (mask & u.frags)
        if not row:
            return
        n0 = len(u.rows)
        u.rows = [(t, m) for t, m in u.rows if t >= u.latest - self.keep]
        if len(u.rows) != n0:
            u.basis = None
        u.rows.append((R, row))
        u.rowunion |= row
        bits = self.insert(u, R, row)
        if bits is None:
            bits = self.solve(u)
        if bits:
            self.decoded += bits.bit_count()
            self.learn(u, bits)

    def insert(self, u: Node, tag: int, row: int) -> int | None:
        """Add one row to the reduced basis, when the basis is current and the
        row fits its frame; the fragments it determines, or None to rebuild."""
        if u.basis is None or row >> u.boff << u.boff != row or row.bit_length() > u.boff + u.bwidth:
            return None
        known = (u.frags >> u.boff) & ((1 << u.bwidth) - 1)
        if known != u.bknown:
            return None
        r = row >> u.boff
        basis = u.basis
        for p, (_, prow) in basis.items():
            if r >> p & 1:
                r ^= prow
        if not r:
            return 0
        p = (r & -r).bit_length() - 1
        changed = [p]
        for k, (t2, r2) in list(basis.items()):
            if r2 >> p & 1:
                basis[k] = (t2, r2 ^ r)
                changed.append(k)
        basis[p] = (tag, r)
        out = 0
        for k in changed:
            rk = basis[k][1]
            if rk & (rk - 1) == 0:
                out |= rk
        if out:
            u.basis = None  # learning these changes what is held
        return out << u.boff

    def solve(self, u: Node) -> int:
        """Gaussian elimination over GF(2); the fragments it determines. The
        rows cover recent fragments only, so they are shifted down to their own
        bit range, which keeps the integers short."""
        union = 0
        for _, row in u.rows:
            union |= row
        if not union:
            u.rows, u.rowunion = [], 0
            return 0
        off = (union & -union).bit_length() - 1
        known = (u.frags >> off) & ((1 << (union.bit_length() - off)) - 1)
        pivots: dict[int, tuple[int, int]] = {}
        for tag, row in u.rows:
            row = row >> off
            row ^= row & known
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
                rows.append((tag, row << off))
                union |= row
        u.rows, u.rowunion = rows, union << off
        if out:
            u.basis = None
        else:
            u.basis = pivots
            u.boff = off
            u.bwidth = len(self.owner) - off + 4096  # room for rows over newer fragments
            u.bknown = (u.frags >> off) & ((1 << u.bwidth) - 1)
        return out << off

    # ------------------------------------------------------------ pulling
    def start_pull(self, u: Node, bid: int, urgent: bool = False) -> None:
        if bid in u.pulling:
            if urgent:  # a pull already waits for bid: fire it now, for what bid lacks
                u.pulling[bid] += 1
                u.deferred.discard(bid)
                self.at(self.now, "pull_timer", u.vid, bid, u.pulling[bid])
            return
        u.pulling[bid] = 0
        if urgent or self.behind(u):
            self.at(self.now, "pull_timer", u.vid, bid, 0)
        else:
            u.deferred.add(bid)
            self.at(self.now + self.repair_delay(u), "pull_timer", u.vid, bid, 0)

    def behind(self, u: Node) -> bool:
        """Holding blocks from f + 1 authors two rounds above its quorum round:
        what it lacks is not in flight."""
        return self.cfg.behind_pull and u.qround + 2 <= u.ahead

    def promote(self, u: Node) -> None:
        """Once behind, deferred pulls go out at once."""
        if u.deferred and self.behind(u):
            for root in u.deferred:
                u.pulling[root] += 1
                self.at(self.now, "pull_timer", u.vid, root, u.pulling[root])
            u.deferred.clear()

    def wanted(self, u: Node, root: int) -> list[int]:
        """The blocks a pull for root can name. With "refs", root itself if
        partial, else the references of root (deeper gaps are found as these
        arrive); with "bitmap", root's window from its bitmap once root is held."""
        mode = self.cfg.pull_mode
        if mode == "oracle":
            return self.window(root) if self.cfg.window_pull else [root]
        if root not in u.complete:
            return [root]
        if mode == "refs":
            return [r for r in self.blocks[root].refs]
        return self.window(root)

    def request_bytes(self, u: Node, fresh: list[int]) -> int:
        """A request names each block by its slot (4 B), or by a bitmap of the
        window's slots, whichever is smaller, and adds a bitmap of the fragments
        held of each block held in part."""
        cfg = self.cfg
        if cfg.pull_mode == "oracle":
            return REQ_BYTES + (cfg.n * (cfg.K + 2) // 8 if cfg.window_pull else 0)
        names = min(4 * len(fresh), -(-cfg.n * (cfg.K + 2) // 8))
        partial = sum(-(-self.blocks[b].nfrag // 8) for b in fresh
                      if u.frags & self.blocks[b].mask)
        return REQ_BYTES + names + partial

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

    def on_pull_timer(self, v: int, root: int, token: int) -> None:
        """Ask root's author for every block of root's window the requester lacks,
        in one request; the author sends them all at once."""
        cfg = self.cfg
        u = self.nodes[v]
        if u.pulling.get(root) != token:  # superseded by a promoted timer
            return
        was_deferred = root in u.deferred
        u.deferred.discard(root)
        blk = self.blocks[root]
        want = self.wanted(u, root)
        missing = [b for b in want if b not in u.complete]
        if not missing:
            return
        if was_deferred and token == 0:  # symbols did not repair it in time
            u.missed = True
            if cfg.warmup <= blk.rnd <= cfg.rounds:
                self.misses += 1
        fresh = [b for b in missing if u.asked.get(b, 0) <= self.now]
        if not fresh:  # outstanding requests cover them all
            self.at(min(u.asked[b] for b in missing), "pull_timer", v, root, token)
            return
        if cfg.warmup <= blk.rnd <= cfg.rounds:
            self.pulls += 1
        # the request's bitmap marks the slots held or already asked for, so the
        # author sends only the fresh blocks
        size = self.request_bytes(u, fresh) + (2 if cfg.adapt else 0)
        retry = self.retry_delay(u, blk.author)
        for b in fresh:
            u.asked[b] = self.now + retry
        if cfg.pull_mode != "oracle":  # the request carries what the requester holds of each
            fresh = [(b, u.frags & self.blocks[b].mask) for b in fresh]
        self.bytes["pullreq"] += size + WIRE
        t = self.transmit(v, blk.author, size, "pullreq")
        if t is not None:
            self.at(t, "pull_req", blk.author, v, fresh, self.my_report(u))
        self.at(self.now + retry, "pull_timer", v, root, token)

    def on_pull_req(self, h: int, v: int, fresh: list, rep: tuple = ()) -> None:
        hold, want = self.nodes[h], self.nodes[v]
        self.hear(hold, v, rep)
        sent, top = 0, 0
        for item in fresh:
            if self.cfg.pull_mode == "oracle":  # the requester's state, read directly
                b = item
                if b in want.complete:
                    continue
                has = want.frags
            else:  # the requester's state as its request reported it
                b, has = item
            if b not in hold.complete:
                continue
            blk = self.blocks[b]
            missing = blk.mask & ~has
            if missing:
                self.send_frags(h, v, blk, missing, "pullresp")
                sent |= missing
                top = max(top, blk.rnd)
        if self.cfg.pull_fec >= 0 and self.cfg.strategy == "coded" and sent:
            # repair symbols over the response, so a lost fragment needs no retry
            cfg = self.cfg
            p = self.loss_for(hold, v)
            for _ in range(poisson_quantile(p * sent.bit_count(), 0.999) + cfg.pull_fec):
                mask = self.code_mask(sent)
                if not mask:
                    continue
                size = SYM_HEADER + cfg.frag
                self.bytes["pullresp"] += size + WIRE
                t = self.transmit(h, v, size, "pullresp")
                if t is not None:
                    self.at(t, "sym", v, top, mask)

    # ------------------------------------------------------------ report
    def mbps(self, table: dict, agg=None) -> float:
        span = max((b.built for b in self.blocks), default=0.0)
        per = [sum(table[k][v] for k in table) for v in range(self.cfg.n)]
        x = (agg or (lambda xs: sum(xs) / len(xs)))(per)
        return x * 8 / max(span, 1e-9) / 1e6

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
            "timeouts": self.why.get("timer", 0) / max(1, sum(self.why.values())),
            # mean over validators of all bytes sent and received, in Mb/s over the run, and the busiest
            "out_mbps": self.mbps(self.out), "in_mbps": self.mbps(self.inb),
            "out_mbps_max": self.mbps(self.out, max), "in_mbps_max": self.mbps(self.inb, max),
            "caught_up": self.caught_up if self.caught_up is not None else float("nan"),
            "misses": self.misses / (cfg.n * (cfg.rounds - cfg.warmup + 1)),
            "p_hat": sum(self.p_hat(u) for u in self.nodes) / cfg.n,
            "margin_end": sum(u.margin for u in self.nodes) / cfg.n,
        }


def simulate(**kw) -> dict:
    sim = Sim(Config(**kw))
    sim.run()
    out = sim.report()
    out["_deliver"] = sim.deliver
    out["_commit"] = sim.commit
    return out
