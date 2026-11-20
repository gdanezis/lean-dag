"""How fast the adaptive validator follows a change of loss; writes adapt_trace.md.

Samples every 20 ms: the mean own loss estimate, the mean loss senders plan
for (over all pairs), the mean margin, and symbol bytes and misses since the
last sample; and the decision latency of each leader by the time it was
built. The oracle plans with each receiver's true current loss, so the gap
between the two is the cost of learning the loss.
"""

from __future__ import annotations

import statistics
import sys

from run import run_jobs
from sim import Config, Sim

N = int(sys.argv[1]) if len(sys.argv) > 1 else 100
SEEDS = [1, 2, 3, 4]
DT = 0.02
T0 = 1.5  # the change
SCENARIOS = [("step up: 0.1% → 5% at 1.5 s", dict(loss=0.001, loss_steps=((T0, 0.05),)), 0.05),
             ("step down: 5% → 0.1% at 1.5 s", dict(loss=0.05, loss_steps=((T0, 0.001),)), 0.001)]
CONFIGS = [("adaptive", dict(adapt=True)), ("adaptive, no reset", dict(adapt=True, est_reset=None)),
           ("oracle", dict(adapt=True, oracle_loss=True))]
MARKS = [-0.1, 0.02, 0.04, 0.06, 0.1, 0.2, 0.4, 1.0, 2.0, 3.0]
WINDOWS = [(-0.5, 0.0), (0.0, 0.1), (0.1, 0.2), (0.2, 0.4), (0.4, 1.0), (1.0, 3.0)]


class Traced(Sim):
    def __init__(self, cfg):
        super().__init__(cfg)
        self.trace = []
        self.last = (0, 0)

    def on_sample(self) -> None:
        live = [u for u in self.nodes if not self.crashed(u.vid)]
        own = statistics.mean(self.p_hat(u) for u in live)
        plan = statistics.mean(self.report_of(u, w.vid)[0] for u in live for w in live if w is not u)
        margin = statistics.mean(u.margin for u in live)
        sym, miss = self.bytes["sym"], self.misses
        self.trace.append((self.now, own, plan, margin, (sym - self.last[0]) / self.cfg.n,
                           miss - self.last[1]))
        self.last = (sym, miss)
        if self.now < T0 + 3.2:
            self.at(self.now + DT, "sample")


def one(job):
    si, ci, seed = job
    kw = {"n": N, "rounds": 60, "warmup": 3, **SCENARIOS[si][1], **CONFIGS[ci][1], "seed": seed}
    s = Traced(Config(**kw))
    s.at(DT, "sample")
    s.run()
    by_leader = [(s.blocks[s.leader_bid[r]].built, x) for x, r in zip(s.commit, s.commit_round)]
    return si, ci, s.trace, by_leader


if __name__ == "__main__":
    jobs = [(si, ci, seed) for si in range(len(SCENARIOS)) for ci in range(len(CONFIGS)) for seed in SEEDS]
    res = {}
    for si, ci, tr, bl in run_jobs(one, jobs):
        res.setdefault((si, ci), []).append((tr, bl))
    out = [f"# Adaptation to a change of loss, n = {N}, seeds {SEEDS}\n",
           "Means over seeds. *own*: validators' own loss estimate. *planned*: the loss senders "
           "plan for, over all pairs. *sym*: symbol KB per validator per 100 ms. *misses*: per "
           "validator per 100 ms. Times relative to the change.\n"]
    for si, (sname, _, target) in enumerate(SCENARIOS):
        out.append(f"\n## {sname}\n")
        out.append("| t − change (s) | " + " | ".join(f"{c} own / planned / margin / sym / misses"
                                                     for c, _ in CONFIGS) + " |")
        out.append("|---|" + "---|" * len(CONFIGS))
        series = {}
        for ci in range(len(CONFIGS)):
            trs = [tr for tr, _ in res[(si, ci)]]
            L = min(len(t) for t in trs)
            series[ci] = [tuple(statistics.mean(t[k][j] for t in trs) for j in range(6)) for k in range(L)]
        for m in MARKS:
            cells = []
            for ci in range(len(CONFIGS)):
                ser = series[ci]
                k = min(range(len(ser)), key=lambda k: abs(ser[k][0] - (T0 + m)))
                win = [x for x in ser if T0 + m - 0.1 < x[0] <= T0 + m]
                symr = sum(x[4] for x in win) / 1000
                missr = sum(x[5] for x in win) / N
                cells.append(f"{ser[k][1]:.4f} / {ser[k][2]:.4f} / {ser[k][3]:.1f} / {symr:.1f} / {missr:.2f}")
            out.append(f"| {m:+.2f} | " + " | ".join(cells) + " |")
        # rise or fall time of the planned loss to within 10% of the target
        for ci, (cn, _) in enumerate(CONFIGS):
            ser = series[ci]
            after = [x for x in ser if x[0] > T0]
            ok = [x[0] - T0 for x in after if abs(x[2] - target) <= 0.1 * target + 0.0005]
            out.append(f"\n{cn}: planned loss within 10% of {target:.1%} after "
                       f"{ok[0] * 1000:.0f} ms" if ok else f"\n{cn}: planned loss never within 10%")
        out.append("\nDecision latency (ms) of leaders by when they were built, mean / max:\n")
        out.append("| built, t − change (s) | " + " | ".join(c for c, _ in CONFIGS) + " |")
        out.append("|---|" + "---|" * len(CONFIGS))
        for a, b in WINDOWS:
            cells = []
            for ci in range(len(CONFIGS)):
                xs = [x for _, bl in res[(si, ci)] for t, x in bl if T0 + a <= t < T0 + b]
                cells.append(f"{1000 * statistics.mean(xs):.0f} / {1000 * max(xs):.0f}" if xs else "—")
            out.append(f"| [{a:+.1f}, {b:+.1f}) | " + " | ".join(cells) + " |")
    text = "\n".join(out) + "\n"
    open("adapt_trace.md", "w").write(text)
    print(text)
