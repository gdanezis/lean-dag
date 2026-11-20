"""Adaptive control against fixed budgets, over many scenarios; writes adapt_results.md.

A fixed budget assumes one loss rate: the scenario's mean over links and time
(what a well-informed operator would configure), or 1%. The adaptive
validator estimates loss, margin and timers locally (Config.adapt). Latency
percentiles pool the seeds; the other columns average them.
"""

from __future__ import annotations

import random
import statistics
import sys

from run import pct, run_jobs
from sim import simulate

N = int(sys.argv[1]) if len(sys.argv) > 1 else 100
SEEDS = [1, 2, 3, 4, 5, 6, 7, 8]
BOOT = 400  # bootstrap resamples for the interval of p99
BASE = dict(n=N, rounds=30, warmup=5)
ROUND = 0.095  # rough round time, to average a loss schedule over a run


def mean_loss(kw: dict) -> float:
    """The loss averaged over links and over the run."""
    p0 = kw.get("loss", 0.01)
    T = (kw.get("rounds", 30) + 6) * ROUND
    pts = [(0.0, p0)] + [s for s in kw.get("loss_steps", ()) if s[0] < T] + [(T, None)]
    p = sum((b[0] - a[0]) * a[1] for a, b in zip(pts, pts[1:])) / T
    for key in ("lossy_in", "lossy_out"):
        if kw.get(key):
            frac, q = kw[key]
            p = p * (1 - frac) + q * frac
    if kw.get("bad_links"):
        p = p * (1 - kw["bad_links"]) + kw["bad_loss"] * kw["bad_links"]
    return p


F = (N - 1) // 3
BURSTS = tuple(x for t in (1.0, 2.0, 3.0, 4.0) for x in ((t, 0.05), (t + 0.2, 0.001)))
# (group, scenario, settings)
SCENARIOS = [
    ("steady", "p = 0.1%", dict(loss=0.001)),
    ("steady", "p = 1%", dict(loss=0.01)),
    ("steady", "p = 2%", dict(loss=0.02)),
    ("steady", "p = 5%", dict(loss=0.05)),
    ("changing loss", "step up: 0.1% → 5% (1.5–3 s) → 0.1%",
     dict(loss=0.001, loss_steps=((1.5, 0.05), (3.0, 0.001)), rounds=50)),
    ("changing loss", "step down: 5% → 0.1% at 1.5 s", dict(loss=0.05, loss_steps=((1.5, 0.001),), rounds=50)),
    ("changing loss", "ramp: 0.1% → 5% over 1–2.5 s",
     dict(loss=0.001, loss_steps=((1.0, 0.005), (1.5, 0.01), (2.0, 0.02), (2.5, 0.05)), rounds=50)),
    ("changing loss", "bursts: 5% for 0.2 s each second, else 0.1%", dict(loss=0.001, loss_steps=BURSTS, rounds=50)),
    ("uneven loss", "5% of links at 20%, p = 0.1%", dict(loss=0.001, bad_links=0.05, bad_loss=0.2)),
    ("uneven loss", "10% of validators receive at 10%, p = 0.1%", dict(loss=0.001, lossy_in=(0.1, 0.1))),
    ("uneven loss", "10% of validators send at 10%, p = 0.1%", dict(loss=0.001, lossy_out=(0.1, 0.1))),
    ("timing", "jitter 30 ms, p = 0.1%", dict(loss=0.001, jitter=0.03)),
    ("timing", "jitter 5 → 30 ms (1.5–3 s) → 5 ms, p = 0.1%",
     dict(loss=0.001, jitter_steps=((1.5, 0.03), (3.0, 0.005)), rounds=50)),
    ("timing", "routing stretch σ = 0.4, p = 1%", dict(loss=0.01, stretch=0.4)),
    ("faults", "outage 500 ms, p = 0.1%", dict(loss=0.001, rounds=60, outage=(7, 2.0, 0.5))),
    ("faults", "f crashed at 0.5 s, p = 1%", dict(loss=0.01, crash=(tuple(range(1, 3 * F, 3)), 0.5))),
    ("size", "n = 50, p = 1%", dict(loss=0.01, n=50)),
    ("size", "n = 150, p = 1%", dict(loss=0.01, n=150)),
    ("size", "no payload, p = 1%", dict(loss=0.01, payload=0)),
    ("size", "payload 100 KB, p = 1%", dict(loss=0.01, payload=100_000)),
    ("combined", "p = 1%, jitter 20 ms, stretch 0.3, 5% of links at 20%",
     dict(loss=0.01, jitter=0.02, stretch=0.3, bad_links=0.05, bad_loss=0.2)),
]
CONFIGS = [("fixed, mean loss", lambda kw: dict(assumed_loss=mean_loss(kw))),
           ("fixed, 1%", lambda kw: dict(assumed_loss=0.01)),
           ("adaptive", lambda kw: dict(adapt=True))]
JOBS = [(si, ci) for si in range(len(SCENARIOS)) for ci in range(len(CONFIGS))]


def settings(si: int, ci: int) -> dict:
    kw = SCENARIOS[si][2]
    return {**BASE, **kw, **CONFIGS[ci][1](kw)}


def cost(job) -> float:
    kw = settings(*job[0])
    return kw["n"] ** 2 * kw["rounds"] * (1 + kw.get("payload", 10_000) / 10_000)


def p99_interval(rs: list) -> tuple:
    """A 95% bootstrap interval for the pooled p99, resampling leader rounds: the
    decisions of one leader at every validator move together, so a leader round,
    not a single decision, is the unit of sampling."""
    groups = []
    for r in rs:
        by = {}
        for x, rho in zip(r["_commit"], r["_commit_round"]):
            by.setdefault(rho, []).append(x)
        groups += list(by.values())
    rng = random.Random(0)
    qs = []
    for _ in range(BOOT):
        xs = [x for _ in groups for x in rng.choice(groups)]
        qs.append(pct(xs, 0.99))
    qs.sort()
    return qs[int(0.025 * BOOT)], qs[int(0.975 * BOOT)]


def one(job):
    (si, ci), seed = job
    return (si, ci), simulate(**{**settings(si, ci), "seed": seed})


if __name__ == "__main__":
    jobs = sorted(((j, s) for j in JOBS for s in SEEDS), key=lambda j: -cost(j))
    runs = {}
    for key, r in run_jobs(one, jobs):
        runs.setdefault(key, []).append(r)
    ms = lambda x: f"{x * 1000:.0f}" if x == x else "—"

    def stats(key):
        rs = runs[key]
        cm = [x for r in rs for x in r["_commit"]]
        mean = lambda k: statistics.mean(r[k] for r in rs)
        extra = mean("sym_kb") + mean("pull_kb")
        cu = [r["caught_up"] for r in rs if r["caught_up"] == r["caught_up"]]
        lo, hi = p99_interval(rs)
        return dict(p50=pct(cm, 0.5), p99=pct(cm, 0.99), lo=lo, hi=hi, mx=max(cm, default=float("nan")),
                    round=mean("round_time"), extra=extra, share=100 * extra / mean("push_kb"),
                    misses=mean("misses"), est=mean("p_hat"), margin=mean("margin_end"),
                    timeouts=mean("timeouts"), cu=statistics.mean(cu) if cu else float("nan"))

    S = {k: stats(k) for k in runs}
    out = [f"# Adaptive control, n = {N} unless stated, seeds {SEEDS}\n",
           "*fixed, mean loss*: the symbol budget assumes the loss averaged over links and over "
           "the run. *fixed, 1%*: it assumes 1%. *adaptive*: `adapt = True`. Latencies in ms, "
           "pooled over seeds. *extra*: symbol and pull bytes as a share of push bytes.\n",
           "## Summary: decide p99 in ms [95% interval, resampling leader rounds] (extra)\n",
           "| group | scenario | mean loss | " + " | ".join(c[0] for c in CONFIGS) + " |",
           "|---|---|---|" + "---|" * len(CONFIGS)]
    for si, (g, name, kw) in enumerate(SCENARIOS):
        cells = []
        for ci in range(len(CONFIGS)):
            s = S[(si, ci)]
            cells.append(f"{ms(s['p99'])} [{ms(s['lo'])}–{ms(s['hi'])}] ({s['share']:.1f}%)")
        out.append(f"| {g} | {name} | {100 * mean_loss(kw):.2f}% | " + " | ".join(cells) + " |")
    out += ["\n## Detail\n",
            "*misses*: partial blocks not repaired by symbols before the repair deadline (fixed: "
            "500 ms; adaptive: twice the round time), per validator per round. *timeouts*: blocks "
            "built on the round timeout. *loss est.*, *margin*: means over validators at the end. "
            "*catch-up*: outage only.\n",
            "| scenario | budget | decide p50 / p99 / max | round | extra KB (%) | misses | timeouts | loss est. | margin | catch-up |",
            "|---|---|---|---|---|---|---|---|---|---|"]
    for si, (g, name, kw) in enumerate(SCENARIOS):
        for ci, (cn, _) in enumerate(CONFIGS):
            s = S[(si, ci)]
            ad = ci == len(CONFIGS) - 1
            out.append(f"| {name} | {cn} | {ms(s['p50'])} / {ms(s['p99'])} / {ms(s['mx'])} | {ms(s['round'])} "
                       f"| {s['extra']:.1f} ({s['share']:.1f}%) | {s['misses']:.3f} | {s['timeouts']:.3f} "
                       f"| {s['est']:.4f} | {s['margin']:.1f} |" if ad else
                       f"| {name} | {cn} | {ms(s['p50'])} / {ms(s['p99'])} / {ms(s['mx'])} | {ms(s['round'])} "
                       f"| {s['extra']:.1f} ({s['share']:.1f}%) | {s['misses']:.3f} | {s['timeouts']:.3f} | — | — |")
            out[-1] += f" {ms(s['cu']) if 'outage' in kw else ''} |"
    text = "\n".join(out) + "\n"
    open("adapt_results.md", "w").write(text)
    print(text)
