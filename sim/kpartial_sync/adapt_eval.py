"""Adaptive control against fixed budgets; writes adapt_results.md.

A fixed budget assumes one loss rate: the true one (an oracle a validator does
not have), or a wrong one. The adaptive validator estimates loss, margin and
timers locally (Config.adapt). Latency percentiles pool the seeds.
"""

from __future__ import annotations

import os
import statistics
import sys
from multiprocessing import Pool

from run import guard, pct
from sim import simulate

N = int(sys.argv[1]) if len(sys.argv) > 1 else 100
SEEDS = [1, 2, 3]
BASE = dict(n=N, rounds=30, warmup=5)
STEP = dict(loss=0.001, loss_steps=((1.5, 0.05), (3.0, 0.001)), rounds=50)

CONFIGS = [("fixed, true loss (oracle)", dict()),
           ("fixed, assumes 1%", dict(assumed_loss=0.01)),
           ("adaptive", dict(adapt=True))]
SCENARIOS = []
for loss in [0.001, 0.01, 0.05]:
    for name, kw in CONFIGS:
        SCENARIOS.append((f"p = {loss:.1%}", name, dict(loss=loss, **kw)))
for sc, skw in [("5% of links at 20%, p = 0.1%", dict(loss=0.001, bad_links=0.05, bad_loss=0.2)),
                ("jitter 30 ms, p = 0.1%", dict(loss=0.001, jitter=0.03)),
                ("outage 500 ms, p = 0.1%", dict(loss=0.001, rounds=60, outage=(7, 2.0, 0.5)))]:
    for name, kw in CONFIGS + [("adaptive, reports only", dict(adapt=True, own_floor=False))]:
        SCENARIOS.append((sc, name, dict(**skw, **kw)))
for name, kw in [("fixed, assumes 0.1%", dict()), ("fixed, assumes 1%", dict(assumed_loss=0.01)),
                 ("fixed, assumes 5%", dict(assumed_loss=0.05)), ("adaptive", dict(adapt=True)),
                 ("adaptive, reports only", dict(adapt=True, own_floor=False))]:
    SCENARIOS.append(("p 0.1% → 5% (1.5–3 s) → 0.1%", name, dict(**STEP, **kw)))


def one(job):
    i, seed = job
    return i, simulate(**{**BASE, **SCENARIOS[i][2], "seed": seed})


if __name__ == "__main__":
    jobs = sorted(((i, s) for i in range(len(SCENARIOS)) for s in SEEDS),
                  key=lambda j: -SCENARIOS[j[0]][2].get("rounds", 30))
    runs = {}
    with Pool(initializer=guard, initargs=(os.getpid(),)) as pool:
        for i, r in pool.imap_unordered(one, jobs):
            runs.setdefault(i, []).append(r)
    ms = lambda x: f"{x * 1000:.0f}" if x == x else "—"
    out = [f"# Adaptive control, n = {N}, seeds {SEEDS}\n",
           "Latencies in ms, pooled over seeds. *extra*: symbol and pull KB per validator per "
           "round, and as a share of push. *misses*: partial blocks not repaired by symbols "
           "before the repair deadline (fixed: pull_timer, 500 ms; adaptive: twice the round time), per validator per round. *loss est.*, *margin*: means "
           "over validators at the end of the run. *catch-up*: outage only.\n",
           "| scenario | budget | decide p50 / p99 / max | round | extra KB (%) | misses | loss est. | margin | catch-up |",
           "|---|---|---|---|---|---|---|---|---|"]
    for i, (sc, name, kw) in enumerate(SCENARIOS):
        rs = runs[i]
        cm = [x for r in rs for x in r["_commit"]]
        mean = lambda k: statistics.mean(r[k] for r in rs)
        extra = mean("sym_kb") + mean("pull_kb")
        cu = [r["caught_up"] for r in rs if r["caught_up"] == r["caught_up"]]
        est = (f"| {mean('p_hat'):.4f} | {mean('margin_end'):.1f} " if kw.get("adapt") else "| — | — ")
        out.append(f"| {sc} | {name} | {ms(pct(cm, 0.5))} / {ms(pct(cm, 0.99))} / {ms(max(cm))} "
                   f"| {ms(mean('round_time'))} | {extra:.1f} ({100 * extra / mean('push_kb'):.1f}%) "
                   f"| {mean('misses'):.3f} " + est
                   + f"| {ms(statistics.mean(cu)) if 'outage' in kw and cu else ''} |")
    text = "\n".join(out) + "\n"
    open("adapt_results.md", "w").write(text)
    print(text)
