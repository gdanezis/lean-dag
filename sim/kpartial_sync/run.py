"""Sweeps comparing synchroniser strategies; writes results.md and results.csv.

Each setting runs with several seeds; latency percentiles pool the samples of
all seeds, and the other columns average them.
"""

from __future__ import annotations

import csv
import statistics
import sys
from multiprocessing import Pool

from sim import simulate

N = int(sys.argv[1]) if len(sys.argv) > 1 else 100
SEEDS = [1, 2, 3]
BASE = dict(n=N, rounds=30, warmup=5)

VARIANTS = {
    "pull 500 ms": dict(strategy="pull", pull_timer=0.5),
    "pull 100 ms": dict(strategy="pull", pull_timer=0.1, retry_timer=0.1),
    "relay + pull 500 ms": dict(strategy="relay", pull_timer=0.5),
    "coded + pull 500 ms": dict(strategy="coded", pull_timer=0.5),
}

GROUPS = {
    "loss": "Loss sweep (all four strategies)",
    "reorder": "Heavy reordering",
    "badlinks": "A few bad links",
    "symbols": "Coded: symbols per receiver per round (p = 1%)",
    "span": "Coded: rounds covered by a symbol",
    "trigger": "Coded: when symbols are sent",
    "density": "Coded: density of a symbol (p = 1%)",
    "scale": "Coded: number of validators (p = 1%)",
}

SCENARIOS = []
for loss in [0.0, 0.001, 0.01, 0.05]:
    for name, v in VARIANTS.items():
        SCENARIOS.append(("loss", f"p = {loss:.1%}", name, dict(loss=loss, **v)))
for name, v in VARIANTS.items():
    SCENARIOS.append(("reorder", "jitter 30 ms, p = 0.1%", name,
                      dict(loss=0.001, jitter=0.03, **v)))
    SCENARIOS.append(("badlinks", "5% of links at 20%, p = 0.1%", name,
                      dict(loss=0.001, bad_links=0.05, bad_loss=0.2, **v)))
for s in [2, 5, 10, 20, 33, 60]:
    SCENARIOS.append(("symbols", "p = 1%", f"s = {s}",
                      dict(loss=0.01, strategy="coded", symbols=s)))
for loss in [0.01, 0.05]:
    for span in [1, 2]:
        SCENARIOS.append(("span", f"p = {loss:.0%}", f"span {span}",
                          dict(loss=loss, strategy="coded", span=span)))
    for trig in ["build", "quorum"]:
        SCENARIOS.append(("trigger", f"p = {loss:.0%}", f"on {trig}",
                          dict(loss=loss, strategy="coded", trigger=trig)))
for d in [1, 2, 3]:
    SCENARIOS.append(("density", "p = 1%", f"2^-{d}",
                      dict(loss=0.01, strategy="coded", density=d)))
for n in [25, 50, 100, 150]:
    for name in ["pull 500 ms", "coded + pull 500 ms"]:
        SCENARIOS.append(("scale", f"n = {n}", name,
                          dict(loss=0.01, n=n, **VARIANTS[name])))


def one(job):
    i, seed = job
    group, setting, name, kw = SCENARIOS[i]
    return i, simulate(**{**BASE, **kw, "seed": seed})


def pct(xs, p):
    xs = sorted(xs)
    return xs[min(len(xs) - 1, int(p * len(xs)))] if xs else float("nan")


def merge(runs):
    out = {}
    for k in runs[0]:
        if k.startswith("_") or not isinstance(runs[0][k], (int, float)):
            out[k] = runs[0][k]
        else:
            out[k] = statistics.mean(r[k] for r in runs)
    dl = [x for r in runs for x in r["_deliver"]]
    cm = [x for r in runs for x in r["_commit"]]
    out.update(deliver_p50=pct(dl, 0.5), deliver_p99=pct(dl, 0.99),
               deliver_p999=pct(dl, 0.999), deliver_max=max(dl, default=float("nan")),
               commit_p50=pct(cm, 0.5), commit_p99=pct(cm, 0.99),
               commit_max=max(cm, default=float("nan")))
    return {k: v for k, v in out.items() if not k.startswith("_")}


if __name__ == "__main__":
    jobs = [(i, s) for i in range(len(SCENARIOS)) for s in SEEDS]
    runs = {}
    with Pool() as pool:
        for i, r in pool.imap_unordered(one, jobs):
            runs.setdefault(i, []).append(r)
    rows = []
    for i, (group, setting, name, kw) in enumerate(SCENARIOS):
        rows.append(dict(group=group, setting=setting, variant=name, **merge(runs[i])))
    with open("results.csv", "w", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=list(rows[0]))
        w.writeheader()
        w.writerows(rows)
    ms = lambda x: f"{x * 1000:.0f}"
    out = [f"# Synchroniser simulation, n = {N} unless stated, seeds {SEEDS}\n",
           "Latencies in ms, pooled over seeds. *deliver*: block built to admitted at "
           "another validator. *decide*: leader block built to decided (committed "
           "directly, or decided by a later direct commit). *direct*: fraction of "
           "leaders committed directly. *extra*: symbol and pull bytes per validator "
           "per round, and as a share of push bytes. *pulls*, *decoded*, *dup*: per "
           "validator per round (requests, fragments decoded, duplicate fragments).\n"]
    for g, title in GROUPS.items():
        out.append(f"\n## {title}\n")
        out.append("| setting | variant | s | deliver p50 / p99 / p99.9 | decide p50 / p99 / max "
                   "| round | direct | push KB | extra KB (%) | pulls | decoded | dup |")
        out.append("|---|---|---|---|---|---|---|---|---|---|---|---|")
        for r in rows:
            if r["group"] != g:
                continue
            extra = r["sym_kb"] + r["pull_kb"]
            out.append(
                f"| {r['setting']} | {r['variant']} | {r['symbols']:.0f} "
                f"| {ms(r['deliver_p50'])} / {ms(r['deliver_p99'])} / {ms(r['deliver_p999'])} "
                f"| {ms(r['commit_p50'])} / {ms(r['commit_p99'])} / {ms(r['commit_max'])} "
                f"| {ms(r['round_time'])} | {r['direct']:.2f} | {r['push_kb']:.0f} "
                f"| {extra:.1f} ({100 * extra / r['push_kb']:.1f}%) | {r['pulls']:.2f} "
                f"| {r['decoded']:.1f} | {r['dup']:.2f} |")
    text = "\n".join(out) + "\n"
    open("results.md", "w").write(text)
    print(text)
