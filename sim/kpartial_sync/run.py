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
SEEDS_ABLATION = [1, 2, 3, 4, 5, 6]  # ablation and outage: decision tails vary between seeds
BASE = dict(n=N, rounds=30, warmup=5)

VARIANTS = {
    "pull 500 ms": dict(strategy="pull", pull_timer=0.5),
    "pull 100 ms": dict(strategy="pull", pull_timer=0.1, retry_timer=0.1),
    "relay + pull 500 ms": dict(strategy="relay", pull_timer=0.5),
    "coded + pull 500 ms": dict(strategy="coded", pull_timer=0.5),  # the default configuration
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
    "payload": "Payload size (p = 1%)",
    "ablation": "Ablation: the default with one component changed",
    "outage": "One validator receives nothing for a while (p = 0.1%)",
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
for s in [5, 10, 20, 40, 60, 100]:
    SCENARIOS.append(("symbols", "p = 1%", f"s = {s}",
                      dict(loss=0.01, strategy="coded", symbols=s)))
for loss in [0.01, 0.05]:
    for span in [1, 2, 4, 6]:
        SCENARIOS.append(("span", f"p = {loss:.0%}", f"span {span}",
                          dict(loss=loss, strategy="coded", span=span)))
    for trig in ["build", "quorum", "held"]:
        SCENARIOS.append(("trigger", f"p = {loss:.0%}", "on f + 1 held" if trig == "held" else f"on {trig}",
                          dict(loss=loss, strategy="coded", trigger=trig)))
for d in [1, 2, 3]:
    SCENARIOS.append(("density", "p = 1%", f"2^-{d}",
                      dict(loss=0.01, strategy="coded", density=d)))
for n in [25, 50, 100, 150]:
    for name in ["pull 500 ms", "coded + pull 500 ms"]:
        SCENARIOS.append(("scale", f"n = {n}", name,
                          dict(loss=0.01, n=n, **VARIANTS[name])))
for pay in [0, 1_000, 10_000, 100_000]:
    for name, kw in [("pull 500 ms", VARIANTS["pull 500 ms"]),
                     ("coded, one class", VARIANTS["coded + pull 500 ms"]),
                     ("coded, 256 B classes", dict(size_class=256, **VARIANTS["coded + pull 500 ms"])),
                     ("coded, nested 320 B", dict(cuts=(320,), **VARIANTS["coded + pull 500 ms"]))]:
        SCENARIOS.append(("payload", f"payload {pay // 1000} KB" if pay else "no payload", name,
                          dict(loss=0.01, payload=pay, **kw)))
OLD = dict(strategy="coded", trigger="quorum", pull_fec=-1)
ABLATION = [("best (default)", dict(strategy="coded")),
            ("+ tail (6, 3)", dict(strategy="coded", tail=(6, 3))),
            ("− pull repair", dict(strategy="coded", pull_fec=-1)),
            ("− pull repair + tail (6, 3)", dict(strategy="coded", pull_fec=-1, tail=(6, 3))),
            ("trigger quorum", dict(strategy="coded", trigger="quorum")),
            ("trigger build", dict(strategy="coded", trigger="build")),
            ("span 1", dict(strategy="coded", span=1)),
            ("span 6", dict(strategy="coded", span=6)),
            ("density 2^-2", dict(strategy="coded", density=2)),
            ("previous default", OLD),
            ("relay (uncoded)", dict(strategy="relay")),
            ("pull 500 ms only", VARIANTS["pull 500 ms"])]
for loss in [0.01, 0.05]:
    for name, kw in ABLATION:
        SCENARIOS.append(("ablation", f"p = {loss:.0%}", name, dict(loss=loss, **kw)))
for dur in [0.2, 0.5]:
    for name, kw in ABLATION:
        SCENARIOS.append(("outage", f"outage {dur * 1000:.0f} ms", name,
                          dict(loss=0.001, rounds=60, outage=(7, 2.0, dur), **kw)))

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
    jobs = [(i, s) for i, sc in enumerate(SCENARIOS)
            for s in (SEEDS_ABLATION if sc[0] in ("ablation", "outage") else SEEDS)]
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
    out = [f"# Synchroniser simulation, n = {N} unless stated, seeds {SEEDS} (ablation and outage {SEEDS_ABLATION})\n",
           "Latencies in ms, pooled over seeds. *deliver*: block built to admitted at "
           "another validator. *decide*: leader block built to decided (committed "
           "directly, or decided by a later direct commit). *direct*: fraction of "
           "leaders committed directly. *extra*: symbol and pull bytes per validator "
           "per round, and as a share of push bytes. *pulls*, *decoded*, *dup*: per "
           "validator per round (requests, fragments decoded, duplicate fragments). "
           "*catch-up*: from the end of the outage to the validator's first block at "
           "or above the median round of the others.\n"]
    for g, title in GROUPS.items():
        out.append(f"\n## {title}\n")
        if g == "outage":
            out.append("| setting | variant | s | catch-up per seed (ms) | mean |")
            out.append("|---|---|---|---|---|")
            for i, (group, setting, name, kw) in enumerate(SCENARIOS):
                if group != g:
                    continue
                cs = [r["caught_up"] for r in runs[i]]
                ok = [c for c in cs if c == c]
                out.append(f"| {setting} | {name} | {runs[i][0]['symbols']:.1f} | "
                           + ", ".join(ms(c) if c == c else "—" for c in cs)
                           + f" | {ms(statistics.mean(ok)) if ok else '—'} |")
            continue
        out.append("| setting | variant | s | deliver p50 / p99 / p99.9 | decide p50 / p99 / max "
                   "| round | direct | push KB | extra KB (%) | pulls | decoded | dup |")
        out.append("|---|---|---|---|---|---|---|---|---|---|---|---|")
        for r in rows:
            if r["group"] != g:
                continue
            extra = r["sym_kb"] + r["pull_kb"]
            out.append(
                f"| {r['setting']} | {r['variant']} | {r['symbols']:.1f} "
                f"| {ms(r['deliver_p50'])} / {ms(r['deliver_p99'])} / {ms(r['deliver_p999'])} "
                f"| {ms(r['commit_p50'])} / {ms(r['commit_p99'])} / {ms(r['commit_max'])} "
                f"| {ms(r['round_time'])} | {r['direct']:.2f} | {r['push_kb']:.0f} "
                f"| {extra:.1f} ({100 * extra / r['push_kb']:.1f}%) | {r['pulls']:.2f} "
                f"| {r['decoded']:.1f} | {r['dup']:.2f} |")
    text = "\n".join(out) + "\n"
    open("results.md", "w").write(text)
    print(text)
