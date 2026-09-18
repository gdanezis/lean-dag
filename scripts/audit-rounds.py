#!/usr/bin/env python3
"""Guard the offset band: no rule may read an absolute round.

`Properties.AgreeBand` relates two universes whose rounds differ by a
constant, and `Properties.Banded` says every verdict is carried by such a
band. A rule can only satisfy it if its decision relation is invariant
under adding a constant to every block round and every `slotRound`.
Concretely: every round a rule reads must be a slot's round plus a
constant, or a comparison between two rounds. A round compared with a
literal, or reached by truncated subtraction, is not.

`docs/target-properties.md` §3.4c is the standing result. This script
recomputes it, so a genesis special case added to any rule fails here
rather than silently making that rule's band unprovable.

Reads `docs/depgraph/deps.tsv` and `docs/decls.json`; regenerate both
before trusting a run (see the top of `scripts/audit-report.py`).
Exits 1 on an unrecorded finding.
"""

import collections
import json
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent

# The decision relation of each rule. FinWhale has no single one; its
# commit and skip predicates stand in, which is itself §3.4c's finding.
RULES = {
    "core Mysticeti": ["LeanDag.Decided"],
    "Hydrozoan": ["LeanDag.Hydrozoan.Decided"],
    "Odontoceti": ["LeanDag.Odontoceti.Decided"],
    "Nemo": ["LeanDag.Nemo.Decided"],
    "Mahi-Mahi": ["LeanDag.MahiMahi.Decided"],
    "Hybrid": ["LeanDag.Hybrid.Decided"],
    "Optimal-Hydrozoan": ["LeanDag.OptimalHydrozoan.DecidedOpt"],
    "FinWhale": ["LeanDag.FinWhale.DirectCommit", "LeanDag.FinWhale.DirectSkip",
                 "LeanDag.FinWhale.IndirectCommit", "LeanDag.FinWhale.SPCommit",
                 "LeanDag.FinWhale.SPSkip", "LeanDag.FinWhale.FastCommit"],
    "Steelhead": ["LeanDag.Steelhead.Decided"],
}

# Findings §3.4c records. A new one must be understood and written down
# before it is added here. Steelhead's wavelength is a function of the
# absolute round by design; its rule has no offset band and claims none.
ALLOW = {
    ("LeanDag.MahiMahi.Model.Rules", "votingRound"),
    ("LeanDag.MahiMahi.Model.Rules", "decisionRoundAt"),
    ("LeanDag.MahiMahi.Model.Decision", "decisionRound"),
    ("LeanDag.Steelhead.Model.Decision", "steelheadAnchored"),
}

COMMENT = re.compile(r"/--.*?-/|--[^\n]*", re.S)
# A round read at all: only these definitions are examined.
TOUCHES = re.compile(r"[Rr]ound")
CHECKS = [
    ("truncated subtraction on a round",
     re.compile(r"(?:[Rr]ound|\br\b|\bk\b)[^\n]{0,44}-\s*\d")),
    ("a round meets a literal",
     re.compile(r"\.round\s*(?:=|≠|≤|<|≥|>)\s*\d"
                r"|\d\s*(?:=|≠|≤|<|≥|>)\s*\(?[\w.]*block[^)\n]*\)?\.round")),
    ("division or modulus reaching a round",
     re.compile(r"[\w)]\s*[/%]\s*[\w(]")),
    ("case split on a round",
     re.compile(r"match[^\n]*\.round|\.round\s+with")),
]


def load_graph():
    edges = collections.defaultdict(set)
    kind, mod = {}, {}
    for line in (ROOT / "docs/depgraph/deps.tsv").read_text().splitlines():
        p = line.split("\t")
        if p[0] == "NODE":
            kind[p[1]], mod[p[1]] = p[3], p[2]
        elif p[0] == "EDGE":
            edges[p[1]].add(p[2])
    return edges, kind, mod


def closure(roots, edges, kind):
    """Every node a rule reaches, seeded with the rule's constructors."""
    stack = [n for r in roots for n in kind if n == r or n.startswith(r + ".")]
    seen = set()
    while stack:
        n = stack.pop()
        if n in seen:
            continue
        seen.add(n)
        stack.extend(edges.get(n, ()))
    return seen


def main():
    edges, kind, mod = load_graph()
    decls = json.loads((ROOT / "docs/decls.json").read_text())
    idx = {}
    for d in decls:
        idx.setdefault((d["module"], d["name"]), d)

    def lookup(module, full):
        parts = full.split(".")
        for i in range(len(parts) - 1, -1, -1):
            d = idx.get((module, ".".join(parts[i:])))
            if d:
                return d
        return None

    findings, recorded, reads = [], [], 0
    for rule, roots in RULES.items():
        for n in sorted(closure(roots, edges, kind)):
            if kind.get(n) not in ("def", "abbrev", "ind", "structure", "class"):
                continue
            if "_proof_" in n or not mod.get(n, "").startswith("LeanDag"):
                continue
            d = lookup(mod[n], n)
            if d is None:
                continue
            body = COMMENT.sub(" ", d["statement"])
            if not TOUCHES.search(body):
                continue
            reads += 1
            for label, rx in CHECKS:
                if rx.search(body):
                    where = f"{rule}: {mod[n]}:{d['line']} `{d['name']}` — {label}"
                    (recorded if (mod[n], d["name"]) in ALLOW
                     else findings).append(where)
                    break

    print(f"{len(RULES)} rules, {reads} round-reading definitions examined")
    for r in sorted(set(recorded)):
        print(f"  recorded (§3.4c) {r}")
    for f in sorted(set(findings)):
        print(f"  FAIL {f}")
    if findings:
        print("\nAn absolute round read makes that rule's `Banded` unprovable.")
        print("Understand it, record it in §3.4c, then add it to ALLOW.")
        return 1
    print("  ok — no unrecorded absolute round read")
    return 0


if __name__ == "__main__":
    sys.exit(main())
