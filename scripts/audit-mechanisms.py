#!/usr/bin/env python3
"""Which mechanisms have been instantiated for which protocols.

`docs/target-properties.md` part 2 claims that a rule showing the
properties composes with *each mechanism* with no further proof.
`audit-conformance.py` says which rules show which properties;
`audit-bespoke.py` says that no mechanism theorem reaches a protocol
outside them. Neither says whether a mechanism has ever been *applied*
to a rule — and it cannot, because a cell nobody wrote leaves no code
behind. Both audits check what exists; this one checks what does not.

A cell is:

* `yes`  — some declaration applies one of the mechanism's generic
           theorems and names one of the rule's carriers; or, for the
           cut, the fill and re-genesis, the carrier has a
           `DagRule.OnRecord` instance, since every verdict cell of
           those three mechanisms is `Properties/Arcs/Record.lean` at
           such an instance and nothing is written per cell;
* `open` — the rule shows everything the mechanism asks for and no such
           declaration exists. That is the gap this audit is for: not a
           defect, but work the properties have already paid for and
           nobody has collected;
* `--`   — the rule does not show what the mechanism asks for, which is
           `audit-conformance.py`'s business and not repeated here.

Reads `docs/depgraph/deps.tsv` and `docs/decls.json`; regenerate both
before trusting a run. Reports only — an uncollected cell is work
outstanding rather than a defect.
"""

import collections
import importlib.util
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent

_spec = importlib.util.spec_from_file_location(
    "conformance", ROOT / "scripts" / "audit-conformance.py")
conformance = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(conformance)

# The generic theorems a protocol instance of each mechanism applies,
# and the properties the mechanism asks of a rule. An entry point is a
# theorem stated over `Properties.DagRule`; applying one at a carrier is
# what "this rule has this mechanism" means.
# The third field names rules the mechanism does not apply to at all,
# with the reason: out of scope is not the same as owed. Barnacle's
# liveness runs on `LiveRule`, so a rule with no `BaseRule` instance is
# not a candidate for it however many properties it shows.
MECHANISMS = [
    ("garbage collection", {},
     ["LeanDag.Properties.LocalTruncate.of_banded",
      "LeanDag.Properties.Arcs.decided_of_truncate",
      "LeanDag.Properties.Arcs.decided_of_truncated",
      "LeanDag.Properties.Arcs.decided_agree_truncate",
      "LeanDag.Properties.Arcs.decided_agree_horizons",
      "LeanDag.Properties.DagRule.OnRecord.decided_chop_iff",
      "LeanDag.Properties.DagRule.OnRecord.decided_agree_chop"],
     ["Banded", "Agree"]),
    ("extension", {},
     ["LeanDag.Properties.Persist.of_banded",
      "LeanDag.Properties.Arcs.decided_skipFill",
      "LeanDag.Properties.Arcs.decided_agree_extends",
      "LeanDag.Properties.Arcs.decided_fill_of_persist",
      "LeanDag.Properties.Arcs.decided_fill_agree_of_properties",
      "LeanDag.Properties.DagRule.OnRecord.decided_fill",
      "LeanDag.Properties.DagRule.OnRecord.decided_agree_fill",
      "LeanDag.Properties.DagRule.OnRecord.decided_copyFill",
      "LeanDag.Properties.DagRule.OnRecord.decided_agree_copyFill"],
     ["Banded", "Agree"]),
    ("re-genesis", {},
     ["LeanDag.Integration.addGenesis", "LeanDag.Properties.DagRule.OnRecord.addGenesis",
      "LeanDag.Properties.DagRule.OnRecord.decided_addGenesis",
      "LeanDag.Properties.DagRule.OnRecord.decided_agree_addGenesis"],
     ["Banded", "Agree"]),
    ("adaptive leaders", {},
     ["LeanDag.Timed.descent_of_support"],
     ["Support", "Indirect"]),
    ("prompt skip", {},
     ["LeanDag.Properties.Arcs.decided_none_of_novel"],
     ["SkipsUnsupported"]),
    ("chain quality", {},
     ["LeanDag.Properties.Arcs.card_coveredAt_ge_of_decided",
      "LeanDag.Properties.Arcs.card_correct_le_two_mul_coveredAt_of_decided",
      "LeanDag.Properties.Arcs.ledger_coverage",
      "LeanDag.Properties.Arcs.mem_history_of_decided_commit",
      "LeanDag.Properties.Arcs.committed_of_correct_block",
      "LeanDag.Properties.Arcs.chain_quality"],
     ["Quorate", "CommitsCandidate"]),
]


# Barnacle reaches a rule through its `LiveRule`, which extends the
# carrier: a descent theorem names `mysticetiLive`, not `mysticetiRule`.
# For the leaders column those names count as the rule's.
LIVE_RULES = {
    "core Mysticeti": ["Barnacle.mysticetiLive"],
    "reactive Mysticeti": ["Barnacle.mysticetiLive"],
    "Hydrozoan": ["Barnacle.hydrozoanLive"],
    "Optimal-Hydrozoan": ["Barnacle.optimalHydrozoanLive"],
    "Odontoceti": ["Barnacle.odontocetiLive"],
    "Nemo": ["Barnacle.nemoLive"],
    "Hybrid / Orcaella": ["Barnacle.orcaellaLive"],
    "Mahi-Mahi": ["Barnacle.mahiMahiLive"],
    "FinWhale": ["Barnacle.finWhaleLive"],
    "Scheme family": ["Scheme.schemeLive"],
}


def graph():
    """Declaration -> what it uses, from the dependency graph."""
    uses = collections.defaultdict(set)
    for line in (ROOT / "docs" / "depgraph" / "deps.tsv").read_text().splitlines():
        parts = line.split("\t")
        if parts[0] == "EDGE":
            uses[parts[1]].add(parts[2])
    return uses


def main():
    import json
    path = ROOT / "docs" / "decls.json"
    if not path.exists():
        print("docs/decls.json missing; run scripts/extract-decls.py", file=sys.stderr)
        return 1
    shown = conformance.conclusions(json.loads(path.read_text()))
    uses = graph()

    # A carrier is "reached with" an entry point when one declaration
    # names both: the entry point is the mechanism, the carrier is the
    # rule it was applied at.
    applied = collections.defaultdict(set)
    for name, _, entries, _ in MECHANISMS:
        for d, used in uses.items():
            if not any(e in used for e in entries):
                continue
            for carrier in {c for _, cs, _ in conformance.RULES for c in cs}:
                if "LeanDag." + carrier in used:
                    applied[name].add(carrier)
            for rule, lives in LIVE_RULES.items():
                for lv in lives:
                    if "LeanDag." + lv in used:
                        for r, cs, _ in conformance.RULES:
                            if r == rule:
                                applied[name].update(cs)

    # A carrier read as block records has the cut, the fill and
    # re-genesis, with every verdict cell, at the instance: the
    # instance is the application.
    ON_RECORD = "LeanDag.Properties.DagRule.OnRecord"
    for d, used in uses.items():
        if ON_RECORD not in used:
            continue
        for carrier in {c for _, cs, _ in conformance.RULES for c in cs}:
            if "LeanDag." + carrier in used:
                for name in ("garbage collection", "extension", "re-genesis"):
                    applied[name].add(carrier)

    width = max(len(name) for name, _, _ in conformance.RULES) + 1
    cols = [name for name, _, _, _ in MECHANISMS]
    head = {"garbage collection": "cut", "extension": "extend", "re-genesis": "regen",
            "prompt skip": "prompt",
            "adaptive leaders": "leaders", "chain quality": "quality"}
    # Liveness across the DAG-transforming mechanisms is one generic theorem
    # per shape (`Support.live_of_sustains`, `Support.live_of_truncates`), fed
    # by the witness the mechanism already has. A rule with a support and a
    # witness therefore has it with nothing written per cell, which the
    # column scores as `der`; `yes` records an instance somebody did write.
    LIVE_ENTRIES = ["LeanDag.Properties.Support.live_of_sustains",
                    "LeanDag.Properties.Support.live_of_truncates",
                    "LeanDag.Properties.Support.decidedBelow_of_run_sustains",
                    "LeanDag.Properties.Support.decidedBelow_of_run_truncates"]
    live_applied = set()
    for d, used in uses.items():
        if not any(e in used for e in LIVE_ENTRIES):
            continue
        for carrier in {c for _, cs, _ in conformance.RULES for c in cs}:
            if "LeanDag." + carrier in used:
                live_applied.add(carrier)
    print("mechanisms applied, by rule (`open` = the properties are there "
          "and nobody collected)\n")
    # Composition is one generic theorem, `Stack.safe_and_live`, assembled
    # from the witnesses the mechanisms already have. A rule with a support
    # and witnesses for two mechanisms therefore composes them with nothing
    # written; `yes` records an assembled stack.
    STACK_ENTRIES = ["LeanDag.Properties.safety",
                     "LeanDag.Properties.Stack.safe_and_live",
                     "LeanDag.Properties.Stack.rebased",
                     "LeanDag.Properties.decided_of_rebased",
                     "LeanDag.Properties.Support.live_of_rebased"]
    stack_applied = set()
    for d, used in uses.items():
        if not any(e in used for e in STACK_ENTRIES):
            continue
        for carrier in {c for _, cs, _ in conformance.RULES for c in cs}:
            if "LeanDag." + carrier in used:
                stack_applied.add(carrier)
    print(" " * width + "  ".join(head[c].ljust(8) for c in cols) + "  live      stack   ")
    gaps = []
    for rule, carriers, _ in conformance.RULES:
        cells = []
        transformed = False
        transformers = 0
        for name, skip, _, needs in MECHANISMS:
            if not carriers or rule in skip:
                cells.append("--      ")
                continue
            has = all(any(c in shown.get(p, ()) for c in carriers) for p in needs)
            got = any(c in applied[name] for c in carriers)
            if got:
                cells.append("yes     ")
                if name in ("garbage collection", "extension", "re-genesis"):
                    transformed = True
                    transformers += 1
            elif has:
                cells.append("open    ")
                gaps.append((rule, name, needs))
            else:
                cells.append("--      ")
        has_supp = any(c in shown.get("Support", ()) for c in carriers)
        if any(c in live_applied for c in carriers):
            cells.append("yes     ")
        elif has_supp and transformed:
            cells.append("der     ")
        else:
            cells.append("--      ")
        if any(c in stack_applied for c in carriers):
            cells.append("yes     ")
        elif has_supp and transformers >= 2:
            cells.append("der     ")
        else:
            cells.append("--      ")
        print(rule.ljust(width) + "  ".join(cells))

    print()
    total = sum(1 for _ in gaps)
    if gaps:
        print(f"{total} cells are open — the rule shows what the mechanism asks "
              f"and no instance exists:")
        for rule, name, needs in gaps:
            print(f"  {rule:20s} {name:20s} (has {', '.join(needs)})")
    else:
        print("no open cells.")
    print("`live`: liveness across every DAG-transforming mechanism the rule has a witness\n"
          "  for — `der` from the rule's support and the witness alone (`Arcs/Liveness.lean`),\n"
          "  `yes` where an instance is written.")
    print("`stack`: the mechanisms compose with one another — `der` from the rule's support\n"
          "  and witnesses for two of them (`Stack.safe_and_live`, `Arcs/Stack.lean`),\n"
          "  `yes` where a stack is assembled or the headline `Properties.Safe` is instantiated.")
    print("\n`--`: the rule has no carrier, does not show what the mechanism asks "
          "(which is\n`audit-conformance.py`'s business), or is out of scope for it:")
    for name, skip, _, _ in MECHANISMS:
        for rule, why in sorted(skip.items()):
            print(f"  {rule:20s} {name:20s} {why}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
