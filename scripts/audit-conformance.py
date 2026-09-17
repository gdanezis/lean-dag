#!/usr/bin/env python3
"""Which protocols have shown which properties.

`docs/target-properties.md` §11.2. Part 1 of the goal claims a set of
properties every DAG consensus rule must show; part 2 claims that showing
them buys every mechanism. Neither claim is worth much against one
protocol, so the count that matters is how many rules have instances —
and this recomputes it rather than trusting the table.

A rule is "conforming" for a property when some theorem's conclusion is
that property applied to the rule's carrier. Carriers are found by
scanning for `DagRule`-valued definitions, so a new one is picked up
without editing this script; a rule with no carrier cannot show anything
and its reason is recorded below.

Reads `docs/decls.json`; regenerate with `scripts/extract-decls.py`.
Reports only — it never fails a build, since a missing instance is work
outstanding rather than a defect.
"""

import json
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent

# The decision rules of this repository. `carrier` is the `DagRule` a
# rule's conformance is stated against, or None with the reason it has
# none.
# A rule may have more than one carrier: the core and Hydrozoan have
# their own, and Barnacle's interface supplies a second for the rules it
# instantiates. A property counts as shown at any of them.
RULES = [
    ("core Mysticeti",     ["MysticetiProperties.mysticetiRule"], None),
    ("reactive Mysticeti", ["MysticetiProperties.mysticetiRule"],
                           "shares the core's rule"),
    ("Hydrozoan",          ["Hydrozoan.rule"],                   None),
    ("Optimal-Hydrozoan",  ["OptimalHydrozoanProperties.optimalRule"], None),
    ("Odontoceti",         ["OdontocetiProperties.odontocetiRule"], None),
    ("Nemo",               ["NemoProperties.nemoRule"], None),
    ("Mahi-Mahi",          ["MahiMahiProperties.mahiMahiRule"],
                           "one carrier per wave width"),
    ("Hybrid / Orcaella",  ["HybridProperties.hybridRule"], "one carrier per threshold"),
    ("FinWhale",           ["FinWhaleProperties.finWhaleRule"],  "band transported one rule at a time (Band.lean)"),
    ("Steelhead",          ["SteelheadProperties.steelheadRule"],
                           "one carrier per wavelength function; no offset band (§3.4c)"),
    ("Black Marlin",       [], "no carrier; commits by round, no slot-indexed relation"),
]

# The obligations, in the order 11.1 lists them.
# The five every rule owes and its support, then the three in
# `Properties/Optional/`, owed only when a mechanism asks:
# `CommitsDirect` by a rule whose direct predicate a window count reads,
# `SkipsUnsupported` by one that skips without waiting for an anchor,
# and `Quorate` by chain quality.
#
# `Support` is the shape a rule's commit counts in (`Properties/Support.lean`),
# pinned by three laws. `Local` and `OfCoverage` are generic for the
# one-round shape and per rule otherwise; `Commits` is per rule always, so
# a rule is scored as having a support when a `.Commits` law is stated at
# its carrier. `LeaderCommits` is derived from it (§11.8).
OBLIGATIONS = ["Banded", "Agree", "CommitsCandidate", "Indirect", "Support",
               "CommitsDirect", "SkipsUnsupported", "Quorate", "SelfParent", "NoEquiv",
               "OfCoverage"]
REQUIRED = 5
DERIVED = ["LeaderCommits", "Persist", "LocalTruncate", "Descends"]
# The headlines (`Properties/Arcs/Headline.lean`): safety across any stack, and
# liveness (progress and inclusion) at the rule's support, each instantiated once.
HEADLINE = ["Safe", "Lives", "Progresses"]
# What each derived property follows from. `Descends` used to be an
# obligation and is now the indirect rule with a downward induction on
# top (`Properties/Derived/Descent.lean`).
DERIVED_FROM = {"LeaderCommits": "Support", "Persist": "Banded", "LocalTruncate": "Banded",
                "Descends": "Indirect"}

# Files that state the generic theory rather than an instance of it.
GENERIC = re.compile(r"^LeanDag\.Properties\b")


def owner(carrier):
    """The module prefix a carrier belongs to.

    Kept from when two carriers could share a short name (the core's
    `mysticetiRule` and a Barnacle copy of it); Barnacle's `BaseRule` now
    extends `DagRule` and names the protocol's carrier, so there is one
    carrier per rule, but a suffix match is still the wrong test.
    """
    return "LeanDag." + carrier.split(".")[0]


def conclusions(decls):
    """Map property name -> set of carriers it is shown for.

    Two ways of showing one: a theorem whose conclusion is the property
    at that carrier, or a conformance `Statement` that lists it — both
    count, since a protocol may discharge a conjunct inline rather than
    naming it."""
    out = {}
    for d in decls:
        if GENERIC.match(d["module"]):
            continue
        flat = " ".join(d["statement"].split())
        is_stmt = d["kind"] == "def" and d["name"] in ("Statement", "holds")
        if d["kind"] != "theorem" and not is_stmt:
            continue
        for prop in OBLIGATIONS + DERIVED + HEADLINE:
            if prop == "Support":
                hit = re.search(r"\)\.Commits\s*\(", flat) or re.search(r"\.Commits\s+\(", flat)
            elif prop == "OfCoverage":
                hit = re.search(r":\s*(LeanDag\.)?(Timed\.)?OfCoverage\b", flat)
            elif prop in ("Lives", "Progresses"):
                hit = re.search(r":\s*(LeanDag\.)?(Properties\.)?Support\." + prop + r"\b", flat)
            else:
                hit = (re.search(r":\s*(LeanDag\.)?(Properties\.)?" + prop + r"\b", flat)
                       or (is_stmt and re.search(r"Properties\." + prop + r"\b", flat)))
            if not hit:
                continue
            owners = {owner(c) for _, cs, _ in RULES for c in cs}
            for carrier in {c for _, cs, _ in RULES for c in cs}:
                if not re.search(r"\b" + re.escape(carrier.split(".")[-1]) + r"\b", flat):
                    continue
                mine = owner(carrier)
                # A statement in another carrier's namespace names that
                # carrier, not this one.
                if d["module"].startswith(mine) or not any(
                        d["module"].startswith(o) for o in owners if o != mine):
                    out.setdefault(prop, set()).add(carrier)
    return out


def main():
    path = ROOT / "docs/decls.json"
    if not path.exists():
        print("docs/decls.json missing; run scripts/extract-decls.py", file=sys.stderr)
        return 1
    shown = conclusions(json.loads(path.read_text()))

    cols = OBLIGATIONS + ["|"] + DERIVED + ["|"] + ["Safe", "Lives"]
    short = {"Causal": "caus", "Banded": "band", "Agree": "agre",
             "CommitsCandidate": "cand", "LeaderCommits": "lead",
             "Indirect": "indr", "Support": "supp",
             "CommitsDirect": "drct*", "SelfParent": "self*", "NoEquiv": "nequ*",
             "OfCoverage": "cov†",
             "Descends": "desc",
             "SkipsUnsupported": "skip*", "Quorate": "quor*",
             "Persist": "pers", "LocalTruncate": "trnc",
             "Safe": "safe", "Lives": "live",
             "|": "|"}
    width = max(len(name) for name, _, _ in RULES) + 1
    print("obligations, then what follows from them "
          "(der = free; desc = free, given indr)\n")
    print(" " * width + "  ".join(short[c].ljust(4) for c in cols))
    conforming = 0
    for name, carriers, note in RULES:
        cells = []
        has = lambda prop: any(c in shown.get(prop, ()) for c in carriers)
        for c in cols:
            if c == "|":
                cells.append("|   ")
            elif carriers and has(c):
                cells.append("yes ")
            elif c in DERIVED and carriers and has(DERIVED_FROM[c]):
                # a consequence of the band: nothing to show per protocol
                cells.append("der ")
            elif c == "Lives" and carriers and has("Progresses"):
                cells.append("prog")
            else:
                cells.append("--  ")
        print(name.ljust(width) + "  ".join(cells) + ("   " + note if note else ""))
        if carriers and all(has(c) for c in OBLIGATIONS[:REQUIRED]):
            conforming += 1

    allcarriers = {c for _, cs, _ in RULES for c in cs}
    without = [n for n, cs, _ in RULES if not cs]
    partial_ = [n for n, cs, _ in RULES
                if cs and not all(any(c in shown.get(o, ()) for c in cs)
                                  for o in OBLIGATIONS[:REQUIRED])]
    print(f"\n{len(allcarriers)} carriers over {len(RULES)} rules; "
          f"{conforming} show the five properties and a support.")
    if partial_:
        print("Carrier but not the five and a support: " + ", ".join(partial_) + ".")
        print("  `Agree` and `CommitsCandidate` are `Barnacle.Laws` renamed;")
        print("  and `Banded` is the induction each rule owes. Those three are per-rule.")
    if without:
        print(f"{len(without)} with no carrier: " + ", ".join(without) + ".")
    print("* CommitsDirect, SkipsUnsupported, Quorate, SelfParent and NoEquiv are optional "
          "(`Properties/Optional/`): owed\n  only when a mechanism reads the "
          "rule's direct predicate, when the rule skips\n  without waiting for an "
          "anchor, or when a deployment quotes chain quality (the coverage\n  half needs "
          "Quorate; the inclusion half needs SelfParent and NoEquiv).")
    print("† OfCoverage is not a property: it is the timed model's bridge into `Support.live`\n"
          "  (`LeanDag/Timed/Coverage.lean`), owed only by a rule with a synchronous story.\n"
          "  A reactive rule reaches `live` from its wait clauses and shows `--` here.")
    print("`supp`: the rule has a `Support` with its `Commits` law (`Properties/Support.lean`),\n"
          "  so `LeaderCommits`, liveness on a covered DAG and liveness across every\n"
          "  `Sustains` are the generic theorems applied (`Arcs/Liveness.lean`).")
    print("`safe`, `live`: the headlines (`Properties/Arcs/Headline.lean`) instantiated at the\n"
          "  rule — safety across any stack of mechanisms; liveness as progress and inclusion\n"
          "  at the rule's support, `prog` where the rule has no self-parent clause and shows\n"
          "  progress only.")
    print("`lead` is derived: `LeaderCommits` at `Support.live` follows from the support's\n"
          "  `Commits` law. A rule that also states it against a precondition of its own\n"
          "  reads `yes`; one that relies on the derivation reads `der`.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
