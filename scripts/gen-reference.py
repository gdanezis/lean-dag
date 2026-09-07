#!/usr/bin/env python3
"""Generate the report's reference appendices from the compiled source.

Appendix B holds every definition and structure the body or Appendix A
names, and Appendix C every theorem they name: the declarations the
report relies on, and no others. Both are verbatim, with the docstrings
the source already carries. Regenerating tracks the code, so the
reference cannot drift; `audit-report.py` check 4 then compares what is
written against the same extraction on every run.

A citation is a backticked name in the hand-written text. A qualified
citation (`MysticetiProperties.safety`) selects the declarations whose
full name ends in it; a bare one (`safety`) selects every declaration
of that short name, since that is what the prose means by it.

    scripts/extract-decls.py && scripts/gen-reference.py

Output replaces whatever lies between the two markers in docs/report.md.
Text outside them is hand-written and is never touched.
"""
import json
import pathlib
import re

ROOT = pathlib.Path(__file__).resolve().parent.parent
BEGIN = "<!-- BEGIN GENERATED REFERENCE -->"
END = "<!-- END GENERATED REFERENCE -->"

# Modules in the order a reader meets them, grouped into layers.
LAYERS = [
    ("The validator set and the fault model", ["Common.Counting", "Common.Validators"]),
    ("Blocks, validity, and the universe", ["Common.Block", "Common.BlockDag"]),
    ("Causal structure", ["Common.Causality", "Common.CausalHistory", "Common.History", "Common.Support",
     "Common.CommonCore", "Common.Persistence"]),
    ("Slots and the schedule", ["Common.Schedule", "Common.Leader"]),
    ("The commit rule, and the ledger", ["Mysticeti.Rule"]),
    ("Delivery, growth, and coverage", ["Common.Participation", "Mysticeti.Liveness"]),
    ("Time: GST, and the rated bounds", ["Mysticeti.Quantitative"]),
    ("The pacing structures, and the delivery they induce",
     ["Mysticeti.ViewPace", "Mysticeti.PaceDelivery"]),
    ("Chain quality", ["Quality.Coverage", "Quality.Inclusion", "Quality.Capstone"]),
    ("Denial of service", ["DoS.Exposure", "DoS.SelfParent", "DoS.Density", "DoS.Counting",
                           "DoS.Adoption", "DoS.Pedigree", "DoS.Exclusion",
                           "DoS.Acceptance", "DoS.Novelty", "DoS.Composition"]),
    ("Garbage collection", ["GC.Chop", "GC.ChopDecided", "GC.Window",
                            "GC.AttestedBase", "GC.Bootstrap", "GC.Horizon"]),
    ("Odontoceti", ["Odontoceti.Rules", "Odontoceti.Decision",
                    "Odontoceti.Liveness"]),
    ("The reactive schedule", ["Reactive.Basic", "Reactive.Mysticeti",
                               "Reactive.Odontoceti"]),
    ("Safe Skip: crash recovery in one message",
     ["SafeSkip.Basic", "SafeSkip.Invariance", "SafeSkip.Jump"]),
    ("Integration: composing the arcs",
     ["Integration.Preservation", "Integration.Coverage",
      "Integration.ScheduleShape", "Integration.Joiner",
      "Integration.Retention", "Integration.ReGenesis",
      "Integration.Stack", "Integration.Lifecycle",
      "Integration.Exposure", "Integration.DeliveryFill",
      "Integration.Margin", "Integration.CommonTarget"]),
    ("Hybrid fault tolerance: Byzantine and crash faults apart",
     ["Hybrid.Faults", "Hybrid.Rules", "Hybrid.Decision", "Hybrid.Liveness",
      "Hybrid.Conservativity"]),
    ("Adaptive leaders: the schedule as a fixpoint",
     ["Adaptive.Basic", "Adaptive.Policy", "Adaptive.Run", "Adaptive.Liveness",
      "Adaptive.Odontoceti"]),
    ("Nemo-Nemo: crash-fault consensus in two rounds",
     ["Nemo.Basic", "Nemo.Rules", "Nemo.Decision", "Nemo.Liveness"]),
    ("Mahi-Mahi: the asynchronous rule at wave w",
     ["MahiMahi.Model.Rules", "MahiMahi.Model.Decision", "MahiMahi.Model.Good",
      "MahiMahi.Model.Unpredictable", "MahiMahi.Safety.Statement",
      "MahiMahi.Counting.Statement", "MahiMahi.Liveness.Statement",
      "MahiMahi.Synchrony.Statement", "MahiMahi.Helpers.Rules",
      "MahiMahi.Helpers.Decision", "MahiMahi.Helpers.Counting",
      "MahiMahi.Helpers.Liveness", "MahiMahi.Helpers.Synchrony",
      "MahiMahi.Safety.Proof", "MahiMahi.Counting.Proof",
      "MahiMahi.Liveness.Proof", "MahiMahi.Synchrony.Proof"]),
    ("Black Marlin: the three-round commit rule",
     ["BlackMarlin.Model.Rules", "BlackMarlin.Model.Decision",
      "BlackMarlin.Safety.Statement", "BlackMarlin.Helpers.Rules",
      "BlackMarlin.Helpers.Decision", "BlackMarlin.Safety.Proof",
      "BlackMarlin.Liveness.Statement", "BlackMarlin.Helpers.Liveness",
      "BlackMarlin.Liveness.Proof", "BlackMarlin.Model.Round",
      "BlackMarlin.Reactive.Statement", "BlackMarlin.Helpers.Reactive",
      "BlackMarlin.Reactive.Proof", "BlackMarlin.Agreement.Statement",
      "BlackMarlin.Helpers.Agreement", "BlackMarlin.Agreement.Proof",
      "BlackMarlin.Model.Ledger", "BlackMarlin.Ledger.Statement",
      "BlackMarlin.Helpers.Ledger", "BlackMarlin.Ledger.Proof",
      "BlackMarlin.Model.Descent", "BlackMarlin.Descent.Statement",
      "BlackMarlin.Helpers.Descent", "BlackMarlin.Descent.Proof",
      "BlackMarlin.Model.Order", "BlackMarlin.Order.Statement",
      "BlackMarlin.Helpers.Order", "BlackMarlin.Order.Proof",
      "BlackMarlin.Model.Repair", "BlackMarlin.Repair.Statement",
      "BlackMarlin.Helpers.Repair", "BlackMarlin.Repair.Proof"]),
    ("FinWhale: the two-round commit rule",
     ["FinWhale.Model.Params", "FinWhale.Model.Rule", "FinWhale.Model.Skip",
      "FinWhale.Model.Decision", "FinWhale.Model.Anchor",
      "FinWhale.Model.Verdict", "FinWhale.Model.Pass", "FinWhale.Model.Order",
      "FinWhale.Model.View", "FinWhale.Model.Schedule",
      "FinWhale.Model.Creation", "FinWhale.Model.Liveness",
      "FinWhale.Model.Protocol",
      "FinWhale.Committee", "FinWhale.Counting",
      "FinWhale.Evidence", "FinWhale.Consequences", "FinWhale.Skip",
      "FinWhale.Decision", "FinWhale.Anchor", "FinWhale.Propagation",
      "FinWhale.Consistency", "FinWhale.Order", "FinWhale.Pass",
      "FinWhale.View", "FinWhale.Decided", "FinWhale.Validity",
      "FinWhale.Rotation", "FinWhale.Reactive", "FinWhale.Creation",
      "FinWhale.Holdings", "FinWhale.Protocol", "FinWhale.Liveness",
      "FinWhale.DoSBridge"]),
    ("Minnow: the minimal commit rule",
     ["Minnow.Model.Rule", "Minnow.Blocking"]),
    ("Barnacle: the adaptive leader count",
     ["Barnacle.Model.Rule", "Barnacle.Model.Schedule",
      "Barnacle.Model.Window", "Barnacle.Model.Run",
      "Barnacle.Model.Live", "Barnacle.Model.Heads", "Barnacle.Model.Anchored",
      "Barnacle.Window.Statement", "Barnacle.Agreement.Statement",
      "Barnacle.Ledger.Statement", "Barnacle.Conservativity.Statement",
      "Barnacle.Aimd.Statement", "Barnacle.Progress.Statement",
      "Barnacle.Heads.Statement", "Barnacle.Mysticeti.Statement",
      "Barnacle.MysticetiLive.Statement", "Barnacle.Odontoceti.Statement",
      "Barnacle.Nemo.Statement", "Barnacle.Helpers.Schedule",
      "Barnacle.Helpers.Anchored", "Barnacle.Helpers.Agreement",
      "Barnacle.Helpers.Ledger", "Barnacle.Helpers.Progress",
      "Barnacle.Helpers.Heads", "Barnacle.Window.Proof",
      "Barnacle.Agreement.Proof", "Barnacle.Ledger.Proof",
      "Barnacle.Conservativity.Proof", "Barnacle.Aimd.Proof",
      "Barnacle.Progress.Proof", "Barnacle.Heads.Proof",
      "Barnacle.Mysticeti.Proof", "Barnacle.MysticetiLive.Proof",
      "Barnacle.Odontoceti.Proof", "Barnacle.Nemo.Proof"]),
    ("The legacy quorum route (report §17)", ["Network.Quorum"]),
    ("Hydrozoan: the dual-path rule under hybrid faults",
     ["Hydrozoan.Model.Faults", "Hydrozoan.Model.Block", "Hydrozoan.Model.BlockUniverse",
      "Hydrozoan.Model.View", "Hydrozoan.Model.CausalHistory", "Hydrozoan.Model.Slots",
      "Hydrozoan.Model.DirectRules", "Hydrozoan.Model.Liveness", "Hydrozoan.Model.IndirectRules",
      "Hydrozoan.Model.Decided", "Hydrozoan.Helpers.Faults", "Hydrozoan.Helpers.Block",
      "Hydrozoan.Helpers.CausalHistory", "Hydrozoan.Helpers.History", "Hydrozoan.Helpers.Schedule",
      "Hydrozoan.Helpers.DirectRules", "Hydrozoan.Helpers.IndirectRules", "Hydrozoan.Helpers.Counting",
      "Hydrozoan.ThresholdArithmetic.Statement", "Hydrozoan.ThresholdArithmetic.Proof", "Hydrozoan.DirectSafety.Statement",
      "Hydrozoan.DirectSafety.Proof", "Hydrozoan.Helpers.SlotAgreement", "Hydrozoan.SlotAgreement.Statement",
      "Hydrozoan.SlotAgreement.Proof", "Hydrozoan.PrefixAgreement.Statement", "Hydrozoan.PrefixAgreement.Proof",
      "Hydrozoan.Helpers.DirectLiveness", "Hydrozoan.DirectLiveness.Statement", "Hydrozoan.DirectLiveness.Proof",
      "Hydrozoan.Helpers.IndirectLiveness", "Hydrozoan.IndirectLiveness.Statement", "Hydrozoan.IndirectLiveness.Proof",
      "Hydrozoan.Helpers.EventualDecision", "Hydrozoan.EventualDecision.Statement", "Hydrozoan.EventualDecision.Proof",
      "Hydrozoan.Helpers.Grounding", "Hydrozoan.Grounding.Statement", "Hydrozoan.Grounding.Proof"]),
    ("Optimal-Hydrozoan: the fast path at Hydrangea's bound",
     ["OptimalHydrozoan.Model.Faults", "OptimalHydrozoan.ThresholdArithmetic.Statement", "OptimalHydrozoan.ThresholdArithmetic.Proof",
      "OptimalHydrozoan.Model.Universe", "OptimalHydrozoan.Helpers.Universe", "OptimalHydrozoan.Model.DirectRules",
      "OptimalHydrozoan.Model.IndirectRules", "OptimalHydrozoan.Model.Decided", "OptimalHydrozoan.Helpers.DirectRules",
      "OptimalHydrozoan.Helpers.IndirectRules", "OptimalHydrozoan.Helpers.Counting", "OptimalHydrozoan.Helpers.Decided",
      "OptimalHydrozoan.DirectSafety.Statement", "OptimalHydrozoan.DirectSafety.Proof", "OptimalHydrozoan.SlotAgreement.Statement",
      "OptimalHydrozoan.Helpers.SlotAgreement", "OptimalHydrozoan.SlotAgreement.Proof", "OptimalHydrozoan.PrefixAgreement.Statement",
      "OptimalHydrozoan.PrefixAgreement.Proof", "OptimalHydrozoan.Helpers.DirectLiveness", "OptimalHydrozoan.DirectLiveness.Statement",
      "OptimalHydrozoan.DirectLiveness.Proof", "OptimalHydrozoan.Helpers.IndirectLiveness", "OptimalHydrozoan.IndirectLiveness.Statement",
      "OptimalHydrozoan.IndirectLiveness.Proof", "OptimalHydrozoan.EventualDecision.Statement", "OptimalHydrozoan.EventualDecision.Proof",
      "OptimalHydrozoan.Grounding.Statement", "OptimalHydrozoan.Helpers.Grounding", "OptimalHydrozoan.Grounding.Proof",
      "OptimalHydrozoan.Model.Faults", "OptimalHydrozoan.ThresholdArithmetic.Statement", "OptimalHydrozoan.ThresholdArithmetic.Proof",
      "OptimalHydrozoan.Model.Universe", "OptimalHydrozoan.Helpers.Universe", "OptimalHydrozoan.Model.DirectRules",
      "OptimalHydrozoan.Model.IndirectRules", "OptimalHydrozoan.Model.Decided", "OptimalHydrozoan.Helpers.DirectRules",
      "OptimalHydrozoan.Helpers.IndirectRules", "OptimalHydrozoan.Helpers.Counting", "OptimalHydrozoan.Helpers.Decided",
      "OptimalHydrozoan.DirectSafety.Statement", "OptimalHydrozoan.DirectSafety.Proof", "OptimalHydrozoan.SlotAgreement.Statement",
      "OptimalHydrozoan.Helpers.SlotAgreement", "OptimalHydrozoan.SlotAgreement.Proof", "OptimalHydrozoan.PrefixAgreement.Statement",
      "OptimalHydrozoan.PrefixAgreement.Proof", "OptimalHydrozoan.Helpers.DirectLiveness", "OptimalHydrozoan.DirectLiveness.Statement",
      "OptimalHydrozoan.DirectLiveness.Proof", "OptimalHydrozoan.Helpers.IndirectLiveness", "OptimalHydrozoan.IndirectLiveness.Statement",
      "OptimalHydrozoan.IndirectLiveness.Proof", "OptimalHydrozoan.EventualDecision.Statement", "OptimalHydrozoan.EventualDecision.Proof",
      "OptimalHydrozoan.Grounding.Statement", "OptimalHydrozoan.Helpers.Grounding", "OptimalHydrozoan.Grounding.Proof"]),
]

KINDS = ("def", "abbrev", "structure", "class", "inductive")


def tidy(doc):
    """The docstring as prose: bold markers kept, hard wraps joined."""
    if not doc:
        return ""
    doc = re.sub(r"\n\s*\n", "\x00", doc.strip())
    doc = re.sub(r"\s*\n\s*", " ", doc)
    return doc.replace("\x00", "\n\n")


def cited(root):
    """The names the hand-written report cites: every backticked
    identifier in the body and in Appendix A, split into qualified
    citations and bare ones."""
    text = (root / "docs/report.md").read_text()
    hand = text[:text.index(BEGIN)] if BEGIN in text else text
    names = set(re.findall(r"`([A-Za-z][A-Za-z0-9_.'\u2032]*)`", hand))
    qualified = {n for n in names if "." in n}
    bare = {n for n in names if "." not in n}
    return qualified, bare


def is_cited(d, qualified, bare):
    """Whether a declaration is one the report names."""
    full = d["name"]
    short = full.rsplit(".", 1)[-1]
    if short in bare:
        return True
    return any(full == q or full.endswith("." + q) for q in qualified)


def entry(d, out):
    mod = d["module"].removeprefix("LeanDag.")
    out.append(f"#### `{d['name']}`")
    out.append("")
    out.append(f"*{d['kind']}, `{mod}.lean`*")
    out.append("")
    out.append("```lean")
    out.append(d["statement"])
    out.append("```")
    out.append("")
    doc = tidy(d["doc"])
    if doc:
        out.append(doc)
        out.append("")


def main():
    decls = json.loads((ROOT / "docs/decls.json").read_text())
    qualified, bare = cited(ROOT)
    lib = [d for d in decls if d["module"].startswith("LeanDag.")
           and d["kind"] in KINDS and is_cited(d, qualified, bare)]
    by_module = {}
    for d in lib:
        by_module.setdefault(d["module"].removeprefix("LeanDag."), []).append(d)

    placed = set()
    out = [BEGIN, ""]
    out.append("## Appendix B. The definition reference")
    out.append("")
    out.append(f"The {len(lib)} definitions and structures the report names, in")
    out.append("the order a reader meets them. Each entry is the source text,")
    out.append("unabridged, with the explanation the source carries. This")
    out.append("appendix is generated from the compiled development by")
    out.append("`scripts/gen-reference.py`, which selects what the body and")
    out.append("Appendix A cite; the statements are therefore the declarations")
    out.append("themselves rather than transcriptions of them.")
    out.append("")
    out.append("Some entries carry proofs, which can look like a")
    out.append("misclassification. They are not. A structure in Lean may have")
    out.append("fields that are propositions — a block record requires causal")
    out.append("closure, validity and non-equivocation — so *constructing* one")
    out.append("means discharging those obligations, and the proof is part of")
    out.append("the definition rather than a theorem about it. A theorem, by")
    out.append("contrast, asserts a proposition about objects already built,")
    out.append("and those are Appendix C.")
    out.append("")

    n = 0
    for title, modules in LAYERS:
        entries = [d for m in modules for d in by_module.get(m, [])]
        if not entries:
            continue
        out.append(f"### {title}")
        out.append("")
        for d in entries:
            placed.add(d["name"] + "@" + d["module"])
            n += 1
            mod = d["module"].removeprefix("LeanDag.")
            out.append(f"#### `{d['name']}`")
            out.append("")
            out.append(f"*{d['kind']}, `{mod}.lean`*")
            out.append("")
            out.append("```lean")
            out.append(d["statement"])
            out.append("```")
            out.append("")
            doc = tidy(d["doc"])
            if doc:
                out.append(doc)
                out.append("")

    leftover = [d for d in lib if d["name"] + "@" + d["module"] not in placed]
    if leftover:
        out.append("### Not otherwise grouped")
        out.append("")
        for d in leftover:
            n += 1
            mod = d["module"].removeprefix("LeanDag.")
            out.append(f"#### `{d['name']}`")
            out.append("")
            out.append(f"*{d['kind']}, `{mod}.lean`*")
            out.append("")
            out.append("```lean")
            out.append(d["statement"])
            out.append("```")
            out.append("")
            doc = tidy(d["doc"])
            if doc:
                out.append(doc)
                out.append("")

    # ---- Appendix C: the theorems other modules depend on ----
    thms = [d for d in decls if d["module"].startswith("LeanDag.")
            and d["kind"] in ("theorem", "lemma")]
    public = [d for d in thms if is_cited(d, qualified, bare)]

    out.append("")
    out.append("---")
    out.append("")
    out.append("## Appendix C. The theorem reference")
    out.append("")
    out.append(f"The {len(public)} theorems the body or Appendix A names, each")
    out.append("the source statement, unabridged. Generated with Appendix B;")
    out.append("a theorem the report does not name is a step of an argument")
    out.append("rather than a result it presents, and the source is its")
    out.append("reference.")
    out.append("")
    seen_c = set()
    for title, modules in LAYERS:
        group = [d for m in modules for d in public
                 if d["module"].removeprefix("LeanDag.") == m]
        if not group:
            continue
        out.append(f"### {title}")
        out.append("")
        for d in group:
            seen_c.add(id(d))
            entry(d, out)
    rest = [d for d in public if id(d) not in seen_c]
    if rest:
        out.append("### Not otherwise grouped")
        out.append("")
        for d in rest:
            entry(d, out)

    out.append(END)
    body = "\n".join(out)

    report = ROOT / "docs/report.md"
    text = report.read_text()
    if BEGIN in text and END in text:
        a = text.index(BEGIN)
        b = text.index(END) + len(END)
        text = text[:a] + body + text[b:]
    else:
        text = text.rstrip("\n") + "\n\n" + body + "\n"
    report.write_text(text)
    print(f"{n} definitions, {len(public)} theorems")


if __name__ == "__main__":
    main()
