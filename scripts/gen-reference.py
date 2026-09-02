#!/usr/bin/env python3
"""Generate the report's reference appendices from the compiled source.

Appendix B holds every definition and structure, Appendix C every theorem
another module depends on, and Appendix D indexes the remaining lemmas.
All are verbatim, with the docstrings the source already carries. Regenerating tracks the code, so the
reference cannot drift; `audit-report.py` check 4 then compares what is
written against the same extraction on every run.

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
    ("The validator set and the fault model", ["Validators"]),
    ("Blocks, validity, and the universe", ["Block", "BlockDag"]),
    ("Causal structure", ["Causality", "CausalHistory", "History", "Support",
     "CommonCore", "Persistence"]),
    ("Slots and the schedule", ["Schedule"]),
    ("The commit rule, and the ledger", ["Mysticeti"]),
    ("Delivery, growth, and coverage", ["Participation", "Liveness"]),
    ("Time: GST, and the rated bounds", ["Quantitative"]),
    ("The pacing structures, and the delivery they induce",
     ["ViewPace", "PaceDelivery"]),
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
     ["Nemo.Basic", "Nemo.CausalHistory", "Nemo.History", "Nemo.Support",
      "Nemo.Rules", "Nemo.Decision", "Nemo.Liveness"]),
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
      "Barnacle.Model.Live", "Barnacle.Model.Heads",
      "Barnacle.Window.Statement", "Barnacle.Agreement.Statement",
      "Barnacle.Ledger.Statement", "Barnacle.Conservativity.Statement",
      "Barnacle.Aimd.Statement", "Barnacle.Progress.Statement",
      "Barnacle.Heads.Statement", "Barnacle.Mysticeti.Statement",
      "Barnacle.MysticetiLive.Statement", "Barnacle.Odontoceti.Statement",
      "Barnacle.Nemo.Statement", "Barnacle.Helpers.Schedule",
      "Barnacle.Helpers.Mysticeti", "Barnacle.Helpers.Agreement",
      "Barnacle.Helpers.Ledger", "Barnacle.Helpers.Progress",
      "Barnacle.Helpers.Heads", "Barnacle.Helpers.MysticetiLive",
      "Barnacle.Helpers.Odontoceti", "Barnacle.Helpers.Nemo",
      "Barnacle.Helpers.NemoLive", "Barnacle.Window.Proof",
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


def labelled(root):
    """Short names of the results Appendix A indexes.

    Cross-module use is blind to the capstones: nothing consumes them
    precisely because they are endpoints, so by usage alone they file as
    internal steps. The statement index carries the judgement the graph
    cannot.
    """
    text = (root / "docs/report.md").read_text()
    app = text[text.index("## Appendix A"):text.index(BEGIN)]
    names = set()
    for lean in re.findall(r"^\|[^|]+\|[^|]+\| (.+?) \|$", app, re.M):
        names.update(re.findall(r"`([A-Za-z][A-Za-z0-9_.'\u2032]*)`", lean))
    return {n.rsplit(".", 1)[-1] for n in names}


def cross_module(root):
    """Names of theorems some other module depends on."""
    import collections
    rdeps = collections.defaultdict(set)
    mod = {}
    for line in (root / "docs/depgraph/deps.tsv").read_text().splitlines():
        p = line.split("\t")
        if p[0] == "NODE":
            mod[p[1]] = p[2]
        elif p[0] == "EDGE":
            rdeps[p[2]].add(p[1])
    out = set()
    for full, m in mod.items():
        if any(mod.get(u) and mod[u] != m for u in rdeps.get(full, ())):
            out.add((full.rsplit(".", 1)[-1], m))
    return out


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
    lib = [d for d in decls if d["module"].startswith("LeanDag.")
           and d["kind"] in KINDS]
    by_module = {}
    for d in lib:
        by_module.setdefault(d["module"].removeprefix("LeanDag."), []).append(d)

    placed = set()
    out = [BEGIN, ""]
    out.append("## Appendix B. The definition reference")
    out.append("")
    out.append("Every definition and structure of the development, in the order")
    out.append("a reader meets them. Each entry is the source text, unabridged,")
    out.append("with the explanation the source carries. This appendix is")
    out.append("generated from the compiled development by")
    out.append("`scripts/gen-reference.py`; the statements are therefore the")
    out.append("declarations themselves rather than transcriptions of them.")
    out.append("")
    out.append("Nine entries carry proofs, which can look like a")
    out.append("misclassification. They are not. A structure in Lean may have")
    out.append("fields that are propositions — `BlockUniverse` requires causal")
    out.append("closure, validity and non-equivocation — so *constructing* one")
    out.append("means discharging those obligations, and the proof is part of")
    out.append("the definition rather than a theorem about it. `chop`, `chopD`")
    out.append("and `toDelivery` are of this kind: each builds an object whose")
    out.append("type demands the proofs shown. A theorem, by contrast, asserts")
    out.append("a proposition about objects already built, and those are")
    out.append("Appendix C.")
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
    cross = cross_module(ROOT)
    idx = labelled(ROOT)
    def is_public(d):
        return (d["name"], d["module"]) in cross \
            or d["name"].rsplit(".", 1)[-1] in idx
    public = [d for d in thms if is_public(d)]
    internal = [d for d in thms if not is_public(d)]

    out.append("")
    out.append("---")
    out.append("")
    out.append("## Appendix C. The theorem reference")
    out.append("")
    out.append(f"The {len(public)} theorems that either another module of the")
    out.append("development depends on, or that Appendix A indexes as principal")
    out.append("results — the second clause because the capstones are consumed")
    out.append("by nothing, being endpoints. Each is the source statement,")
    out.append("unabridged. Generated with Appendix B.")
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

    # ---- Appendix D: the remaining lemmas, indexed ----
    out.append("---")
    out.append("")
    out.append("## Appendix D. Index of internal lemmas")
    out.append("")
    out.append(f"The {len(internal)} lemmas used only within the file that proves")
    out.append("them. They are steps of the arguments above rather than results")
    out.append("in their own right, so they are listed rather than displayed;")
    out.append("the source is the reference for their statements. One")
    out.append("subsection per module, in the layer order of Appendices B and C.")
    out.append("")

    # group by module, in LAYERS order (leftovers last)
    by_mod = {}
    for d in internal:
        by_mod.setdefault(d["module"].removeprefix("LeanDag."), []).append(d)
    ordered = [m for _, mods in LAYERS for m in mods if m in by_mod]
    ordered += [m for m in sorted(by_mod) if m not in ordered]

    for mod in ordered:
        group = sorted(by_mod[mod], key=lambda x: x["name"])
        out.append(f"### `{mod.replace(chr(46), chr(47))}.lean` ({len(group)})")
        out.append("")
        out.append("| Lemma | Role |")
        out.append("|:---|:---|")
        for d in group:
            doc = tidy(d["doc"]).split("\n")[0]
            doc = re.sub(r"\*\*", "", doc)
            if len(doc) > 110:
                doc = doc[:107].rsplit(" ", 1)[0] + " …"
            out.append(f"| `{d['name']}` | {doc or '—'} |")
        out.append("")

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
    print(f"{n} definitions, {len(public)} public theorems, "
          f"{len(internal)} indexed lemmas")


if __name__ == "__main__":
    main()
