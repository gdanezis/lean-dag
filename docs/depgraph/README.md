# The support graph: what holds up what

> **Provenance.** Code and prose in this project were co-written with
> heavy LLM assistance. The Lean proofs are machine-checked — the kernel
> verifies every theorem against its stated form — but whether the
> definitions and theorem statements capture their *intended* meaning,
> and whether the surrounding prose is faithful to what is proved, has
> only human-plus-LLM review behind it. Read critically.

Two diagrams of the development's claim structure, extracted from the
compiled Lean environment rather than written by hand, each in two
renderings:

* `support-core.svg` — the assumptions of report §4 and the core
  safety/liveness results (T, M, L), with each box's Lean name.
* `support-full.svg` — the same, plus every principal result of the four
  arcs (CQ, D/C/B, G, O), with each box's Lean name.
* `support-core-compact.svg`, `support-full-compact.svg` — the same two
  diagrams at smaller scale with Lean names omitted, embedded as the
  report's own two figures (§6.8 and §26).

An arrow `A → B` means **`A` is used in the proof of `B`**, directly or
through unlabelled lemmas. Arrows implied by longer paths are removed, so
what remains is the shortest honest account of each dependency. A box
with no incoming arrow rests only on definitions and unlabelled lemmas.

## How it is built

    lake env lean scripts/DepGraph.lean > docs/depgraph/deps.tsv
    python3 scripts/depgraph.py

`deps.tsv` is not tracked: it is eight megabytes, changes with every
Lean edit, and the audit scripts that read it (`audit-rounds.py`,
`audit-bespoke.py`, `audit-mechanisms.py`) say to regenerate it before
trusting a run. The four SVGs are tracked, since the report embeds two
of them as figures.

`scripts/DepGraph.lean` walks `Environment.constants` and, for every
declaration of this development, records the constants appearing in its
type **and in its body** — for a theorem, that body is the proof term, so
the edges are the real proof structure rather than the statement's
signature. Two details of the extraction matter:

* `ConstantInfo.value?` returns `none` for imported theorems in this Lean
  version; the proof term must be reached by matching `.thmInfo`
  explicitly.
* Private declarations and compiler-generated auxiliaries (`_proof_N`,
  `_simp_N`) must be kept as pass-through nodes. A labelled result
  frequently reaches another only through one of them, and filtering
  them at extraction silently severs the path. Mathlib and core constants
  *are* dropped, safely: they never mention a `LeanDag` constant, so no
  path between two of our results can run through them.

`scripts/depgraph.py` selects the node set — the assumptions of §4 by
name, and every principal result by parsing **Appendix A of the report**,
so the diagram tracks the report automatically — then contracts paths
through unlabelled lemmas, takes the transitive reduction, assigns
columns by longest path, orders each column by barycentre sweeps, and
emits SVG. No external graph tooling is used; hovering a box shows its
full Lean name and the report's statement of it.

## What it confirms

The extracted edges are an independent check on the report's prose, and
three claims come out exactly as stated:

* **`P3′` (`ValidWrt.self_parent`) has no outgoing edge in the core
  view**, and in the full view feeds only C1′, C3′, G1, G9 and G11 —
  precisely the report's claim that safety and liveness never consume the
  self-parent clause and that it is required only by the DoS and
  garbage-collection arcs.
* **`L7a ← N2a, P7` and `L7b ← N2b, P9, T1`** — the two derivations of
  eventual DAG synchrony, matching the §4.4 table row for row. The extra
  `T1` on the timing route is the non-equivocation step that identifies a
  validator's block with the one the timing structure names.
* **`O5 ← O1, O1′, O2, O3, O4′`** — Odontoceti's agreement rests on
  exactly the four counting theorems plus twin uniqueness, as §10.3
  claims, and `O4′` is genuinely consumed rather than decorative.

## PDFs

    scripts/svg2pdf.sh

places vector PDFs of all four SVGs in `docs/pdf/`, each on a page cut to
the diagram's own size. Typst is already required for the document build
and renders SVG natively, so no separate converter is involved.

## Regenerating

All four SVGs are checked in, but they are build products: re-run the
two commands above after adding results or renaming lemmas. `deps.tsv`
is also useful on its own — it is the full declaration-level dependency
graph of the development (≈9,900 declarations, ≈82,500 edges).
