# lean-dag — writing style

> **Provenance.** Code and prose in this project were co-written with
> heavy LLM assistance. The Lean proofs are machine-checked — the kernel
> verifies every theorem against its stated form — but whether the
> definitions and theorem statements capture their *intended* meaning,
> and whether the surrounding prose is faithful to what is proved, has
> only human-plus-LLM review behind it. Read critically.

Conventions for the documents and the source, derived from the editing
passes that produced them. The rules are few; the examples are the point.

## 0. What is governed by what

`report.md` is the academic artifact and is held to all four sections
below. The companion documents — `spec.md`, `liveness.md`, `garbage.md`,
`odontoceti.md`, `chain-quality.md`, `related.md` and the rest — are
technical records of a completed development: they are held to §2–§4 and
to the final-state rule in §1, but their register may be more informal
than the report's. They predate this guide and still contain several of
the phrases tabulated below; the substitutions are owed at their next
revision, not as a separate sweep.

**Source docstrings are report text.** The report's reference appendices
are generated from them, so §1 applies to every docstring in `LeanDag/`,
and fixes belong at source — editing the generated copy diverges it and
is undone at the next regeneration.

## 1. Register

`report.md` is an academic report. It states results; it does not narrate
the work that produced them.

**Avoid commercial metaphor.** It reads as sales copy and is almost
always less precise than the literal statement.

| Instead of | Write |
|:---|:---|
| this clause is load-bearing | this clause is indispensable to §8 |
| what the stronger committee buys | what the stronger committee yields |
| at the price of `X` | though `X`; at the cost of `X` |
| where the fifth `f` is spent | where the committee of size `5f+1` is required |
| pruning only cheapens blocks | pruning only decreases novelty |
| obtained for free | obtained without further hypotheses |
| mechanisation earns its keep here | the value of mechanisation is concentrated here |
| speed is bought where … | the schedule accelerates only where … |
| what the rule buys anything for | the whole of what the rule contributes |
| every deferred block gets cheaper | every deferred block's novelty only decreases |
| P3′ pays in §8 and charges in §12 | the self-parent clause, on both sides |
| spends the fifth `f` | the first use of the fifth `f` |
| transports more cheaply | transports with fewer side conditions |
| the obligation costs nothing | the obligation needs no further hypothesis |
| retaining it costs nothing but | retaining it requires nothing beyond |
| an affordable block | a block within the budget |

**Avoid figurative verbs and nouns.** A metaphor that has to be decoded
is slower to read than the thing it replaces.

| Instead of | Write |
|:---|:---|
| the assumption would swallow its own conclusion | would presuppose what it is invoked to establish |
| retains the attacker's freight | retains material injected by an adversary |
| the budget paces what an author can inject | limits the rate at which an author can inject material |
| that indexing does the work | that indexing is what carries the argument |
| the two budgets sandwich each other | the two formulations bound each other to within a factor of `f` |
| its engine deserves stating | the mechanism behind it should be stated |
| exclusion does not depend on luck | does not depend on favourable circumstances |
| it just stores more junk | it merely retains more |
| the refutation is seen to bite | the refutation is not vacuous |
| the concern does not bite | the concern does not reach the condition |
| the clearest vindication of | which is what the layering was drawn for |
| the arc's headline on data | the arc's principal witness |
| `history_B1_subset_fill` is its engine | … is the mechanism behind it |

**Avoid the laboratory notebook.** The report is not a record of how the
development evolved. Delete, rather than rephrase:

- corrections of earlier drafts — "the correction to §4.3's earlier
  claim", "an earlier version of this development fixed …";
- discovery narration — "turned out", "the surprise", "we found",
  "worth recording", "two things must be said";
- process asides — "this cost a debugging round", "for anyone repeating
  the exercise".

State the final position. If an alternative was considered and rejected,
say so in one clause and give the reason — *"a block-count variant was
considered and rejected: neither route yields an informative ratio"* —
not the history of considering it.

A note on the two hardest cases. **`budget` and `cost` are defined
terms** of §8 and §9 — "the novelty budget", "storage cost" — and are
not metaphor when used of the quantities those sections define.
Extending them figuratively is the error: a *block* is not affordable,
a *clause* does not pay for itself, and an `f` is not spent. And a
**pleasing formulation is the most dangerous kind**: the banned row
above beginning "P3′ pays" was written because it reads well, survived
several revisions on that ground, and says less than the plain
sentence that replaced it.

**Permitted, and encouraged.** Established technical metaphor with a
fixed meaning in the field: quorum *intersection*, the correct
*backbone*, a causal *cone*, a sliding *window*, a *horizon*. Honest
negative statements: *"this does not hold before `R`"*, *"a `T`-relative
variant would require a `T`-relative backbone lemma, and is not attempted
here"*. Naming which hypothesis a result consumes, and where.

## 2. Structure

- **Define notation before use.** Global symbols belong in the notation
  table of §2.5; a symbol introduced in one section and used in another
  belongs there too.
- **Every displayed Lean statement is copied from the source** and
  type-checks against the built library. Binders may be elided for
  layout; mark an elision with `…`.
- **Labels** are alphanumeric by area — T, M, L (core), V, CU, RS
  (view convergence, catch-up, reactive), P, N, R (trust boundary),
  CQ, D/C/B/E, G, O, SS, AL, H, NN, MM, BN, HZ, OH, I (the arcs) — and must be *introduced where
  the reader first meets them*, not only in the appendix.
- **Tables are left-aligned** (`|:---|`), and carry short cells with the
  explanation in the surrounding prose.
- **Cross-references** use `§n.m`. After renumbering, re-run the audit in
  §4 below; a reference to a section that no longer exists is the most
  common casualty of restructuring.
- **Section references in docstrings name their document** — `` `spec.md`
  §3.2 ``, `report §6.9` — never a bare `§4.2`. In the generated
  appendices a bare reference reads as a report section, and it may even
  *resolve* to one by coincidence, which the resolution check cannot
  catch. Audit check 6 enforces this.
- **Uniqueness and superlative claims are the most fragile sentences.**
  "the only consumer", "used at exactly one place", "nothing else
  imports", "derived twice" — each is true of an architecture and false
  of its successor. When results move, search for these before searching
  for names.
- **Generated regions are never edited by hand.** Text between
  `BEGIN/END GENERATED` markers is owned by its generator; a global edit
  (a renumbering script especially) that touches it silently diverges
  the document from source until the next regeneration reverts the fix.
- **A topic confined to its own section gets pointers only elsewhere.**
  Outside the section, at most a bare pointer — naming no theorem and no
  assumption of the confined topic — as with the rotation backbone
  (report §11.5).

## 3. The Lean source

- **A witness precedes the theorem.** Every definition is exercised on a
  concrete model by `decide` before anything is proved from it. A
  definition that cannot be witnessed is a definition that may be
  vacuous.
- **Docstrings say why, not what.** The statement already says what.
  Record the design decision, the alternative rejected, and the
  hypothesis that is genuinely consumed.
- **Names**: `X_of_Y` concludes `X` from characteristic hypothesis `Y`;
  a prime marks a post-`R` or incremental variant; a protocol variant
  lives in its own namespace (`Odontoceti.DirectCommit`) rather than
  carrying a suffix.
- **Arcs are additive.** A new development goes in its own directory and
  consumes the core read-only. If it requires a change to the core, that
  is a finding to report, not a refactor to perform quietly.
- **Every public declaration carries its own `/-- … -/` docstring.** A
  `/-!` section comment documents the section and attaches to nothing; a
  definition whose explanation lives only there shows bare in the
  reference.
- **Docstrings precede attributes**: `/-- … -/` above `@[simp]`, not
  between the attribute and the declaration, which does not parse.
- **Standard axioms only** — `propext`, `Classical.choice`, `Quot.sound`.
  No `sorry`, no bespoke axioms, no `native_decide`.

## 4. Before committing a document change

The mechanical part is one pipeline, and the pre-merge ritual is to run
it and require an empty diff — which regeneration being deterministic
makes meaningful:

    lake build
    lake env lean scripts/DepGraph.lean > docs/depgraph/deps.tsv
    scripts/extract-decls.py && scripts/gen-reference.py
    scripts/depgraph.py && scripts/svg2pdf.sh
    scripts/audit-report.py
    git diff --stat   # empty, or the committed state was stale

`audit-report.py` runs six checks: cross-references resolve;
identifiers resolve against the extraction (regenerate it first — a
stale `deps.tsv` reports every new result as unknown); displayed
statements name nothing their declaration lacks; displayed statements
are verbatim, as tokenised subsequences of the source; the banned
phrases of §1 are absent, appendices included; and docstring section
references are qualified.

The first, second, third, fourth and sixth checks apply to the report.
The banned-phrase check applies to **every document in `docs/`** except
this one, which quotes the phrases in order to ban them. A new design
record is therefore covered from the moment it is added, and no
document is exempt for being a working note: the register rules are
about accuracy rather than formality, and a working note that says a
clause "earns its keep" is as imprecise as a report that does.

Two judgement checks remain:

3. **Claims are consistent with what was added.** New material commonly
   falsifies an older sentence — a count, a "these two are the whole
   of …", a "two routes" that has become three. Search for the numeral.
4. **Read the render, not the source.** Rebuild with
   `docs/build-pdf.sh` and read the changed pages: clipped captions,
   tables that will not break, and figures too small to read are
   invisible in Markdown.
