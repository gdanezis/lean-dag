# lean-dag presentation — slide outline

Status: revision 3 (2026-10-14), the plan from which the deck was built.
The deck in `parts/` is now the authoritative text and has 91 slides: the
findings slides 30, 33, 42, 48, 56 and 92 of this outline are merged into the
table of slide 55 (deck slide 51), and later slide numbers shift accordingly.

This document lists every planned slide. Each entry gives:

- **Text**: the exact words on the slide.
- **Figure**: the illustration, if there is one. Stepped figures list their
  steps.
- **Notes**: what the presenter says, and the Lean evidence for every claim
  on the slide.

**Fact-checking rule.** Every factual claim on a slide has been checked
against the Lean sources (`LeanDag/`, `LeanDagTest/`): the definition or
theorem that states it, and for each example the witness that exhibits it.
The prose in `docs/` is not used as evidence. Paths in the notes are relative
to the repository root, as `path:line`. A claim with no Lean counterpart is
marked **(informal)** in the notes. Such a claim is background (for example,
what a paper says, or a latency in message delays). On a slide, a claim about
a paper always names the paper ("the paper's Lemma 22 …").

---

## 0. Decisions

Taken on 2026-10-14:

1. **Audience.** First-year PhD and MSc students in information security.
   They know signatures and hashes, but not BFT consensus or DAG protocols.
   - Part I teaches BFT basics (the fault model, why `n ≥ 3f + 1`, quorum
     intersection) before any DAG material.
   - Slide text uses plain words and symbols. Lean names go in the notes,
     except on the slides about the formalisation itself.
2. **Order of protocols.** Mysticeti first, as the reference rule; then the
   other rules from simplest to most complex: Nemo-Nemo, Odontoceti, Hybrid,
   FinWhale, Hydrozoan, Optimal-Hydrozoan, Bluestreak, Mahi-Mahi,
   Async BlueBottle, Steelhead.
3. **Minnow and Black Marlin** form their own section at the end of Part II,
   "Refuted rules".
4. **Format.** Content and style are separate files:
   - `presentation/index.html` holds the slides' content only, with semantic
     classes (`slide`, `title`, `notes`, `figure`, `dag`, `verdict-commit`, …)
     and no inline styles;
   - `presentation/theme.css` holds every visual choice (fonts, colours,
     layout, DAG figure colours) as CSS custom properties, so that changing
     the theme means editing or swapping this one file;
   - `presentation/deck.js` handles navigation (keys, slide counter, figure
     steps) and toggles speaker notes with `N`;
   - `presentation/dag.js` draws the DAG figures as SVG from a small
     description (validators × rounds × references). The SVG elements carry
     classes (`block`, `leader`, `vote`, `cert`, `blame`, `byz`, `crashed`,
     `twin`, `fill`), so their colours also come from `theme.css`.
   There are no external dependencies except one web font.
5. **Stepped figures.** Commit-rule figures advance in large steps, at most
   four per figure.
6. **Witnesses.** Every DAG figure is drawn from a Lean witness. Where none
   existed, one was added: `Ush` (LeanDagTest/Nemo/Shadow.lean), `Dbare`
   (LeanDagTest/FinWhale/Model.lean), and the AIMD sequence
   (LeanDagTest/Barnacle/Agreement.lean). Figures with no DAG are marked
   "(diagram)" or "(illustration of …)" with the theorem they illustrate.
7. **Length.** Slides are merged where the result stays legible. Each
   protocol's trade-offs are on its overview slide. The deck has 97 slides,
   plus one divider slide per part, generated from the part headings.
8. **Uniform slide shapes.** Each protocol's overview says what it changes
   relative to Mysticeti (or to the rule it extends) and ends with **+** and
   **−** lines. Each mechanism's first slide ends with a **Uses** line (the
   properties it reads) and a **Gives** line (what it guarantees).
9. **Barbouni** is proposed, not built; it appears only on the "open work"
   slide.

## Diagram conventions (apply to every DAG figure)

- Rows are validators `v0 … v{n−1}`; columns are rounds, increasing to the
  right. Block identifiers follow the witness, so that the figure can be
  checked against the Lean data.
- A block is a rounded square. An arrow from a block points to a block it
  references, one round earlier. References not relevant to the rule are
  drawn faint grey.
- The **leader block** `L` is filled in the accent colour.
- A **vote** for `L` has an accent outline.
- A **certificate** for `L` is filled in a second colour and labelled "C".
- A **blame** (a voting-round block that references no candidate of the
  slot) has a dashed outline.
- A Byzantine validator's row is shaded. Two blocks of one author in one
  round (twins) are drawn stacked.
- A crashed validator's row stops with a cross after its last block.
- A **filled** block (added by a recovery message) is drawn with a hatched
  fill.
- The verdict appears as a badge under the slot's column: **commit**,
  **skip**, or **undecided**.
- Counts are written next to their threshold, e.g. "3 ≥ q = 3".

**Symbols.** `n`, `f` and `q = n − f` mean the same throughout. Other
letters follow each paper and are local to that protocol's slides: FinWhale
and Hydrozoan use `p` for the faults the fast path tolerates; Hybrid uses `k`
for a threshold and Hydrozoan for a slack; Steelhead's period is `P`. In
Parts I, III and IV, `k` is a slot index.

---

# Part I — Foundations (slides 1–13)

### Slide 1 — Title

**Text.**
> Uncertified DAG consensus, machine-checked
> Protocols, properties and mechanisms, formalised in Lean 4

**Figure.** A faint DAG grid (4 validators × 6 rounds) as background.

**Notes.** The development is in Lean 4 over Mathlib. Every theorem named in
the deck is checked by the Lean kernel. Whether the definitions say what the
papers mean is checked by human and LLM review only; the README's provenance
note applies.

### Slide 2 — Scope

**Text.**
> - **Protocols.** Thirteen commit rules from the literature. Eleven are
>   proved safe and live; two are shown unsafe or not live by counterexamples.
> - **Properties.** One small interface — four properties and a "support" —
>   that each of the eleven rules is proved to satisfy.
> - **Mechanisms.** A pacemaker, chain quality, a storage bound, garbage
>   collection, crash recovery, adaptive leaders and an adaptive leader count,
>   checkpoints: each proved once against the interface, and composable.
> - Safety theorems use no assumption about the network.

**Figure.** Three columns, "Protocols", "Properties", "Mechanisms", with an
arrow Protocols → Properties labelled "each rule proves" and an arrow
Properties → Mechanisms labelled "each mechanism uses".

**Notes.**
- The eleven rules with a carrier (`DagRule`): `mysticetiRule`
  (LeanDag/Mysticeti/Properties.lean:52), `nemoRule`
  (LeanDag/Nemo/Carrier.lean:37), `odontocetiRule`
  (LeanDag/Odontoceti/Carrier.lean:32), `hybridRule`
  (LeanDag/Hybrid/Carrier.lean:29), `finWhaleRule`
  (LeanDag/FinWhale/Carrier.lean:39), `Hydrozoan.rule`
  (LeanDag/Hydrozoan/Helpers/Carrier.lean:27), `optimalRule`
  (LeanDag/OptimalHydrozoan/Carrier.lean:42), `bluestreakRule`
  (LeanDag/Bluestreak/Carrier.lean:35), `mahiMahiRule`
  (LeanDag/MahiMahi/Carrier.lean:28), `asyncBlueBottleRule`
  (LeanDag/AsyncBlueBottle/Carrier.lean:26), `steelheadRule`
  (LeanDag/Steelhead/Properties.lean:41).
- The two refuted rules: LeanDagTest/Minnow/Safety.lean,
  LeanDagTest/BlackMarlin/Divergence.lean.
- Safety without network hypotheses: `Properties.Safe`
  (LeanDag/Properties/Arcs/Headline.lean:46), `AnchoredRule.decided_agree`
  (LeanDag/Common/Anchored.lean:483).
- "Live" means progress for all eleven; four of them do not prove inclusion
  (slide 64).

### Slide 3 — The problem: replicated agreement

**Text.**
> - `n` validators each keep a copy of one ordered log (a ledger).
> - Clients submit transactions to any validator.
> - **Safety:** no two validators output conflicting logs.
> - **Liveness:** every transaction from a correct client is eventually in
>   every correct validator's log.
> - Some validators may be faulty. The protocol must tolerate them without
>   identifying them.

**Figure.** (diagram) Four validators, each holding a log of coloured boxes; three logs
equal, one validator marked faulty.

**Notes.** (informal) Background for the audience. In Lean the ledger is
`commitSeq` and `ledgerSet` (LeanDag/Common/Ledger.lean), and agreement of
ledgers is `AnchoredRule.commitSeq_agree`, `ledgerSet_agree`
(LeanDag/Common/Anchored.lean:521, 528).

### Slide 4 — Faults and quorums

**Text.**
> - A **Byzantine** validator may deviate arbitrarily from the protocol: send
>   false messages, send none, or send different messages to different
>   validators (equivocate).
> - A **crashed** validator stops and never resumes.
> - With `n ≥ 3f + 1` validators, at most `f` Byzantine, a **quorum** is
>   `n − f` validators.
> - Two quorums share at least `n − 2f ≥ f + 1` validators, so at least one
>   correct validator.
> - A correct validator does not equivocate, so two quorums cannot support
>   two conflicting statements.

**Figure.** (diagram) `n = 4`, `f = 1`: two overlapping sets of 3 validators drawn as
Venn circles. The overlap has 2 validators, of which at most 1 is Byzantine.

**Notes.**
- `Faults` (LeanDag/Common/Validators.lean:23): `3 * f + 1 ≤ n`,
  `byzantine.card ≤ f`. Quorum `quorumCard = n − f` (Validators.lean:39).
- Intersection: `exists_correct_mem_inter` (LeanDag/Common/Validators.lean:152).
- `Correct` is the complement of `byzantine`; a crashed validator is in
  `Correct`. Liveness theorems name the validators that keep producing
  separately.

### Slide 5 — What the network is assumed to do

**Text.**
> - Messages can be delayed arbitrarily, up to an unknown time GST (global
>   stabilisation time).
> - A **reliable** validator is a correct one that keeps producing blocks.
>   Liveness assumes a quorum of them.
> - After GST, what one reliable validator holds reaches every reliable
>   validator within `Δ`. This is called **view convergence**.
> - Safety is proved with no assumption about the network.
> - Liveness is proved from view convergence and the protocol's own rules.

**Figure.** (diagram) A timeline: before GST arrows of arbitrary length; after GST
arrows of length at most `Δ`.

**Notes.**
- (informal) Partial synchrony is background.
- View convergence: `ConvergesWithin` (LeanDag/Mysticeti/ViewPace.lean:61);
  `PaceCore.converges` (ViewPace.lean:166): `gst ≤ t → holds w t ⊆ holds v
  (t + delay)` for `v, w ∈ T`. `T` is a quorum-sized reliable set.
- `ViewPace` also carries protocol rules (P7, P9), which are the
  validators' behaviour, not the network.

### Slide 6 — Blocks and the DAG

**Text.**
> - Validators work in **rounds**. In each round each validator creates one
>   **block**: a round number, its creator, references to earlier blocks, and
>   a payload of transactions.
> - A valid block at round `r > 0` references blocks of round `r − 1` from at
>   least `n − f` distinct creators, one of them its own creator.
> - The blocks and references form a directed acyclic graph (DAG). A block's
>   **history** is every block it reaches by references. A validator's
>   **view** is the set of blocks it holds, including their histories.
> - Blocks are named by identifier (a hash), so two validators may hold
>   different sets of blocks but agree on what each identifier means.

**Figure.** Witness `U3`, rounds 0–2 (`n = 4`). Block 8 (`v0`, round 2) is
highlighted with its 3 references (blocks 4, 5, 6) drawn bold; block 4 is its
own previous block.

**Notes.**
- `Block` (LeanDag/Common/Block.lean:20); `ValidWrt` (Block.lean:61) has four
  clauses: predecessor (references at `r − 1`), distinct creators, quorum,
  self-parent (some block by the creator).
- Identifiers: `BlockRecord.block` (LeanDag/Common/BlockRecord.lean:35).
- History: `Reaches`, `historyFrom` (LeanDag/Common/CausalHistory.lean,
  LeanDag/Common/History.lean). A view is closed under references
  (`viewComplete`, LeanDag/Properties/Carrier.lean:49).
- Some rules change validity: Nemo drops self-parent and distinct creators
  and uses a majority (LeanDag/Nemo/Basic.lean:48); FinWhale replaces
  self-parent by leader exclusion (LeanDag/FinWhale/Model/Rule.lean:27–37);
  Bluestreak requires a quorum only of leader blocks
  (LeanDag/Bluestreak/Rule.lean:45, 79).

### Slide 7 — Certified and uncertified DAGs

**Text.**
> - In a certified DAG (Narwhal, Bullshark), each block receives a certificate,
>   built by an extra exchange of signatures, before others may reference it.
> - In an uncertified DAG (Mysticeti and this family), no certificate is sent.
> - A block two rounds above a leader **is** a certificate for it when its
>   references include `n − f` blocks that reference the leader.
> - Every direct commit rule is then a threshold on a set of blocks found in
>   the graph.

**Figure.** (illustration) Left: one round of a certified DAG with the extra
signature exchange between proposal and reference. Right: witness `U3`; the
certificate is the pattern found at round 2.

**Notes.**
- (informal) Narwhal and Bullshark.
- `Certifies` / `CarriesVotes` (LeanDag/Mysticeti/Model/Rule.lean:36;
  LeanDag/Common/Support.lean:324). Threshold shapes: LeanDag/Common/Rules.lean.

### Slide 8 — Slots and the leader schedule

**Text.**
> - A **slot** `k` has a round and a leader. The schedule may put several
>   leaders in one round and a leader in every round.
> - The **candidates** of slot `k` are the blocks of its leader at its round.
>   A correct leader has at most one candidate; a Byzantine leader may have
>   several.
> - Each slot is decided as **commit** (one candidate) or **skip**.
> - The ledger is the committed leaders in slot order, each followed by the
>   blocks in its history not yet output.

**Figure.** Two schedule strips, rounds 0–8: `pipeSlots` (one leader per
round) and `duoSlots` (two leaders per round), slot indices underneath.

**Notes.**
- `Slots` (LeanDag/Common/Slots.lean): `slotRound`, `leader`, a `kind`
  (default 0, :44), keyed by (round, leader) (:40).
- Pipelined and two-leader schedules: `pipeSlots`, `duoSlots`
  (LeanDagTest/Mysticeti/Pipelined.lean:53).
- `IsLeaderBlock` (LeanDag/Common/Leader.lean:28). A Byzantine leader with
  two candidates: witness `U6` (LeanDagTest/Mysticeti/Model.lean).
- Ledger: `commitSeq`, `ledgerSet`, `OutputAt` (LeanDag/Common/Ledger.lean).

### Slide 9 — One decision relation for every rule

**Text.**
> A slot is decided in one of four ways:
> 1. **Direct commit**: the rule's commit condition holds in the validator's
>    view.
> 2. **Direct skip**: the rule's skip condition holds.
> 3. **Indirect commit**: a later committed slot (the **anchor**) links a
>    candidate.
> 4. **Indirect skip**: the anchor links no candidate.
>
> The anchor is the nearest eligible committed slot above; every eligible
> slot in between must be skipped.

**Figure.** (diagram) Flowchart: "direct commit?" → commit; "direct skip?" → skip;
otherwise "nearest eligible committed anchor above" → "links a candidate?" →
commit (the least, if the rule has a tie-break) / skip.

**Notes.**
- `AnchoredRule.Decided` (LeanDag/Common/Anchored.lean:189). The
  "in between" premise is `hmid`.
- The relation is inductive, not a function. The order of questions in the
  flowchart is for presentation.

### Slide 10 — A rule is a card of thresholds

**Text.**
> Every rule fills in the same record:
> - the **wave**: how many rounds above the proposal the direct rules read;
> - the **commit** and **skip** conditions;
> - the **link** from an anchor, possibly in several graded **rungs**;
> - a **tie-break** between linked candidates.
>
> Agreement and the agreement of ledgers are proved once, for every rule whose
> card satisfies a short list of laws.

**Figure.** The Mysticeti card as a five-row table (filled in on slide 15),
with the other rules' cards shown as a stack of cards behind it.

**Notes.**
- `structure AnchoredRule` (LeanDag/Common/Anchored.lean:86): `waveAt`
  (the direct rules read up to round `r + waveAt`, as a function of the
  slot's kind), `Commit`, `Skip`, `rungs`, `Link`, `tie`, `Anchor`.
- `AnchoredRule.Laws` (Anchored.lean:292) is a property of the rule relative
  to a record invariant. Proved once: `decided_agree` (:483), `decided_mono`
  (:502), `commitSeq_agree`, `ledgerSet_agree`, `outputAt_agree`
  (:521, 528).

### Slide 11 — Eligibility

**Text.**
> - An anchor at slot `j` is **eligible** for slot `k` when
>   `round(k) + wave < round(j)`.
> - A slot one round above `k` cannot reach a certificate for `k`'s leader. A
>   slot two rounds above reaches one only if its own block is a certificate.
> - Anchoring at such slots would let one validator's direct commit become
>   another validator's indirect skip.

**Figure.** Schedule `pipeSlots` over a Mysticeti DAG, slots at every round. Slot `k` at
round `r`; slots at `r+1` and `r+2` greyed, "not eligible"; slot at `r+3`
marked "eligible anchor".

**Notes.**
- `EligibleAt` (LeanDag/Common/Anchored.lean:37).
- `¬ EligibleAt 2 0 1`, `¬ EligibleAt 2 0 2`, `EligibleAt 2 0 3`
  (LeanDagTest/Mysticeti/Pipelined.lean:72, 77, 80); the commit-to-skip
  hazard is described at Pipelined.lean:68–72.
- `Reaches` is reflexive (LeanDag/Common/CausalHistory.lean:35), which is why
  a round-`r+2` anchor that is itself a certificate does link.

### Slide 12 — A skip must count blocks

**Text.**
> - The absence of the leader's block from a view is not a sound reason to
>   skip: a validator cannot distinguish a silent leader from a leader whose
>   block has not yet arrived.
> - In Mysticeti a direct skip needs `n − f` blocks of the round above that
>   reference no candidate. Those blocks exist, and later blocks do not alter
>   them.

**Figure.** Stepped, two steps, on witness `Ugrow` (`n = 4`, every block
references the whole previous round, slot `k` at round `3k` led by `v1`).
(1) `Ugrow 5`, which stops before slot 2's round 6: no candidate exists, and
a skip on absence would fire. (2) The larger universe `Ugrow 8`:
slot 2 has 4 votes and 4 certificates and is committed. Caption: "a skip on
absence would have been overturned".

**Notes.**
- `blameSkip q`, `slotBlamers` (LeanDag/Common/Leader.lean:99).
- `ugrow_not_directSkip` (LeanDagTest/Mysticeti/Growth.lean:308);
  `ugrow_directCommit` (:272); `ugrow_commits_recur` (:332); `fairSlots`
  (:260–265).
- Other rules skip differently (Nemo never skips directly; FinWhale,
  Hydrozoan, Bluestreak use other counts); their slides say so.

### Slide 13 — How the results are checked

**Text.**
> - Every definition and theorem is written in Lean 4 and checked by its
>   kernel.
> - A **witness** is a small concrete DAG, usually 4 to 9 validators, on which
>   Lean computes the verdicts. Witnesses show that hypotheses can be met and
>   that bounds are tight; counterexamples show that a published claim fails.
> - Every DAG in this deck is drawn from a witness. Figures that are not are
>   marked as diagrams.

**Figure.** A Lean snippet: a witness DAG definition and one line
`example : DirectCommit U3 0 0 := by decide`, next to the drawn DAG.

**Notes.** `DirectCommit U3 0 0` is at LeanDagTest/Mysticeti/Model.lean:264.

---

# Part II — Protocols (slides 14–56)

### Slide 14 — The protocol family

**Text.**
> Each rule in this part changes Mysticeti in one or more ways:
>
> | Change | Rules |
> |---|---|
> | Crash faults only, two rounds | Nemo-Nemo |
> | A larger committee, two rounds | Odontoceti, Hybrid |
> | A fast commit beside the slow one | FinWhale, Hydrozoan, Optimal-Hydrozoan |
> | Fewer references per block | Bluestreak |
> | No timing assumption | Mahi-Mahi, Async BlueBottle, Steelhead |
>
> Then two published rules that have no indirect rule, Minnow and Black
> Marlin, with counterexamples to both; and a summary of all the rules.

**Figure.** (diagram) Mysticeti at the centre with an arrow to each rule,
labelled by its change. Hybrid hangs from Odontoceti, Optimal-Hydrozoan from
Hydrozoan, Async BlueBottle from Odontoceti and Mahi-Mahi, Steelhead from
Mysticeti and Mahi-Mahi.

**Notes.** The arrows are facts about the rule records (slide 10): Hybrid
with `fc = 0` has Odontoceti's thresholds (LeanDag/Hybrid/Conservativity.lean);
Mahi-Mahi at `w = 3` is Mysticeti (`DecidedConservative`,
LeanDag/Steelhead/MahiMahiPair/Safety/Statement.lean:152); Steelhead is the
composite of two rules (`compose`, LeanDag/Steelhead/Model/Compose.lean:31).
Optimal-Hydrozoan reuses Hydrozoan's committee
(LeanDag/OptimalHydrozoan/Model/Faults.lean:23).

## II.1 Mysticeti — the reference rule (slides 15–18)

### Slide 15 — Mysticeti

**Text.**
> | | |
> |---|---|
> | Faults | `f` Byzantine, `n ≥ 3f + 1`, quorum `q = n − f` |
> | Round `r` | the leader proposes `L` |
> | Round `r + 1` | a block referencing `L` is a **vote** |
> | Round `r + 2` | a block referencing `q` votes is a **certificate** |
> | Direct commit | `q` certificates at `r + 2` |
> | Direct skip | `q` blocks at `r + 1` reference no candidate |
> | Indirect | a certificate for `L` in the anchor's history; no tie-break |
>
> **+** Commits at round `r + 2` with no certificate messages. `n = 3f + 1`
> validators tolerate `f` Byzantine faults.
> **−** Three rounds per commit; Odontoceti and Hybrid use two.

**Figure.** None beyond the table.

**Notes.**
- `coreAnchored` (LeanDag/Mysticeti/Model/Rule.lean:86–95): `waveAt = 2`,
  `Commit = DirectCommitIn` (`certCommit IsVote q q 2`, :68),
  `Skip = DirectSkipSlotIn` (`blameSkip q`, :83), one rung
  `CertifiedIn` (`certifiedLink IsVote q 2`, :62), `tie = False`.
- `IsVote` (LeanDag/Common/Support.lean:92).
- No tie-break: two certified candidates are equal,
  `eq_of_certificates_nonempty` (LeanDag/Mysticeti/Rule.lean:120).
- (informal) "Three message delays", and the optimality of `3f + 1` for
  Byzantine faults, are background, not Lean statements.

### Slide 16 — Mysticeti: direct commit and direct skip

**Text.**
> `n = 4`, `f = 1`, `q = 3`. Slot 0 is led by `v0`; another slot by `v3`.
> - At round 1, `v0`, `v1`, `v2` vote for `v0`'s block; `v3`'s block does not.
> - At round 2, the blocks of `v0`, `v1`, `v2` each reference those three
>   votes: three certificates. `3 ≥ q`: **commit**.
> - At round 1, `v0`, `v1`, `v2` reference no block of `v3` at round 0:
>   three blames. `3 ≥ q`: `v3`'s slot is **skipped**.

**Figure.** Witness `U3`, stepped:
(1) round 0 and the round-1 votes (blocks 4, 5, 6 reference `{0, 1, 2}`;
block 7 references `{1, 2, 3}`);
(2) the round-2 certificates (blocks 8, 9, 10 reference `{4, 5, 6}`);
(3) the commit badge on slot 0 and the skip badge on `v3`'s slot, with the
three blames dashed.

**Notes.**
- `U3` (LeanDagTest/Mysticeti/Model.lean:112–127); `Certifies U3 8 0`
  (:261); `DirectCommit U3 0 0` (:264); `blames U3 3 1 = {0, 1, 2}` (:258);
  `DirectSkip U3 3 0` (:267).
- A direct commit and a direct skip exclude each other:
  `not_directCommit_of_directSkip` (LeanDag/Mysticeti/Rule.lean:67).

### Slide 17 — Mysticeti: indirect commit

**Text.**
> - At round 2 only `v0`'s block is a certificate for `L`. One certificate is
>   fewer than `q`, and one blame is fewer than `q`: no direct decision.
> - The slot at round 3, led by `v0`, is eligible. It is committed directly by
>   rounds 4 and 5.
> - Its block references `v0`'s certificate, so `L` is **committed
>   indirectly**.

**Figure.** Witness `U7`, stepped:
(1) round 1: votes from `v0`, `v1`, `v2`; `v3`'s block blames;
(2) round 2: block 8 (`v0`) references `{4, 5, 6}` and is the only
certificate; the blocks of `v1`, `v2`, `v3` reference `{5, 6, 7}` and carry 2
votes each;
(3) round 3: anchor block 12 (`v0`, references `{8, 9, 10}`) with its direct
commit from rounds 4–5 shown as a badge;
(4) the path anchor → certificate → `L` highlighted, and the commit badge on
slot 0.

**Notes.**
- `U7` (LeanDagTest/Mysticeti/Model.lean:470–495, 526):
  `certificates U7 0 0 = {8}`, `DirectCommitIn U7 V7 12 3`.
- Why an indirect skip cannot contradict a direct commit: a direct commit puts
  a certificate in the history of every block from round `r + 3`,
  `exists_certificate_reaches_of_directCommit` (LeanDag/Mysticeti/Rule.lean:79);
  `indirect_agrees_with_direct` (:185).

### Slide 18 — Mysticeti: why it is safe

**Text.**
> 1. Two quorums share a correct validator.
> 2. A correct validator votes once per round, so a slot has at most one
>    certified candidate.
> 3. A direct commit puts a certificate in every history from round `r + 3`.
> 4. A direct skip leaves no certificate anywhere.
> 5. So any two views decide every slot the same way, and their ledgers agree.
>
> No step uses the network. Every rule that follows is proved safe by the same
> five steps, with its own counts: these are the laws of slide 10.

**Figure.** The five steps as a diagram: step 1 (quorum intersection) supports
steps 2, 3 and 4, and those three support step 5. Each arrow names what one
step takes from another; steps 3 and 4 also count quorums
(`exists_certificate_reaches_of_directCommit` uses
`card_inter_correct_of_quorum`).

**Notes.**
1. `exists_correct_mem_inter` (LeanDag/Common/Validators.lean:152).
2. `eq_of_certificates_nonempty` (LeanDag/Mysticeti/Rule.lean:120).
3. `exists_certificate_reaches_of_directCommit` (:79); across views,
   `certifiedIn_of_directCommitIn`.
4. `certificates_eq_empty_of_directSkip` (:41), for the per-candidate skip;
   the slot skip implies it by `directSkipIn_of_directSkipSlotIn`.
5. `AnchoredRule.decided_agree` at `coreLaws` (LeanDag/Mysticeti/Rule.lean);
   `MysticetiProperties.agree` (LeanDag/Mysticeti/Properties.lean:483);
   ledgers: `commitSeq_agree`, `ledgerSet_agree`.
- A backlog of undecided slots is cleared by a run of consecutive commits,
  `decided_below_of_committed_run` (LeanDag/Common/Anchored/Bounded.lean:329);
  under pipelining the run has length 3, `pipe_spansEligible`
  (LeanDagTest/Mysticeti/Pipelined.lean:160).

## II.2 Nemo-Nemo — crash faults only (slides 19–20)

### Slide 19 — Nemo-Nemo

**Text.**
> | | Mysticeti | Nemo-Nemo |
> |---|---|---|
> | Faults | `f` Byzantine | `f` crash; no validator equivocates |
> | Committee | `n ≥ 3f + 1` | `n ≥ 2f + 1` |
> | Quorum | `n − f` | majority `⌊n/2⌋ + 1` |
> | Rounds | propose, vote, certify | propose, vote |
> | Direct commit | `q` certificates | a majority of votes |
> | Direct skip | `q` blames | none |
> | Indirect link | a certificate in history | one vote in history |
>
> **+** Two rounds per commit; `n = 2f + 1`; safety holds for any number of
> crashes.
> **−** Crash faults only. A crashed leader's slot waits for an anchor.
> Liveness needs committed leaders in **adjacent** rounds.

**Figure.** None beyond the table.

**Notes.**
- Non-equivocation of every validator: `Nemo.Universe`
  (LeanDag/Nemo/Basic.lean:104). `CrashFaults.card_validators`, `n ≥ 2f + 1`
  (LeanDag/Nemo/Liveness.lean:55, 63), used only by liveness.
- `majority` (Nemo/Basic.lean:32). `nemoAnchored` (LeanDag/Nemo/Decision.lean:49):
  `waveAt = 1`, `Skip = False` (:54), `Nemo.CertifiedIn`
  (LeanDag/Nemo/Rules.lean:42), `tie = False` (:57).
- Safety with no fault hypothesis: `NemoProperties.agree`
  (LeanDag/Nemo/Carrier.lean:84), `NemoProperties.safety`
  (LeanDag/Nemo/Properties.lean:238).
- Adjacent commits: `Nemo.all_decided_below_of_fairRun`
  (Nemo/Properties.lean:186) assumes `FairRunOn T 2`. Round-robin over
  `2f + 1` validators provides it by counting: `Steelhead.roundRobin_fairRun`
  (LeanDag/Steelhead/Helpers/Liveness.lean:44, hypothesis
  `c · (n − |T|) < n`, here `2f < 2f + 1`); on data `nemo_fairRun`
  (LeanDagTest/Nemo/Model.lean:166). Without adjacent live leaders, odd slots
  are never decided: witness `Ush` (slide 20).
- (informal) Why the implementation has no direct skip (its skip quorum is
  the full stake): docstring LeanDag/Nemo/Rules.lean:13–18.

### Slide 20 — Nemo-Nemo: the rules on a crash

**Text.**
> `n = 3`, majority 2. Validator 2 creates blocks in rounds 0 and 1, then
> crashes.
> - Slot 3 (round 3, leader `v0`): `v0` and `v1` vote at round 4. `2 ≥ 2`:
>   **commit**.
> - Slot 2 (round 2, leader `v2`) has no candidate. It has no direct skip; the
>   anchor at slot 4 links nothing for it: **indirect skip**. Slot 3 is not
>   eligible for slot 2.

**Figure.** Two panels.
Left, witness `Unemo`, rounds 0–5, `v2`'s row ending with a cross after
round 1. Stepped: (1) the slot-3 commit; (2) the empty slot 2, the slot-4
anchor and its history, the skip badge.
Right, witness `Ush`: the crashed `v2` leads every odd round, `v0` every even
round. Slots 0, 2, 4 commit; slots 1, 3, 5 stay undecided, each waiting for
the odd slot above it. Caption: "no two live leaders in a row: no odd slot is
ever decided".

**Notes.**
- `Unemo`, `nemoBlk` (LeanDagTest/Nemo/Model.lean:60, 75);
  `nemo_slot0/1/3/4` (:96–109): slots 0, 1, 3, 4 commit directly; slot 3's
  supporters are `{0, 1}`.
- Slot 2 has no candidate (:112); `nemo_slot2` (:120), anchor slot 4
  (block 11).
- `Ush` (LeanDagTest/Nemo/Shadow.lean:32): `sh_slot0/2/4` (:49–55);
  `odd_undecided` (:74), in every view; `sh_not_fairRun` (:92).

## II.3 Odontoceti — two rounds at `n ≥ 5f + 1` (slides 21–23)

### Slide 21 — Odontoceti

**Text.**
> | | Mysticeti | Odontoceti |
> |---|---|---|
> | Committee | `n ≥ 3f + 1` | `n ≥ 5f + 1` |
> | Rounds | propose, vote, certify | propose, vote |
> | Direct commit | `n − f` certificates | `n − f` votes |
> | Direct skip | `n − f` blames | `n − f` blames |
> | Indirect link | a certificate in history | `n − 3f` distinct voters in the anchor's history |
> | Tie-break | none | the least candidate |
>
> **+** One round fewer per commit. Liveness needs two rounds of production
> instead of three.
> **−** Six validators to tolerate one fault, against four. Agreement depends
> on a fixed order of candidates.

**Figure.** None beyond the table.

**Notes.**
- `Faults5.card_validators5` (LeanDag/Odontoceti/Rules.lean:35–38).
- `odontocetiAnchored` (LeanDag/Odontoceti/Decision.lean:111–120):
  `waveAt = 1`, `DirectCommitIn` (:46), `DirectSkipSlotIn` (:117),
  `ThickLink = coneLink (n − 3f)` (Odontoceti/Rules.lean:82), `tie = (<)`
  (:120).
- Two rounds of production: `directCommit_of_leader_mem`
  (LeanDag/Odontoceti/Liveness.lean:59) takes two populated rounds; Mysticeti's
  (LeanDag/Mysticeti/Liveness.lean:165) takes three.
- The direct rules' safety proofs, `not_directSkip_of_directCommit` (:94) and
  `eq_of_directCommit` (:106), use only `n ≥ 3f + 1`; the fifth `f` is used by
  `not_thickLink_of_directSkip` (:128) and `eq_of_directCommit_of_thickLink`
  (:221).

### Slide 22 — Odontoceti: direct and indirect

**Text.**
> `n = 6`, `f = 1`: direct threshold 5, indirect threshold 3. `v0` is Byzantine.
> - Slot 0 (leader `v0`): 5 blames: **direct skip**.
> - Slot 1: 3 votes, 3 blames: no direct decision. The anchor at slot 3 has
>   voters `{1, 2, 3}` in its history, `3 ≥ 3`: **indirect commit**.
> - Slot 2: 2 votes, 4 blames: no direct decision. The anchor at slot 4 links
>   nothing: **indirect skip**.

**Figure.** Witness `Uskip`, rounds 0–5. Stepped: (1) slot 0's direct skip;
(2) slot 1's 3–3 split; (3) the slot-3 anchor's history shaded, the three
voters circled, commit badge; (4) slot 2's 2–4 split and the slot-4 anchor,
skip badge. Slots 3 and 4 carry direct-commit badges.

**Notes.**
- `Uskip` (LeanDagTest/Odontoceti/Model.lean): `uskip_slot0` (:145–153,
  blames `{1, …, 5}`); `supporters Uskip 7 2 = {1, 2, 3}`, anchor block 21,
  `uskip_slot1` (:157–187); slot 2 supporters `{2, 3}`, anchor block 28,
  `uskip_slot2` (:202). Round 5 (block 35) supplies slot 4's direct commit.
- A direct commit is seen with at least `n − 3f` voters by every block from
  round `r + 2`: `thickLink_of_directCommit` (Odontoceti/Rules.lean:209).

### Slide 23 — Odontoceti: two twins pass

**Text.**
> - A Byzantine leader can make two blocks (twins) in one round.
> - Both twins can reach the `n − 3f` threshold inside one anchor's history.
> - If each validator committed any passing twin, two validators could commit
>   different twins.
> - The rule therefore commits the **least** passing candidate, an order
>   every validator computes the same way.

**Figure.** Two panels.
Left, Odontoceti, witness `Utwin6` (`n = 6`): twins 0 and 6 of Byzantine
`v0`, voters `{0, 1, 2}` and `{3, 4, 5}`; both reach 3 inside the history of
block 19 (a round-3 block). Caption: "both twins pass".
Right, the same pattern at a committed anchor, witness `x9` (Hybrid rule,
`n = 9`, `k = 4`): twins 16 and 17, voters `{1, 2, 3, 4}` and `{5, 6, 7, 0}`,
both inside the history of the committed anchor block 27; the least twin
committed, the other refused.

**Notes.**
- `utwin6_both_pass` (LeanDagTest/Odontoceti/Model.lean:250–260). Block 19 is
  not the slot's committed anchor; at the actual anchor (slot 2, block 15)
  only twin 0 passes, and `utwin6_slot0` commits it (:268–273).
- `x9_both_pass` (LeanDagTest/Barnacle/OrcaellaIndirect.lean:249), `x9_slot3`
  (:270), `x9_least` (:288), under the Hybrid rule `orcaella 4` on nine
  validators.
- The tie and its law: `tie`, `link_unique` in `odontocetiLaws`
  (LeanDag/Odontoceti/Decision.lean:161, 173).
- Counting authors, not blocks: `coneSupports` (Odontoceti/Rules.lean:75).
- (informal) That the thesis's argument picks "the" candidate.

## II.4 Hybrid (Orcaella) — Byzantine and crash faults apart (slides 24–26)

### Slide 24 — Hybrid

**Text.**
> - `fb` Byzantine validators and `fc` crash-prone validators. A crash-prone
>   validator never equivocates but may stop.
> - Quorum `q = n − fb − fc`. The rule is Odontoceti's: `q` votes to commit,
>   `q` blames to skip, the least candidate with `k` voters in the anchor's
>   history to link.
> - `k` must satisfy `2fb + fc + 1 ≤ k` and `k + 3fb + 2fc ≤ n`. Such a `k`
>   exists exactly when `n ≥ 5fb + 3fc + 1`.
> - With `fc = 0` the thresholds are Odontoceti's.
>
> **Compared with Odontoceti:** crash-prone validators are counted apart from
> Byzantine ones, which lowers the committee; the link threshold `k` becomes a
> parameter.
> **+** Tolerating one crash requires 4 validators; tolerating one Byzantine
> fault requires 6.
> **−** Crash-prone validators must not equivocate. When the fault sets are
> full, every correct validator is needed for liveness.

**Figure.** A number line for `k` with the admissible interval: `n = 4`,
`fb = 0`, `fc = 1` gives `[2, 2]`; `n = 9`, `fb = 1`, `fc = 1` gives `[4, 4]`.
Beside it a table: `f = 1` Byzantine → `n = 6`; `fc = 1` → `n = 4`;
`fb = fc = 1` → `n = 9`.

**Notes.**
- `HybridFaults` (LeanDag/Hybrid/Faults.lean:20); `HonestNoEquiv` (:104) is a
  hypothesis, enforced by the carrier as a subtype.
- `q` (LeanDag/Hybrid/Rules.lean:37); `Admissible` (:52);
  `exists_admissible_iff` (:77); `hybridAnchored`
  (LeanDag/Hybrid/Decision.lean:127–136).
- `fc = 0`: `q_eq_of_fc_zero`, `kRel_eq_of_fc_zero`,
  `honestNoEquiv_of_fc_zero`, `toHybrid_toFaults`
  (LeanDag/Hybrid/Conservativity.lean). Odontoceti is the case
  `k = n − 3f`.
- Intervals: LeanDagTest/Hybrid/Model.lean:48–50, 138–139.
- `q_le_card_correct` (LeanDag/Hybrid/Liveness.lean:30); `|Correct| = q` on
  `Uhyb4`, `Uhyb9` (Model.lean:58, 140).

### Slide 25 — Hybrid: the rules on four and five validators

**Text.**
> - `fb = 0`, `fc = 1`, `n = 4`, `q = 3`: validator 3 stops after round 0.
>   Each slot led by a live validator receives 3 votes: **direct commit**.
> - `fb = 0`, `fc = 1`, `n = 5`, `q = 4`, `k ∈ {2, 3}`: slot 1 receives 2
>   votes and 3 blames, so no direct decision. Both voters are in the history
>   of the anchor at slot 3. At `k = 2` slot 1 is **committed**; at `k = 3` it is
>   **skipped**.

**Figure.** Two panels. Left: witness `Uhyb4`, a direct commit on 3 votes,
`v3`'s row crossed. Right: witness `U5`, stepped: (1) the 2–3 split of slot 1;
(2) the slot-3 anchor (block 18) and its history; (3) two badges, "k = 2:
commit" and "k = 3: skip".

**Notes.**
- `Uhyb4` (LeanDagTest/Hybrid/Model.lean:36–83), `uhyb4_slot1` (:98). The
  crashed validator's slot is not directly skipped
  (`uhyb4_slot3_not_directSkip`, :116).
- `U5` (LeanDagTest/Barnacle/OrcaellaIndirect.lean): `u5_commit` (:129),
  `u5_skip` (:143). In `U5` nobody crashes; the split is produced by the
  references alone.

### Slide 26 — Hybrid: the committee bound is tight

**Text.**
> With `fb = 1`, `fc = 1` and `n = 8` (one fewer than `5fb + 3fc + 1 = 9`), no
> `k` is admissible. For every `k`, one full view of one DAG derives both a
> commit and a skip for the same slot.

**Figure.** Witnesses `UtightA` and `UtightB` side by side: leader `v1`
(correct) with candidate block 1; Byzantine `v0` with two round-1 blocks
(8 and 9), one of which votes for block 1 (9 in `UtightA`, 8 in `UtightB`);
anchor block 17. `UtightA`: 6 blames against 3 voters in the
anchor's history (for `k ≤ 3`, commit and skip). `UtightB`: 6 votes but only 3
voters in the anchor's history (for `k ≥ 4`, commit and skip).

**Notes.** `hyb8_no_admissible` (LeanDagTest/Hybrid/Tight.lean:58);
`UtightA` (:100), `UtightB` (:147); `LeanDagTest.hybrid_bound_necessary`
(:171). Sufficiency at the bound: `hybridLaws` under `Admissible`
(LeanDag/Hybrid/Decision.lean:171).

## II.5 FinWhale — a fast path that tolerates `p` missing votes (slides 27–30)

### Slide 27 — FinWhale

**Text.**
> - Committee `n = 3f + 2p − 1`, with `1 ≤ p ≤ f`. Safety: up to `f`
>   Byzantine. Fast path: when at most `p` are Byzantine.
> - Three thresholds: slow `2f + p`, block validity `n − f`, fast `n − p`.
> - **Fast commit** at round `r + 1`: `n − p` votes.
> - **Slow commit** at round `r + 2`: `2f + p` blocks, each referencing
>   `2f + p` votes.
> - Validity: if two of a block's references reference two different blocks of
>   `v`, the block may not reference a block of `v` (leader exclusion).
> - `p = 1` gives `n = 3f + 1`; `p = f` gives `n = 5f − 1`.
>
> **Compared with Mysticeti:** a second, faster commit rule at `r + 1`; the
> skip and the indirect rule also read "evidence" (slide 29); a different
> committee; leader exclusion instead of self-parent.
> **+** The parameter `p` sets both the committee size and the number of
> faults the fast path tolerates.
> **−** The committee grows with `p`. Beyond `p` faults only the slow path
> commits. There is no self-parent rule, so inclusion of every block is not
> proved.

**Figure.** A table at `f = 2`: `p = 1 → n = 7`, `p = 2 → n = 9`; and the
three thresholds at `f = p = 2`: slow 6, validity 7, fast 7.

**Notes.**
- `Params` (LeanDag/FinWhale/Model/Params.lean:24: `card_add_one`, `p_pos`,
  `p_le_f`); `spQuorum` (:40); `fastCard` (:45); validity quorum
  `ValidHere.quorum` (LeanDag/FinWhale/Model/Rule.lean:36).
- `FastCommit` (Model/Rule.lean:156); `SPCertificate` (:148); `SPCommit`
  (LeanDag/FinWhale/Model/Decision.lean:40).
- `Clause.leaderExcluded` (LeanDag/Common/BlockRecord.lean:304), used at
  Model/Rule.lean:39. FinWhale's validity has no self-parent clause.
- Safety: `FinWhaleProperties.safety` (LeanDag/FinWhale/Carrier.lean:356).
  Fast path: `fastCommit_of_reactive` with `byzantine.card ≤ p`
  (LeanDag/FinWhale/Reactive.lean:65); `fwFastReliability`
  (Carrier.lean:297). Progress through the slow path: `progress` (:360).
- Thresholds at `f = p = 2`: LeanDagTest/FinWhale/Model.lean:53.
- Theorem 26 (validity) holds under `SelfParented`
  (`theorem26_of_selfParent`, LeanDag/FinWhale/Procedure/Validity.lean:27),
  which DoS-valid DAGs supply (`selfParented_ofDoSValid`,
  LeanDag/FinWhale/DoSBridge.lean:77).

### Slide 28 — FinWhale: fast and slow commit

**Text.**
> `f = 2`, `p = 2`, `n = 9`; validators 0 and 1 are Byzantine.
> - **Fast.** Seven round-1 blocks reference the leader's block: `7 ≥ 7`,
>   commit at round 1.
> - **Slow.** Every round-2 block references 7 votes; six such blocks suffice:
>   `6 ≥ 6` certificates, commit at round 2.

**Figure.** Witness `Dfast`, stepped: (1) the leader block 0 (by Byzantine
`v0`) and the 7 votes; (2) the round-2 blocks, all certificates, 6 of them
counted; (3) both badges.

**Notes.**
- `Dfast` (LeanDagTest/FinWhale/Model.lean:88): `voters = {0, …, 6}`,
  `FastCommit Dfast 0` (:103, 105); every round-2 block has 7 voting parents
  (:115) and is an SP-certificate (:117); `SPCommit` from 6 certificates
  (:120).
- Latency: `fastCommit_latency` (LeanDag/FinWhale/Reactive.lean:98): after
  GST, with a correct leader and at most `p` Byzantine, every correct round-1
  block is built within `Δ + δ + 2·proc` of its author entering round 0;
  `no_timeout_of_fast` (:118). (informal) "Two message delays" is a reading of
  this bound.

### Slide 29 — FinWhale: skip and evidence

**Text.**
> - A round-`r+2` block is **evidence** for `l` when it references at least
>   `f + p − 1` votes for `l`; if its references show the leader equivocating,
>   at least `f + p` for `l` and at most `f + p − 1` for every other candidate.
> - **Direct skip**: `2f + p` blocks at `r + 1` reference no candidate, **and**
>   `2f + p` blocks at `r + 2` are evidence for nothing.
> - **Indirect commit**: the anchor's history holds a slow certificate for
>   `l`, or `2f + p` evidence blocks for `l`. The least such `l` is committed.
> - Evidence is needed because a fast commit may leave no slow certificate.

**Figure.** Two panels.
Left, witness `Dequiv` (`n = 9`): twins 0 and 27 of Byzantine `v0`. Block 18
sees both twins, references 4 votes for 0 and 2 for 27, threshold
`f + p = 4`: evidence for 0. Block 19 sees one twin, threshold 3. Block 20 is
evidence for nothing.
Right, witness `Dbare`, stepped: (1) 7 votes, fast commit; (2) every round-2
block references 5 votes, one short of a slow certificate, but is evidence;
(3) the round-3 anchor (block 30) references seven evidence blocks, at least
`2f + p = 6`: indirect commit.

**Notes.**
- `FPEvidence` (LeanDag/FinWhale/Model/Rule.lean:135), branching on
  `ExposesEquivocationBy` (:122). `DirectSkip`
  (LeanDag/FinWhale/Model/Decision.lean:67); `SPSkip`
  (LeanDag/FinWhale/Model/Skip.lean:42); `NonFPEvidence` (Skip.lean:32).
  `IndirectCommit` (LeanDag/FinWhale/Model/Anchor.lean:32); `chooseLeast`
  (LeanDag/FinWhale/Procedure/Model/Verdict.lean:87),
  `chooseLeast_least` (LeanDag/FinWhale/Procedure/Consistency.lean:67).
  Anchor at least 3 rounds above (Carrier.lean:99).
- `Dequiv` (LeanDagTest/FinWhale/Model.lean:204, 212, 232–246). Not the
  `n = 4` witness of the same name in LeanDagTest/FinWhale/Equivocation.lean.
- A fast commit with no slow certificate: witness `Dbare`
  (LeanDagTest/FinWhale/Model.lean:164–210). `FastCommit Dbare 0` (:193);
  every round-2 block references 5 votes and is no certificate (:197);
  `¬ SPCommit` (:200); every round-2 block is evidence (:203); the round-3
  leader block 30 commits through evidence alone (:207, 209).

### Slide 30 — FinWhale: what the formalisation found

**Text.**
> - The paper's counting argument for Lemma 22 covers only `p = 1`. For
>   `p ≥ 2` (smallest case `n = 9`) the lemma is proved by a pigeonhole
>   argument.
> - In the paper's case C3 of Lemmas 18 and 19 the count has no margin at
>   `p = 1`; the lemmas are proved instead by induction on the time a block
>   is built.
> - The paper's proofs of Lemmas 6 and 7 pass through the slow skip, which
>   does not apply when a validator holds no block of the slot; they are
>   proved through the evidence quorum.
> - The paper's latency claim (Definition 1) is proved, and the evidence count
>   is exactly tight at `n = 3f + 2p − 1` and one short at `n − 1`.

**Figure.** None.

**Notes.**
- `window_margin` (LeanDag/FinWhale/Counting.lean:143): the cyclic window
  works iff `p ≤ 1`. `lemma22` (LeanDag/FinWhale/Rotation.lean:187) holds for
  all `p`, through `three_correct_window` (:143).
- `c3_margin` (Counting.lean:156), `c3_reachable` (:149); `lemma18`,
  `lemma19` (LeanDag/FinWhale/Creation.lean:76, 128).
- `no_directSkip_of_commit_view` (LeanDag/FinWhale/View.lean:216),
  `no_indirectCommit_of_directSkip_view` (:265); witness `Vmiss`
  (LeanDagTest/FinWhale/Equivocation.lean:247–270).
- `fastCommit_latency` (Reactive.lean:98). `equivocating_margin`
  (Counting.lean:130) is arithmetic tightness of the count, not a lower bound
  for every protocol.
- (informal) Which of these the paper states without proof.

## II.6 Hydrozoan — two paths under hybrid faults (slides 31–33)

### Slide 31 — Hydrozoan

**Text.**
> - `f` Byzantine, `c` crashed, a slack `k ≥ 0`: `n ≥ 3f + 2c + k + 1`.
> - Thresholds: `p = ⌊(c + k)/2⌋`, `q = n − f − c`, `qFast = n − p`,
>   `qCert = ⌊(n + f)/2⌋ + 1`, `qSlow = 2f + c + 1`, `qWeak = f + p + 1`.
> - **Fast commit**: `qFast` votes at `r + 1`. **Slow commit**: `qSlow`
>   certificates at `r + 2`, each referencing `qCert` votes.
> - **Skip**: `qFast` blames at `r + 1`.
> - **Indirect, two rungs**: (1) a certificate in the anchor's history;
>   (2) if no candidate has one, the least candidate with `qWeak` votes in the
>   anchor's history.
>
> **Compared with Mysticeti:** crashes counted apart from Byzantine faults; a
> fast commit at `r + 1`; a second indirect rung for slots committed only by
> the fast path.
> **+** Each crash fault adds 2 to the committee bound, against 3 for a
> Byzantine fault. Commits in two rounds when at most `p` are faulty.
> **−** Only the slow path is guaranteed to commit; the fast path is a
> latency result.

**Figure.** The threshold table at `f = c = k = 1`, `n = 7`: `p = 1`, `q = 5`,
`qFast = 6`, `qCert = 5`, `qSlow = 4`, `qWeak = 3`.

**Notes.**
- `Faults.card_replicas` (LeanDag/Hydrozoan/Model/Faults.lean:41); thresholds
  (:53–74). `FastCommit` (LeanDag/Hydrozoan/Model/DirectRules.lean:45),
  `SlowCommit`, `IsCertificate`, `certificates` (:40, 50, 62),
  `SkippedLeader` (:73). `hydrozoanAnchored`
  (LeanDag/Hydrozoan/Model/Decided.lean:28–42). Rung-0-empty premise:
  `Decided.indirectCommit` (LeanDag/Common/Anchored.lean:201).
- Values at `n = 7`: LeanDagTest/Hydrozoan/Model.lean:42–45.
- `FastLatency` (LeanDag/Hydrozoan/DirectLiveness/Proof.lean:28) is outside
  the liveness statement; `CommitLiveness`
  (LeanDag/Hydrozoan/DirectLiveness/Statement.lean:29) is the guarantee.

### Slide 32 — Hydrozoan: why the second rung exists

**Text.**
> `n = 7`; `v0` is Byzantine and equivocates; `v1` has crashed.
> - The leader receives exactly `qFast = 6` votes: **fast commit**.
> - No block is a certificate: each round-2 block references only 4 votes, one
>   fewer than `qCert = 5`.
> - A validator that missed the fast commit consults the anchor. Rung 1 finds
>   no certificate. Rung 2 finds 4 voters, at least `qWeak = 3`: **commit**.

**Figure.** Witness `U4` / view `V4`, stepped: (1) the 6 votes and the fast
commit; (2) round 2, every block one vote short of a certificate; (3) the
anchor (block 24) and its history, rung 1 empty, rung 2 counting 4 voters.

**Notes.**
- `U4`, `V4` (`lk4`, 32 blocks; LeanDagTest/Hydrozoan/DirectSafety.lean):
  `FastCommit U4 2 0`, `certificates U4 2 0 = ∅`,
  `supporters U4 2 1 = {0, 2, 3, 4, 5, 6}`; the anchor reaches 4 voters
  (checked by evaluation; the witness's docstring states the same).
- `WeakLinked` (LeanDag/Hydrozoan/Model/IndirectRules.lean).

### Slide 33 — Hydrozoan: what the formalisation found

**Text.**
> - The six threshold inequalities hold for every slack `k ≥ 0`.
> - One of them must be strengthened to `qFast + q − n − f ≥ qWeak`, so that
>   every eligible anchor sees at least `qWeak` votes of every fast commit.
> - Round-robin by slot is not fair inside the bound: at `n = 5`, `f = 0`,
>   `c = 2`, it need not place three live leaders consecutively. A rotation
>   aligned to waves is fair.

**Figure.** The six inequalities as a checklist, the strengthened one
highlighted as "proved separately".

**Notes.**
- `ThresholdArithmetic.Statement` / `holds`
  (LeanDag/Hydrozoan/ThresholdArithmetic/Statement.lean:61, Proof.lean:13).
  Row 6 of the statement is the weaker `AnchorSeesFast`
  (Statement.lean:56); the strengthened form is
  `n_add_qWeak_add_f_le_qFast_add_q`
  (LeanDag/Hydrozoan/Helpers/SlotAgreement.lean:52).
- (informal) The paper's cap `k ≤ 2f + c − 4` appears only in a docstring
  (LeanDagTest/OptimalHydrozoan/Thresholds.lean:232).
- `fiveCrashy`, `¬ FairRunOn (S := slotRobin) Correct 3`
  (LeanDagTest/Hydrozoan/Grounding.lean:135, 160); `WaveRobinFair`
  (LeanDag/Hydrozoan/Grounding/Statement.lean).
- Properties: `Agree`, `CommitsCandidate`, `SkipsUnsupported`
  (LeanDag/Hydrozoan/Properties/Statement.lean:27, Proof.lean:35),
  `commitsDirect` (Helpers/Commit.lean:298), `quorate`
  (Helpers/Carrier.lean:47); `safety`, `progress` (Properties/Proof.lean:44–49).

## II.7 Optimal-Hydrozoan — one more fault on the fast path (slides 34–35)

### Slide 34 — Optimal-Hydrozoan

**Text.**
> - Hydrozoan's committee, with at least one tolerated fault (`f + c ≥ 1`).
> - The fast path tolerates one more fault: `pOpt = p + 1`,
>   `qFastOpt = n − pOpt`.
> - FinWhale's evidence: a round-`r+2` block is evidence for `L` when it
>   references `tPlain = n − (2f + c + pOpt)` votes for `L`; or, if it saw the
>   leader equivocate, `tEquiv = f + pOpt` votes with every rival below
>   `tEquiv`.
> - **Skip**: `qCert` blames and `qCert` round-`r+2` blocks that are evidence
>   for nothing.
> - **Indirect**: (1) a certificate; (2) `qCert` evidence blocks in the
>   anchor's history. No tie-break.
>
> **Compared with Hydrozoan:** the fast path tolerates one more fault; the
> second rung reads FinWhale's evidence instead of weak votes.
> **+** At `n = 4`, `f = 1`: commits on 3 of 4 votes, where Hydrozoan needs 4.
> A guaranteed skip for slots with no candidate.
> **−** The skip is one round later than Hydrozoan's. Validity needs leader
> exclusion.

**Figure.** At `n = 4`: Hydrozoan `qFast = 4`, Optimal-Hydrozoan
`qFastOpt = 3`, `tPlain = 1`, `tEquiv = 2`.

**Notes.**
- `OptimalFaults` (LeanDag/OptimalHydrozoan/Model/Faults.lean:23–27);
  `pOpt` (:36), `qFastOpt` (:42), `tPlain` (:49), `tEquiv` (:55).
- `IsFastEvidence` (LeanDag/OptimalHydrozoan/Model/DirectRules.lean:55);
  `SkippedLeaderOpt` (:88, decision round :83–90); `optimalAnchored`
  (Model/Decided.lean:29–41, `tie = False`); `EvidenceLinked`
  (Model/IndirectRules.lean:24).
- `fourReplicasOpt` (LeanDagTest/OptimalHydrozoan/Thresholds.lean:55–75).
- `SkipLiveness` (LeanDag/OptimalHydrozoan/DirectLiveness/Statement.lean:54);
  FinWhale's attack on a slot with a candidate: `OA`, ending in
  `¬ SkippedLeaderOpt UA 1`
  (LeanDagTest/OptimalHydrozoan/DirectLiveness.lean:122–162).
- `ValidOpt`, `LeaderExcluded` (LeanDag/OptimalHydrozoan/Model/Universe.lean:25, 91).
- (informal) "Matches Hydrangea's lower bound".

### Slide 35 — Optimal-Hydrozoan: the evidence rung

**Text.**
> `n = 4`. The leader equivocates (copies 4 and 5).
> - Copy 4 receives 3 votes: **fast commit**. No block is a certificate.
> - Each round-`r+2` block sees both copies, references 2 votes for copy 4
>   and 1 for copy 5, and is evidence for copy 4.
> - The anchor's history holds the three evidence blocks: rung 2 **commits**
>   copy 4.

**Figure.** Witness `OE` (22 blocks), stepped: (1) twins and votes;
(2) the three evidence blocks 13, 14, 15; (3) anchor 18 and the commit.

**Notes.** `OE` (`lkE`; LeanDagTest/OptimalHydrozoan/SlotAgreement.lean:127,
162): `supporters UE 4 2 = {0, 1, 3}`, `certificates UE 4 1 = ∅` (:175),
`EvidenceLinked UE 18 4 1` (:181), `oe_slot1_evidence` (:186).

## II.8 Bluestreak — claims in place of certificates (slides 36–39)

### Slide 36 — Bluestreak

**Text.**
> - `n ≥ 3f + 1`, quorum `n − f`.
> - **Sparse DAG**: only leader blocks must reference `n − f` blocks. Other
>   blocks reference their own previous block and, optionally, leader blocks.
> - A round-`r+2` block **claims** `L` by naming it in its payload, or by
>   referencing `n − f` votes for it.
> - **Direct commit**: `n − f` claims for a leader-tagged `L`.
> - **Direct skip**: `n − f` round-`r+1` blocks in view, and for each candidate
>   `n − f` of them that omit it.
> - **Indirect**: a claim for a tagged `L` in the anchor's history.
>
> **Compared with Mysticeti:** most blocks reference two blocks instead of
> `n − f`; a certificate is replaced by a claim, which only names the block.
> **+** Far fewer references per block. Three rounds at `n = 3f + 1`.
> **−** Blocks need not reference a quorum, so chain-quality coverage is not
> shown. Claims require a discipline (slide 39).

**Figure.** Two witnesses side by side: Mysticeti `U3`, rounds 0–2 (each
block 3 references), and Bluestreak `U1`, rounds 0–3 (non-leader blocks with
1–2 references).

**Notes.**
- `roleClause` (LeanDag/Bluestreak/Rule.lean:45); `ValidWrt` with
  self-parent (:79). (informal) "At most two references" is a docstring
  (:77–78).
- `Claims` (:124), `claimers` (:131); `Commit = DirectCommitIn ∧ Tagged`
  (:138, 189); `DirectSkipIn` (:144); `Link = ClaimedIn ∧ Tagged`, one rung,
  no tie (:192–194).
- `Quorate` is not shown for Bluestreak (LeanDag/Bluestreak/Carrier.lean:19–21).

### Slide 37 — Bluestreak: direct and indirect

**Text.**
> `n = 4`, leader of slot `k` is `v(k mod 4)`.
> - Slot 0 has 3 votes but only 2 claims (blocks 8 and 10): not decided
>   directly.
> - Slots 1–3 are committed directly.
> - The anchor, block 15, references block 8, which claims block 0:
>   slot 0 is **committed indirectly**.

**Figure.** Witness `U1` (24 blocks, identifiers `4·round + creator`),
stepped: (1) slot 0's votes (blocks 4, 5, 7); (2) the claims, drawn dotted
(block 8 by payload, leader block 10 by votes); (3) the anchor 15 and its
link.

**Notes.** `U1` (LeanDagTest/Bluestreak/Model.lean:73): `Certified U1 0`
(:84), `claimers U1 0 = {8, 10}` (:85), no direct decision (:87),
`U1_slot1/2/3` (:91–95), `U1_slot0` (:100).

### Slide 38 — Bluestreak: an anchor must be committed

**Text.**
> - A claim names a block; the votes behind it need not be in the claimer's
>   history.
> - A Byzantine block can claim a slot that a quorum skipped.
> - So the indirect rule is safe only at a committed anchor: every committed
>   anchor is certified, backed and leader-tagged. Of the rules here, only
>   Bluestreak requires this field.

**Figure.** Witness `U2`: slot 0 directly skipped; Byzantine block 11 claims
it; the uncertified would-be anchor 15 links that claim.

**Notes.**
- `skip_link` (LeanDag/Common/Anchored.lean:324) has the premise
  `R.Anchor U A`; `bluestreakLaws` (LeanDag/Bluestreak/Safety.lean:183);
  `Anchor = Certified ∧ Backed ∧ Tagged` (LeanDag/Bluestreak/Rule.lean:195),
  proved of committed anchors by `anchor_commit`, `anchor_link`
  (Safety.lean:193–199). Default `Anchor = True` (Anchored.lean:118).
- `U2`: `DirectSkipIn` (LeanDagTest/Bluestreak/Model.lean:164),
  `ClaimedIn U2 15 0` (:167), `¬ Certified U2 15` (:168). `U2` has no
  committed block.

### Slide 39 — Bluestreak: the claim discipline

**Text.**
> - From round 2, a correct block's claim must name a block certified exactly
>   two rounds below.
> - Safety, liveness and every mechanism assume this discipline.
> - Read two rounds deep, the discipline is preserved by garbage collection.

**Figure.** (diagram) A claim with a two-round window drawn beneath it, the certified
block inside the window.

**Notes.**
- `BackedClaim` (LeanDag/Bluestreak/Rule.lean:153), `Disciplined` (:175);
  `bluestreakLaws` under `Invariant := Disciplined`
  (LeanDag/Bluestreak/Safety.lean:162–167); carrier is the `Disciplined`
  subtype (Carrier.lean:35); `ReactiveB.disciplined`
  (LeanDag/Bluestreak/Reactive.lean:126); `disciplined_chop`
  (LeanDag/Bluestreak/Record.lean:50).
- (informal) That the paper's unbounded reading would make garbage collection
  impossible.

## II.9 Mahi-Mahi — asynchronous, at a wave of `w` rounds (slides 40–42)

### Slide 40 — Mahi-Mahi

**Text.**
> - `n ≥ 3f + 1`. A wave of `w` rounds: propose at `r`, vote at `r + w − 2`,
>   certify at `r + w − 1`. At `w = 3` this is Mysticeti.
> - A block **votes** for the least block of the leader's round found in its
>   history (not only among its direct references).
> - A direct skip blames the slot: the blamer has no block of the slot in its
>   history.
> - The leader of a wave is revealed only after the wave, so the adversary
>   cannot direct its message scheduling against it.
>
> **Compared with Mysticeti:** a longer wave, votes found anywhere in the
> history, a skip per slot, and an unpredictable leader.
> **+** Live with no timing assumption about the network.
> **−** More rounds per commit; it needs an unpredictable leader (a common
> coin).

**Figure.** (diagram) A `w = 5` wave: proposal at `r`, propagation at `r+1, r+2`, votes
at `r+3`, certificates at `r+4`, the leader revealed above `r+4`.

**Notes.**
- `votingRound` (LeanDag/MahiMahi/Model/Rules.lean:34), `decisionRoundAt`
  (:40), `Votes` (:55), `Blames` (:63), `DirectSkip` (:110).
- `w = 3` equals Mysticeti: `DecidedConservative`
  (LeanDag/Steelhead/MahiMahiPair/Safety/Statement.lean:152).
- Safety for `w ≥ 2` (`MahiMahiProperties.safety`,
  LeanDag/MahiMahi/Properties.lean:407); liveness for `w ≥ 4` (:315, 392).
- Liveness hypothesis `UnpredictableWithin`
  (LeanDag/MahiMahi/Model/Unpredictable.lean:38). (informal) The coin itself is
  modelled only in the Steelhead arc.

### Slide 41 — Mahi-Mahi: votes and what a wave commits

**Text.**
> - At `w ≥ 4` a history can contain two twins of the leader; a block votes
>   only for the least.
> - At `w ≥ 4`, once a correct quorum produces through the wave, some correct
>   validator's block is directly committed.
> - At `w ≥ 5`, at least `n − f − b` correct validators are **good**: their
>   block would commit if chosen (`b` = number of Byzantine).
> - An adversary that knows the leader in advance can prevent the leader's
>   block from entering the other validators' histories.

**Figure.** Two panels. Left: witness `twin4`, a history with twins 0 and 4;
the vote arrow goes to 0. Right: witness `aim4` (`n = 4`, nobody equivocates):
the scheduler delivers validator 1's round-1 block into no other history;
`good = {0, 2, 3}` at `w = 4`; at `w = 5` every validator is good.

**Notes.**
- `twin4` (LeanDagTest/MahiMahi/Model.lean:151, 159, 162–163).
- `GoodNonempty` (LeanDag/MahiMahi/Counting/Statement.lean:47); `GoodCard`
  (:67, 81): `n − f ≤ |goodAt ∩ Correct| + |byzantine|`; `goodAt`
  (LeanDag/MahiMahi/Model/Good.lean:29).
- `goodAt aim4 4 1 = {0, 2, 3}` (LeanDagTest/MahiMahi/Counting.lean:84);
  `goodAt aim4 5 1 = univ` (:102); `¬ UnpredictableWithin aim4 4 1 5` with a
  fair schedule (LeanDagTest/MahiMahi/Liveness.lean:71, 82).

### Slide 42 — Mahi-Mahi: what the formalisation found

**Text.**
> - The paper counts all `n − f` validators in the common core as good. Twins
>   of Byzantine leaders can split the votes, so the proved count is
>   `n − f − b`.
> - Proved commit probability per wave, at `w ≥ 5`: at least `(n − f − b)/n`,
>   which is always at least `1/3`. At `n = 4`, `f = b = 1`: `1/2`.
> - `2f + 1` leader slots per round guarantee a commit at `w ≥ 5`.
> - Mysticeti skips per candidate; Mahi-Mahi skips per slot.

**Figure.** A bar chart at `n = 4`: the paper's `(2f + 1)/n = 3/4` against the
proved `1/2`; a second pair for large `n`: `2/3` against `1/3`.

**Notes.**
- `GoodCard` as above. `CommitProbability`
  (LeanDag/Steelhead/MahiMahiPair/Coin/Statement.lean:193):
  `(n − f − b)/n ≤ commitProb` and `1/3 ≤ commitProb` at `wa ≥ 5`; at `w = 4`
  only `1/n` (`CommitProbabilityFour`, :205).
- `MultiLeader` (LeanDag/MahiMahi/Counting/Statement.lean:88) proves `2f + 1`
  suffice. (informal) The paper's `f + 1` and `2/3`.
- `DirectSkip` (Rules.lean:106–112); `mahiMahiAnchored`
  (LeanDag/MahiMahi/Model/Decision.lean:60).

## II.10 Async BlueBottle — Odontoceti's rule, asynchronous (slides 43–44)

### Slide 43 — Async BlueBottle

**Text.**
> - `n ≥ 5f + 1`. Propose at `r`; vote and decide at `r + 2`, with votes found
>   in the history as in Mahi-Mahi; no certificates.
> - **Direct commit**: `n − f` votes. **Direct skip**: `n − f` blames.
> - **Indirect**: `n − 3f` voters in the anchor's history; the least passing
>   candidate is committed.
> - The leader is unpredictable, as in Mahi-Mahi.
>
> **Compared with Odontoceti:** the vote round moves from `r + 1` to `r + 2`
> and votes are found anywhere in the history, so that the rule is live with
> an unpredictable leader.
> **+** Live with no timing assumption, three rounds per wave; commit
> probability at least `(n − 3f)/n` per wave.
> **−** Six validators per fault and an unpredictable leader.

**Figure.** (diagram) A three-round wave with each round-`r+2` block's history drawn as
a shaded cone back to round `r`.

**Notes.**
- `card_validators5` (LeanDag/Odontoceti/Rules.lean:35);
  `AsyncBlueBottle.decisionRoundAt` (LeanDag/AsyncBlueBottle/Model/Rules.lean:35),
  `voters` (:44), `DirectCommit` (:69), `DirectSkip` (:76), `coneSupporters`
  (:92), `WeakLink` (:99); `tie = (<)`
  (LeanDag/AsyncBlueBottle/Model/Decision.lean:58).
- `CommitProbability` (LeanDag/Steelhead/BlueBottlePair/Coin/Statement.lean:76).
- `SkipsUnsupported` is not established for this rule.

### Slide 44 — Async BlueBottle: witnesses

**Text.**
> - `n = 6`: the leader's block enters no history but its own. Five blames:
>   **direct skip**. The schedule is fair, but the leader was known in
>   advance.
> - Two twins can both pass the `n − 3f` test at one anchor: the least must
>   be chosen.
> - The paper's procedure skips per candidate, which can skip one twin while
>   the other is committed.

**Figure.** Three small panels: `aim6` (5 dashed blames); `twin6` (both twins
passing at block 19); `hazard6` (one twin committed, the other skipped).

**Notes.**
- `aim6` (LeanDagTest/AsyncBlueBottle/Model.lean:132, 147–154);
  `roundRobin_fair`, `aim6_not_unpredictable`
  (LeanDagTest/AsyncBlueBottle/Liveness.lean:85, 74).
- `twin6_both_pass` (LeanDagTest/AsyncBlueBottle/Twins.lean:109),
  `twin6_slot0` (:124); `hazard6_commit` (:177), `hazard6_skipped_twin`
  (:182).
- A direct commit at exactly the quorum: witness `five6` (Model.lean).
- `GoodCard` at `n − 3f`, every `n ≥ 5f + 1`
  (LeanDag/AsyncBlueBottle/Counting/Statement.lean:69).

## II.11 Steelhead — two rules on one DAG (slides 45–48)

### Slide 45 — Steelhead

**Text.**
> - Each slot has a **kind**: synchronous (a known leader, short wave `ws`) or
>   asynchronous (an unpredictable leader, long wave `wa`).
> - A slot is decided by the rule of its kind, at its own wave; its anchor
>   lies at or above `round + w(kind)`.
> - A **period** `P` sets the kinds: round `r` is asynchronous when
>   `r mod P = 0`. The period is adapted at intervals of `I` rounds.
> - Two instances: Mysticeti with Mahi-Mahi (`n ≥ 3f + 1`, waves 3 and
>   `wa ≥ 4`), and Odontoceti with Async BlueBottle (`n ≥ 5f + 1`, waves 2
>   and 3).
>
> **Compared with Mysticeti:** two rules on one DAG, chosen per slot, and a
> controller that chooses how often the asynchronous rule runs.
> **+** Short waves while the network is synchronous; liveness under
> asynchrony.
> **−** Two rules, a coin, a period controller, and a failover (slide 47).

**Figure.** (illustration of `periodicKind`) A strip of rounds coloured by
kind at `P = 3`, with the two waves drawn as brackets of 3 and 5 rounds.

**Notes.**
- `wavelength` (LeanDag/Steelhead/Model/Wavelength.lean:40); `periodicKind`,
  `IsAsync` (:48, 59); `steelheadAnchored`
  (LeanDag/Steelhead/Model/Decision.lean:48–54, `waveAt = w κ − 1`); `compose`
  (LeanDag/Steelhead/Model/Compose.lean:31); `mahiMahiPair`, `blueBottlePair`
  (LeanDag/Steelhead/Model/Pair.lean:43, 52); `pair_tie` (least, for the
  `5f + 1` pair; LeanDag/Steelhead/Helpers/BlueBottlePair.lean).
- `PeriodAt` (LeanDag/Steelhead/Model/Period.lean); `anchorUpdate`
  (LeanDag/Steelhead/Model/Replay.lean:310) is one update rule; any is allowed.
- Reading the anchor floor at `ws` for every slot is unsafe: `lowFloor`
  (LeanDagTest/Steelhead/Model.lean:170, 188, 194).

### Slide 46 — Steelhead: the stall

**Text.**
> - At any period `P ≥ ws`, an adversary delivers each synchronous leader's
>   block to exactly `f + 1` validators. Neither a commit nor a skip quorum
>   forms.
> - The synchronous slot just below each asynchronous round is then undecided
>   in every view, and the output does not advance beyond it.
> - A committed asynchronous slot does not decide the synchronous slots below
>   it.
> - At period 1 every slot is proved to be decided.

**Figure.** Witness `st20` (`n = 4`): every synchronous candidate with 2 votes;
the asynchronous slot 0 committed directly; slot 3 undecided in every view.

**Notes.**
- `Stall` (LeanDag/Steelhead/MahiMahiPair/Liveness/Statement.lean:611): slots
  at rounds `≡ P − 1 (mod P)` are never decided, under "no synchronous
  certificate and no synchronous direct skip". `AllDecidedBelowAtPeriodOne`
  (:639). Nothing is stated for period 2.
- `st20` (LeanDagTest/Steelhead/Counterexamples/Stall.lean:70, 101–117,
  `st20_slot0` :129, `st20_stall_view` :170).
- `rt_stall` (LeanDagTest/Steelhead/Counterexamples/RotatingStall.lean:270).

### Slide 47 — Steelhead: control and failover

**Text.**
> - The period is changed by a second verdict, read at the asynchronous
>   **control** slots of each interval.
> - **Failover**: when the anchor is more than `I` rounds above the last
>   committed output, the next interval runs at period 1.
> - Under failover a stalled slot is decided almost surely. The probability it
>   is still undecided after `M` blocks, each of `wa·K` coins, is at most
>   `2 · ((n^{wa·K} − (n − f − b)^{wa·K}) / n^{wa·K})^{⌊M/2⌋}`, where `b` is
>   the number of Byzantine validators and `K` bounds the period.

**Figure.** Timeline from witness `Failover`: periods 4, 4, then failover to
1, 1; the stalled slot decided after a run of good coins.

**Notes.**
- `ControlDecided`, `controlRound`, `controlSlots`
  (LeanDag/Steelhead/Model/Chain.lean:79–129); `PeriodAt.anchor`
  (Model/Period.lean:144); `PeriodOne`
  (LeanDag/Steelhead/MahiMahiPair/Period/Statement.lean:277).
- `UndecidedTail` (LeanDag/Steelhead/MahiMahiPair/Coin/Statement.lean:277),
  `badBlockBound` (:265); `K` is the period bound; hypotheses `5 ≤ wa`,
  `K ≤ I`, `wa ≤ I`, `wa·K ≤ q·I`; `DecidedAlmostSurely` (:461).
- `rt_failover`, `rt_recovers` (LeanDagTest/Steelhead/Failover.lean:345, 384).

### Slide 48 — Steelhead: what the formalisation found

**Text.**
> - The paper's period update alone retains a stalled period; liveness
>   requires the failover.
> - An equivocating leader at a slot's anchor floor can hold the slot
>   undecided.
> - The interval must satisfy `I ≥ 2·maxPeriod` and `I ≥ maxPeriod + wa − 2`.
> - In the paper's timeout appendix, with exactly one vote missing, a
>   certificate forms with probability `f/n`, not `(n − f)/n`.

**Figure.** None.

**Notes.**
- `anchorUpdate_half_retains` (LeanDag/Steelhead/Helpers/Replay.lean:821);
  `rt_update_four`, `rt_no_output_above_two` (RotatingStall.lean:287, 302).
- `bf30_slot0_undecided`
  (LeanDagTest/Steelhead/Counterexamples/ByzantineFloor.lean:184).
- `TwoAsyncRounds`, `TwoAsyncRoundsInWindow` (Period/Statement.lean:295, 379);
  `WindowResolves` (:336); `rw44_keeps_two`
  (LeanDagTest/Steelhead/Counterexamples/ReplayShortWindow.lean:98).
- `CertProbEdges` (LeanDag/Steelhead/MahiMahiPair/Timeout/Statement.lean:43).
- (informal) How many findings the paper adopted.

## II.12 Refuted rules (slides 49–53)

### Slide 49 — Minnow: the rule

**Text.**
> - `n ≥ 3f + 1`; no self-parent rule.
> - **Commit** a leader block `l` when `n − f` processes reference it from the
>   round above, and every earlier leader slot is **resolved**: one of its
>   blocks is in `l`'s history, or is concurrent with `l` and committed or
>   skipped.
> - **Skip** when `n − f` processes of the round above have no block that
>   references it.
> - The rule consults no later anchor.

**Figure.** (diagram) A two-round DAG with the "resolved" condition drawn as a check
mark on the previous slot.

**Notes.** `Minnow.ValidHere` (LeanDag/Minnow/Model/Rule.lean:43); `Quorum`
(:119); `Skipped` (:134; the vertex-counting reading `SkippedByVertex`, :145,
lets one vertex be committed and skipped, LeanDagTest/Minnow/Skip.lean:60,
69); `CommittedAt` (:161).

### Slide 50 — Minnow: an earlier leader committed after a later one

**Text.**
> `n = 4`. Process 0 equivocates at round 0: blocks 0 and 4. Block 4 is
> referenced by process 1 only.
> - A validator missing block 5 sees the round-1 leader block 6 reach block 4,
>   which resolves slot 0. Block 6 is **committed**, while slot 0 is still
>   undecided.
> - Block 5 arrives. Block 0 now has a quorum and is **committed** for slot 0,
>   after the later leader.

**Figure.** Witness `Dpart` / `Dfull`, stepped: (1) the twins and their
references; (2) the partial view, block 6 committed; (3) the full view, block
0 committed for the earlier slot.

**Notes.** LeanDagTest/Minnow/Safety.lean: `slotBlocks Dfull (0,0) = {0, 4}`
(:86, 91); `Reaches Dpart 6 4`, `CommittedAt Dpart sfLead 1 6` (:112, 116);
`Dfull` adds blocks 5 and 12 (:96, 126); block 4 is never committed
(`¬ Quorum Dfull 4`, :179); the violated property is Safe-Commit (:134).

### Slide 51 — Minnow: slots that are never decided

**Text.**
> - A leader referenced by 2 of 4 processes is neither committed nor skipped,
>   and no later leader can be committed.
> - With two leaders per round in round-robin, no leader is committed.
> - A silent leader's empty slot prevents every later leader from being
>   committed.
> - With one leader per round, the same DAG does commit.

**Figure.** Two panels: `mLead` (two leaders per round, no commits) and `Ds`
(a silent leader). A third, small: `mFair`, one leader per round, a commit at
slot 2.

**Notes.** LeanDagTest/Minnow/Deadlock.lean: 2 of 4 pointers (:86, 89);
`mLead` (:79, 109–146); `Ds` (:205–223). LeanDagTest/Minnow/Fair.lean:
`CommittedAt Dm mFair 2 11` (:92). `not_committedAt_of_dead`
(LeanDag/Minnow/Blocking.lean:40). (informal) That `2f + 1` is the least safe
skip threshold, so the gap cannot be closed.

### Slide 52 — Black Marlin: the rule

**Text.**
> - `n ≥ 3f + 1`; one anchor per round; no certificates.
> - **Commit** an anchor `B` at round `r` when `n − f` validators reference it
>   at round `r + 1`, and some anchor at `r + 1` references `B` and is itself
>   referenced by `n − f` validators at `r + 2`.
> - There is no skip. Anchors that are not committed are output through a
>   descent from a later committed anchor.

**Figure.** (diagram) Three rounds: anchor `B`, its supporters, the linking anchor and
its supporters.

**Notes.** `Rotation.anchor`, `IsAnchor`, `Supported`, `Linked`, `Committed`
(LeanDag/BlackMarlin/Model/Rules.lean:37, 51, 63, 83, 94); `descend`,
`flushRecord` (LeanDag/BlackMarlin/Model/Descent.lean:85, 100). Black Marlin
has no carrier. (informal) "No reliable broadcast, no coin".

### Slide 53 — Black Marlin: agreement fails

**Text.**
> `n = 4`, `f = 1`. Validator 0 equivocates at round 2: blocks 8 and 12.
> - Block 8 is committed; block 12 is not supported.
> - The committed anchor 19 at round 4 omits block 14.
> - One validator outputs block 8 for round 2; another outputs block 12.
>
> Total order also fails, on blocks 5 and 7 of correct validators.

**Figure.** Witness `Udiv`, stepped: (1) the twins 8 and 12; (2) the commit of
block 8; (3) the committed anchor 19 and its descent to block 12. One
validator outputs block 8 itself; the other reaches block 12 by descent.

**Notes.** LeanDagTest/BlackMarlin/Divergence.lean: `divBlk` (:71), twins
(:57, 115), commit of 8 and non-support of 12 (:120), anchor 19 omits 14
(:124), `Committed Udiv 19 4` (:129), differing outputs (:135, 154, 182);
total order (:261, 298). Sound lemmas: `eq_of_supported`,
`reaches_of_supported`, `reaches_of_committed_of_le`,
`quorum_authorsAt_of_lt` (LeanDag/BlackMarlin/Helpers/Rules.lean:40, 59, 77,
110).

## II.13 The rules side by side (slides 54–56)

### Slide 54 — Every rule on one page

**Text.**
> | Rule | Faults | Committee | Rounds to commit | Indirect rungs | Tie-break | Leader |
> |---|---|---|---|---|---|---|
> | Mysticeti | Byzantine | `n ≥ 3f + 1` | 3 | 1: certificate | none | scheduled |
> | Nemo-Nemo | crash | `n ≥ 2f + 1` | 2 | 1: one vote | none | scheduled |
> | Odontoceti | Byzantine | `n ≥ 5f + 1` | 2 | 1: `n − 3f` voters | least | scheduled |
> | Hybrid | Byz. + crash | `n ≥ 5fb + 3fc + 1` | 2 | 1: `k` voters | least | scheduled |
> | FinWhale | Byzantine | `n = 3f + 2p − 1` | 2 fast / 3 slow | 1: certificate or evidence | least | scheduled |
> | Hydrozoan | Byz. + crash | `n ≥ 3f + 2c + k + 1` | 2 fast / 3 slow | 2 | second rung: least | scheduled |
> | Opt-Hydrozoan | Byz. + crash | same, `f + c ≥ 1` | 2 fast / 3 slow | 2 | none | scheduled |
> | Bluestreak | Byzantine | `n ≥ 3f + 1` | 3 | 1: claim | none | scheduled |
> | Mahi-Mahi | Byzantine | `n ≥ 3f + 1` | `w` (live for `w ≥ 4`) | 1: certificate | none | unpredictable |
> | Async BlueBottle | Byzantine | `n ≥ 5f + 1` | 3 | 1: `n − 3f` voters | least | unpredictable |
> | Steelhead | Byzantine | `3f + 1` / `5f + 1` | by kind: 3 or `wa` / 2 or 3 | 1 | none / least | both |
> | Minnow (refuted) | Byzantine | `n ≥ 3f + 1` | 2 | none | — | scheduled |
> | Black Marlin (refuted) | Byzantine | `n ≥ 3f + 1` | 3 | none | — | one anchor per round |

**Figure.** The table.

**Notes.** Rounds to commit = `waveAt + 1`; for Minnow and Black Marlin, the
rounds their commit rules read (`Quorum`, LeanDag/Minnow/Model/Rule.lean:119;
`Committed`, LeanDag/BlackMarlin/Model/Rules.lean:94). Sources: the rule records cited on
each protocol's slide; FinWhale `LeanDag/FinWhale/Model/Decided.lean:24`;
Hybrid's committee through `Admissible` (`HybridFaults` itself asks
`3(fb + fc) + 1`, LeanDag/Hybrid/Faults.lean:38).

### Slide 55 — What the formalisation found, by rule

**Text.**
> | Rule | Finding |
> |---|---|
> | Odontoceti, Hybrid, Async BlueBottle | two twins can pass the indirect test; the least must be chosen |
> | Mahi-Mahi | the good-validator count is `n − f − b`, not `n − f` |
> | FinWhale | Lemma 22's argument covers only `p = 1`; Lemmas 18/19 and 6/7 need new proofs |
> | Hydrozoan | the slack cap is unnecessary; one inequality must be strengthened |
> | Bluestreak | the indirect rule needs a committed anchor; claims must be read two rounds deep |
> | Steelhead | the stall; the failover is needed for liveness |
> | Minnow | an earlier leader committed after a later one; slots that are never decided |
> | Black Marlin | agreement and total order fail |

**Figure.** The table.

**Notes.** Each row is detailed, with its Lean evidence, on the rule's slides.

### Slide 56 — Three recurring lessons

**Text.**
> 1. **Fix an order.** Wherever two twins can pass a test, the choice between
>    them must be made by an order every validator computes.
> 2. **Count, do not infer from absence.** A skip must count blocks that
>    exist.
> 3. **Use later evidence.** Every rule proved safe here has an indirect rule
>    that reads a later committed anchor; the two refuted rules have none.

**Figure.** None.

**Notes.**
- 1: `tie = (<)` in Odontoceti, Hybrid, FinWhale, Hydrozoan (second rung),
  Async BlueBottle; Mahi-Mahi's `Votes` picks the least block.
- 2: `ugrow_not_directSkip` (LeanDagTest/Mysticeti/Growth.lean:308).
- 3: every carrier has `rungs ≥ 1`; Black Marlin and Minnow have no anchor
  rule. (informal) That the missing rule causes the failures.

---

# Part III — Properties (slides 57–66)

### Slide 57 — From rules to properties

**Text.**
> Mechanisms such as garbage collection or crash recovery should not be
> proved once per rule. Instead:
> - each rule is proved to have a few **properties**;
> - each mechanism is proved once, using only those properties.
>
> Eleven rules (all but Minnow and Black Marlin) have the properties.

**Figure.** The Protocols → Properties → Mechanisms diagram of slide 2, with
the middle column highlighted.

### Slide 58 — The carrier

**Text.**
> A mechanism accesses a rule only through its **carrier**:
> - a type of universes (all blocks) and of views (what one validator holds);
> - the round, creator and references of each block;
> - the decision relation: under schedule `S`, view `V` decides slot `k` as
>   `v`.
>
> Laws: a view holds only universe blocks; a view holds every block that its
> blocks reference; references go one round down.

**Figure.** (diagram) Universe ⊇ View, both projecting into "Block"; an arrow "Decided"
from (schedule, view, slot) to {commit `L`, skip}.

**Notes.** `DagRule` (LeanDag/Properties/Carrier.lean:31); `Decided` is a
relation `Slots → View U → ℕ → Option BlockId → Prop` (:56); `viewSound`
(:45), `viewComplete` (:49), `causal` (:54). Eleven carriers (slide 2).

### Slide 59 — Banded: a verdict reads a finite band of rounds

**Text.**
> Each verdict depends only on the blocks in a band of rounds, from the
> slot's round to some round `top`. Any other universe, view and schedule
> that match in the band — up to a shift of round and slot numbers — reach the
> same verdict.

**Figure.** Witness `Uexcl` and its cut `chop Uexcl 2` (as on slide 76): the
band shaded identically in both; the same verdict, at slot 1 before the cut
and at slot 0 after it.

**Notes.** `Banded` (LeanDag/Properties/Band.lean:227): the other view holds
at least the original view's blocks inside the band; slot rounds, leaders and
kinds match there. Used by `LocalTruncate.of_banded`
(LeanDag/Properties/Derived/Truncate.lean:38), `Persist.of_banded`
(LeanDag/Properties/Derived/FromBand.lean:25), `Stack.safe_and_live`
(LeanDag/Properties/Arcs/Stack.lean:109), `safety`
(LeanDag/Properties/Arcs/Headline.lean:63).

### Slide 60 — Agree, CommitsCandidate, Indirect

**Text.**
> - **Agree**: two views of one universe never decide a slot differently,
>   skips included.
> - **CommitsCandidate**: a committed block is a candidate of its slot.
> - **Indirect**: a committed eligible anchor, with every eligible slot in
>   between skipped, decides the slot; changing the other slots' leaders does
>   not change that verdict.

**Figure.** (diagram) Indirect: an anchor at slot `j`, intermediate slots marked skip,
the other leaders recoloured; slot `i`'s verdict unchanged.

**Notes.** `Agree` (LeanDag/Properties/Agree.lean:22); `CommitsCandidate`
(LeanDag/Properties/Candidate.lean:50); `Indirect`
(LeanDag/Properties/Commit.lean:40). `Indirect` gives `Descends`
(`Descends.of_indirect`, LeanDag/Properties/Derived/Descent.lean:83).

### Slide 61 — The support: the conditions for a commit

**Text.**
> - A **support** names the wave and what it means for a block to certify a
>   candidate.
> - **Law 1 (local)**: certification depends only on the wave's rounds, so it
>   is unchanged by cutting or shifting rounds outside them.
> - **Law 2 (commits)**: if a reliable quorum `T` leads a slot, produces
>   through its wave and certifies every candidate, then a view that holds
>   those rounds commits the slot.
> - Liveness needs exactly this, at every slot `T` leads. The network
>   assumption is used only to establish it.

**Figure.** (diagram) A wave window over rounds `r … r + wave`, `T`'s rows highlighted,
the commit badge. Two arrows into "live": "synchrony and coverage" and
"reactive pacemaker".

**Notes.** `Support` (LeanDag/Properties/Support.lean:39), `Local` (:92),
`Commits` (:103). `Support.live` (LeanDag/Properties/Derived/LeaderCommits.lean:40):
production and certification at the `T`-led slots of a window.
`live_of_coverage` (LeanDag/Timed/Coverage.lean:108);
`coreSupport_live_of_reactiveLive`
(LeanDag/Reactive/MysticetiProperties.lean:59). No synchrony name appears
under `LeanDag/Properties/` (checked by `scripts/check-arc-holes.py`, a
Makefile step).

### Slide 62 — Optional and derived properties

**Text.**
> Optional, needed by one mechanism each:
> - **CommitsDirect**: a direct commit is a verdict (adaptive leader count).
> - **SkipsUnsupported**: a slot is skipped when a large enough set, present
>   one round above, references none of its candidates (prompt skip).
> - **Quorate**: every block references `n − f` distinct creators (chain
>   quality).
> - **SelfParent**, **NoEquiv**: every block references its creator's previous
>   block; a reliable creator makes one block per round (inclusion).
>
> Derived, so no rule needs to prove them: **Persist** and **LocalTruncate** from
> Banded; **LeaderCommits** from Law 2; **Descends** from Indirect.

**Figure.** (diagram) A derivation graph: Banded → Persist, LocalTruncate; Law 2 →
LeaderCommits; Indirect → Descends.

**Notes.**
- `CommitsDirect` (LeanDag/Properties/Optional/Direct.lean:25), used by
  LeanDag/Barnacle/Healthy/Statement.lean:101. `SkipsUnsupported`
  (Optional/Skip.lean:51). `Quorate` (Optional/Quorate.lean:33), for
  non-genesis blocks, `n − slack` with `slack = f` in the core reliability.
  `SelfParent`, `NoEquiv` (Optional/SelfParent.lean:23, 28).
- Derivations: `Persist.of_banded`, `LocalTruncate.of_banded`,
  `Support.leaderCommits` (Derived/LeaderCommits.lean:50),
  `Descends.of_indirect`.
- Some rules also prove them directly: Mysticeti proves `LeaderCommits`
  (`leaderCommits_cert`, LeanDag/Mysticeti/Properties.lean:534) and derives
  Law 2 from it (:634); Steelhead's `persist` (LeanDag/Steelhead/Properties.lean:158).

### Slide 63 — Safety, for every rule and every mechanism

**Text.**
> From **Banded**, **Agree** and **CommitsCandidate**, across any sequence of
> cuts, recoveries and re-geneses:
> - every verdict above the settling round is the same before and after;
> - any view after agrees with any view before, above the settling round;
> - every commit is a candidate, and no block is committed at two slots;
> - adding blocks never changes a verdict.

**Figure.** (illustration) A source DAG, a stack of transformations (fill,
then cut), and the resulting DAG, with "=" between the verdicts above the
settling round.

**Notes.** `Safe` (LeanDag/Properties/Arcs/Headline.lean:46), `safety` (:63),
`Safe.prefix_agree` (:76). The last bullet is the conjunct on `Extends`.

### Slide 64 — Liveness, for every rule

**Text.**
> From **Law 2**, **CommitsCandidate**, **SelfParent** and **NoEquiv**:
> - **Progress**: every slot below a run of reliably led slots is decided, and
>   reliably led slots continue to be committed.
> - **Inclusion**: every block of a reliable validator enters the ledger,
>   through a later slot its creator leads.
>
> Seven rules have both. Nemo, FinWhale, Hydrozoan and Optimal-Hydrozoan lack
> SelfParent and have progress only.

**Figure.** (diagram) A reliable validator's chain of own blocks, pulled into the
ledger when its next leader slot commits.

**Notes.** `Progresses` (Headline.lean:94), `Includes` (:105), `Lives` (:117),
`liveness` (:139); `Progresses` takes `Descends` as a hypothesis. Progress
only: LeanDag/Nemo/Properties.lean:242, LeanDag/FinWhale/Carrier.lean:360,
LeanDag/Hydrozoan/Properties/Proof.lean:47,
LeanDag/OptimalHydrozoan/Carrier.lean:290.

### Slide 65 — Which rule has which property

**Text.**
> All eleven rules have Banded, Agree, CommitsCandidate, Indirect,
> CommitsDirect, and a support with both laws.

**Figure.** The grid (✓ proved, — not shown):

> | Rule | SkipsUnsupported | Quorate | SelfParent | NoEquiv | Safe | Lives |
> |---|---|---|---|---|---|---|
> | Mysticeti | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ |
> | Nemo-Nemo | — | ✓ | — | ✓ | ✓ | progress |
> | Odontoceti | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ |
> | Hybrid | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ |
> | FinWhale | — | ✓ | — | ✓ | ✓ | progress |
> | Hydrozoan | ✓ | ✓ | — | — | ✓ | progress |
> | Opt-Hydrozoan | — | ✓ | — | — | ✓ | progress |
> | Bluestreak | ✓ | — | ✓ | ✓ | ✓ | ✓ |
> | Mahi-Mahi | — | ✓ | ✓ | ✓ | ✓ (`w ≥ 2`) | ✓ |
> | Async BlueBottle | — | ✓ | ✓ | ✓ | ✓ | ✓ |
> | Steelhead | — | ✓ | ✓ | ✓ | ✓ | ✓ |

**Notes.** Locations (all under LeanDag/), in the column order Banded, Agree,
CommitsCandidate, Indirect, Commits, SkipsUnsupported, Quorate, SelfParent,
NoEquiv, Safe, Lives:
- Mysticeti/Properties.lean: 347, 483, 359, 657, 634, 407, 147, 153, 159,
  799, 805.
- Nemo: Properties 98, Carrier 84, Carrier 89, Properties 138,
  Properties 111, —, Carrier 63, —, Carrier 77, Properties 238, 242.
- Odontoceti: Properties 91, Carrier 52, 57, Properties 154, 129, 106,
  Carrier 37, 42, 47, Properties 251, 255.
- Hybrid: Properties 71, Carrier 52, 57, Properties 127, 100, 84, Carrier 35,
  40, 45, Properties 160, 165.
- FinWhale/Carrier.lean: 91, 56, 61, 99, 250, —, 44, —, 50, 356, 360.
- Hydrozoan: Helpers/Banded 210, Helpers/Commit 42, 292, 266, 124,
  Helpers/Skippability 54, Helpers/Carrier 47, —, —, Properties/Proof 44, 47.
- OptimalHydrozoan/Carrier.lean: 83, 61, 66, 267, 139, —, 49, —, —, 286, 290.
- Bluestreak/Carrier.lean: 363, 52, 57, 70, 130, 101, —, 94, 86, 373, 380.
- MahiMahi: Properties 252, Carrier 50, 56, Properties 382, 344, —,
  Carrier 34, 39, 44, Properties 407, 411.
- AsyncBlueBottle: Properties 205, Carrier 47, 54, Properties 296, 262, —,
  Carrier 32, 37, 42, Properties 316, 320.
- Steelhead/Properties.lean: 139, 60, 65, 81, 280, —, 45, 50, 55, 164, 301.
- `CommitsDirect` is proved for all eleven.

### Slide 66 — The properties a user sees

**Text.**
> | Guarantee | Needs |
> |---|---|
> | Validators' ledgers agree | Banded, Agree, CommitsCandidate |
> | Every slot is eventually decided | Law 2, Indirect |
> | A validator decides from the blocks it holds | the pacemaker (slide 71) |
> | A committed block's history contains blocks of many correct validators | Quorate, CommitsCandidate |
> | Every correct validator's blocks are committed | SelfParent, NoEquiv, LeaderCommits |
> | Storage stays linear under equivocation | the novelty budget (slide 75) |
> | Storage stays constant | garbage collection (slide 77) |

**Figure.** The table.

**Notes.** `Safe.prefix_agree`; `Progresses`; `decided_local`
(LeanDag/Mysticeti/ViewPace.lean:507; LeanDag/Reactive/Mysticeti.lean:119;
LeanDag/Bluestreak/Reactive.lean:245); `chain_quality`
(LeanDag/Properties/Arcs/Quality.lean:223, also needs
`2·slack ≤ |correct|`); `dos_resistance` (LeanDag/DoS/Novelty.lean:729);
`card_retained_le` (LeanDag/GC/Window.lean:189). The last two are stated over
the storage model, not the carrier.

---

# Part IV — Mechanisms (slides 67–97)

Each mechanism: the problem; how it works; a worked example; the properties
it uses and provides; its limits.

### Slide 67 — The mechanisms

**Text.**
> | Mechanism | Problem it solves | Uses | Slides |
> |---|---|---|---|
> | Pacing | progress, for a rule that does not refer to time | view convergence | 68–71 |
> | Chain quality | which validators' blocks enter the ledger | Quorate, CommitsCandidate, SelfParent, NoEquiv | 72–73 |
> | Storage bound | storage growth caused by equivocation | the acceptance rule only | 74–75 |
> | Garbage collection | unbounded storage growth | Banded, Agree, Law 1 | 76–79 |
> | Crash recovery | a recovering validator cannot produce blocks | Banded, Agree, SkipsUnsupported, Law 1 | 80–85 |
> | Composition | several mechanisms at once | Banded, Agree, Law 1 | 86–87 |
> | Adaptive schedules | faulty leaders in the schedule; the number of leaders per round | Agree, CommitsDirect, Law 2, Indirect | 88–92 |
> | Checkpoints, Red Snapper | applications beyond ordering | Agree, CommitsCandidate, Law 2 | 93–94 |

**Figure.** The table, with each "Uses" entry linking back to its property
slide in Part III.

**Notes.** Each row is detailed, with its Lean evidence, on the slides listed.
The storage bound is stated over the delivery model (`LeanDag/DoS/`) and reads
no property of the rule.

## IV.1 Pacing (slides 68–71)

### Slide 68 — Liveness, and the role of time

**Text.**
> - The commit rule counts references; it does not refer to time.
> - Liveness is reduced to two facts about the DAG, from some round on:
>   - every reliable validator has a block in each round;
>   - each reliable block references every reliable block of the round below.
> - These follow from view convergence and the pacemaker's rules.
>
> **Uses:** view convergence and the pacemaker's rules (slide 69).
> **Gives:** the support's precondition `live` (slide 61).

**Figure.** (diagram) Layers: network (view convergence) → pacemaker (production and
coverage) → support (`live`) → commits.

**Notes.** `PopulatedOn` (LeanDag/Common/Participation.lean:62),
`SynchronisedOn` (:80). `PaceCore` (LeanDag/Mysticeti/ViewPace.lean:114).
Mysticeti's route: `certifiesAt_of_synchronisedOn`
(LeanDag/Mysticeti/Liveness.lean:95) → direct commit; `Support.live`
(LeanDag/Properties/Derived/LeaderCommits.lean:40).

### Slide 69 — The pacemaker's rules

**Text.**
> - **Advance**: a validator holding blocks of `n − f` creators at round `n`
>   moves past round `n`.
> - **Catch up**: after GST, a validator that holds a reliable block of round
>   `n` enters round `n` within `proc`, the time to process and build a
>   block.
> - **Wait**: a validator spends at least `timeout(n)` in round `n`.
> - **Reference**: a validator's block references every block of the previous
>   round that it holds.

**Figure.** (diagram) One validator's round counter as a state machine with the four
rules on its transitions.

**Notes.** `PaceCore.advances` (LeanDag/Mysticeti/ViewPace.lean:171),
`catchup` (:182), `ViewPace.waits` (:349:
`built v n + timeout n ≤ built v (n+1)`), `references` (:351).

### Slide 70 — Drift collapses in one round

**Text.**
> - Validators' clocks may drift apart before GST.
> - After GST, catching up brings every reliable validator within `Δ + proc`
>   of the others in one round, whatever the spread before.
> - A timeout of `2Δ + proc` therefore suffices; it does not depend on the
>   spread before GST.

**Figure.** Witness `ugrowLag`: round-entry times of four validators against
rounds. The spread is 10 at round 0 and 3 (`= Δ + proc`) from round 1 on.

**Notes.** `PaceCore.drift_collapse` (ViewPace.lean:289), `driftOn_of_catchup`
(:306, 428); `synchronisedOn_of_converges` (:461), `directCommit_of_wait`
(:708), `decided_of_wait` (:721), each with `2·delay + proc ≤ timeout n`.
`ugrowLag` (LeanDagTest/Reactive/Collapse.lean:65: `gst = 12`, `delay = 2`,
`proc = 1`, `timeout = 5`), `ugrowLag_collapse` (:208), `ugrowLag_decided`
(:230, no spread hypothesis). (informal) "Waiting alone does not reduce
drift" has no Lean statement.

### Slide 71 — The reactive schedule, and local liveness

**Text.**
> - A validator waits only until it holds the leader's block, then votes; the
>   timeout is a fallback.
> - The vote round then takes at most drift + delivery + processing. When that
>   sum is below the timeout, no timeout fires.
> - Every reliable validator decides from the blocks it holds, by an explicit
>   time.

**Figure.** Witness `ugrowReactive`: four validators building at spacing 6
inside a timeout of `9 = 2Δ + proc`; one timeline per validator, the timeout
drawn as a dashed bar that is never reached.

**Notes.** `vote_or_wait`, `prompt_vote` (LeanDag/Reactive/Basic.lean:96, 106);
`ReactiveM.cert_or_wait` (LeanDag/Reactive/Mysticeti.lean:31);
`built_succ_le_of_fast` (Basic.lean:166, `D + δ + proc`);
`built_succ_le_of_fast_gst` (:220, `Δ + δ + 2·proc`); `no_timeout_of_fast`
(:194), `no_timeout_of_fast_gst` (:243). `decided_local`
(LeanDag/Mysticeti/ViewPace.lean:507), `commits_recur_local` (:534),
`ReactiveM.decided_local` (Reactive/Mysticeti.lean:119). `ugrowReactive`
(LeanDagTest/Reactive/Model.lean:50). The reactive
schedule does not provide coverage (docstring); inclusion is preserved through the
rotation (LeanDag/Reactive/MysticetiProperties.lean:96).

## IV.2 Chain quality (slides 72–73)

### Slide 72 — Chain quality

**Text.**
> - **Coverage**: the history of every committed block contains, at every
>   round below it, blocks of at least `|Correct| − f` correct validators. No
>   timing assumption is needed.
> - **Inclusion**: a correct validator's block is committed once a later slot
>   it leads commits.
> - Coverage holds for every rule except Bluestreak. Inclusion holds for the
>   seven rules with SelfParent and NoEquiv.
>
> **Uses:** Quorate and CommitsCandidate (coverage); SelfParent, NoEquiv and
> LeaderCommits (inclusion).
> **Gives:** lower bounds on which correct validators' blocks enter the
> ledger.

**Figure.** Witness `Ucens`, slot 1's committed history: at each round the
correct creators counted, 2 of 3.

**Notes.** `card_coveredAt_ge_of_decided`
(LeanDag/Properties/Arcs/Quality.lean:96); `mem_history_of_decided_commit`
(:150); `committed_of_correct_block` (:195); `chain_quality` (:223). Coverage
instances: LeanDagTest/Quality/Generic.lean (Steelhead's is
`steelhead_card_correct_le_two_mul`); its inclusion is in `liveness`
(LeanDag/Steelhead/Properties.lean:301).

### Slide 73 — Coverage does not give inclusion

**Text.**
> Validators 0, 1, 2 reference only each other for six rounds; validator 3 is
> correct and no other validator references it. Each round of the commit has 2 correct
> creators, exactly the bound. None of validator 3's blocks enters the
> committed leader's history.

**Figure.** Witness `Ucens`: validator 3's row with no incoming references,
validator 0 shaded Byzantine.

**Notes.** `Ucens` (LeanDagTest/Quality/Model.lean:312–405): `Correct =
{1, 2, 3}`, `ucens_slot1` (:339), `missingAt Ucens 13 r = {3}` (:345–347),
card `f` (:348), `coveredAt … 13 1 = {1, 2}` (:351), no block of 3 in slot 1's
history (:364), block 7 not in the ledger (:393).

## IV.3 Storage under equivocation (slides 74–75)

### Slide 74 — Equivocation and exposure

**Text.**
> - Safety requires no restriction on equivocation; bounded storage does.
> - A creator is **exposed** in a block's history when the history holds two of
>   its blocks in one round.
> - **Rule**: never reference a block whose creator is exposed in your own
>   history.
> - This alone bounds a history, but with a constant that grows like `f^f`: one
>   history can hold `2^e` chains of one creator.
>
> **Uses:** no property of the rule; only which blocks a validator accepts.
> **Gives:** a bound on what a correct validator stores (next slide).

**Figure.** Witness `Udouble` (`n = 13`, `f = 4`): 4 chains of validator 1 in
one history, with `e = 2` exposed creators.

**Notes.** `ExposedIn` (LeanDag/DoS/Exposure.lean:43); `DoSValid` (:77);
`card_history_le'` (LeanDag/DoS/Pedigree.lean:723:
`|H(b)| ≤ (n + (n − 1)·f^f)·(r + 1)`); `udouble_four_chains`,
`udouble_exposed`, `udouble_dosValid` (LeanDagTest/DoS/Doubling.lean:119, 122,
101). Safety results restated under `DoSValid` without using it:
LeanDagTest/DoS/SafetyUnderDoS.lean.

### Slide 75 — The novelty budget

**Text.**
> - Accept a block only if its history adds at most `τ` blocks you do not
>   hold; reference only blocks you have accepted.
> - The rule is independent of a block's creator.
> - Storage then grows linearly: with `C` correct validators, a correct
>   validator holds at most `C·((1 + fτ)·n + 1 + f)` blocks at round `n`.
>   At `C = 3`, `f = 1`, `τ = 3`, round 9: 114 blocks.

**Figure.** The store bound `12n + 6` at `C = 3`, `f = 1`, `τ = 3`, rounds
0–9, ending at 114. (The exposure-only bound of slide 74 bounds one block's
history, not a store, and is not drawn on the same axes.)

**Notes.** `UniformBudget` (LeanDag/DoS/Novelty.lean:192); `RefsAccepted`
(:452); `dos_resistance` (:729); `dos_resistance_of_pace'`
(LeanDag/Mysticeti/PaceDelivery.lean:165). After a round `R`, a correct
block's novelty is at most `f·κ + 1` (`card_novelty_le_of_byzBudget`,
Novelty.lean:432).

## IV.4 Garbage collection (slides 76–79)

### Slide 76 — The cut

**Text.**
> - Each validator keeps a **horizon** `G` and discards every block below it.
>   Validators do not agree on `G`.
> - Keep the blocks of rounds `≥ G` and renumber round `G` as round 0, with no
>   references. The result is again a valid DAG.
> - Slot `d + k` of the full DAG and slot `k` of the cut DAG have the same
>   verdict.
>
> **Uses:** Banded, Agree, and Law 1 of the support.
> **Gives:** the same verdicts and liveness after the cut, and constant
> storage (next slide).

**Figure.** Witness `Uexcl` cut at `G = 2`, stepped: (1) the DAG of rounds
0–5 with a line at round 2; (2) rounds 2–5 renumbered 0–3, the round-2 blocks
(e.g. block 8) with no references; the commit of block 11 (round 3, now
round 1), at slot 1 before the cut and at slot 0 after it.

**Notes.** `BlockRecord.chop` (LeanDag/Common/Record/Chop.lean:20);
`Slots.chop` (LeanDag/GC/ChopDecided.lean:34); `decided_chop_iff`
(LeanDag/Properties/Arcs/Record.lean:39, premise `G ≤ slotRound d`);
`decided_agree_chop` (:46); `decided_agree_horizons`
(LeanDag/Properties/Arcs/GC.lean:60); `chop_chop` (LeanDag/GC/Horizon.lean:57).
Uses Banded (through LocalTruncate), Agree, and Law 1 (`live_of_truncates`,
LeanDag/Properties/Arcs/Liveness.lean:146). Witness: LeanDagTest/GC/Chop.lean:
`chop Uexcl 2` (:46–49), `DirectCommit Uexcl 11 3` and
`DirectCommit (chop Uexcl 2) 11 1` (:60–61), the decided slot before and
after (:72–84).

### Slide 77 — Storage is constant

**Text.**
> With the horizon at most `Λ` rounds below the current round, a correct
> validator keeps at most `C·(Λ + 1) + C·f + Λ·C·f·κ` blocks, whatever the
> round. Here `κ` bounds the number of new blocks that accepting one
> Byzantine block adds to the store. At `C = 3`, `f = 1`, `κ = 3`, `Λ = 5`: 66 blocks.

**Figure.** (illustration of the bound) A window of width `Λ + 1` sliding
right; the store size flat at 66.

**Notes.** `card_retained_le` (LeanDag/GC/Window.lean:189), under
`ByzBudget D κ`, `RefsAccepted D`, `G ≤ t ≤ G + Λ`. `C` is the number of
correct validators.

### Slide 78 — Joining from an attested base

**Text.**
> - A new validator adopts the round-`G` blocks that are reached from blocks of
>   at least `f + 1` distinct creators at a later round `t`.
> - One of those creators is correct, so every base block is attested by a
>   correct validator. No signatures are needed.
> - It then copies a correct peer's blocks above `G`. Its verdicts equal those
>   of any validator with the full history.

**Figure.** Witness `Uexcl` (`n = 4`): the round-1 layer, attested from
round 4; the base is `{5, 6, 7}`, the joiner's blocks are
`{5, 6, 7, 8, 9, 10}`.

**Notes.** `Base` (LeanDag/GC/AttestedBase.lean:40);
`exists_correct_attester_of_mem_base` (:55); `bootstrap_agree`
(LeanDag/GC/Bootstrap.lean:169, needs `m + 2 ≤ t`); `joinIds` (:100).
Witness: `Base Uexcl 4 1 = {5, 6, 7}`, `joinIds Dexcl 1 2 4 1 =
{5, …, 10}` (LeanDagTest/GC/Bootstrap.lean:150, 153); `Base Utwin 1 0 =
{1, 2, 3}` with both equivocation halves excluded (LeanDagTest/GC/Chop.lean:139).

### Slide 79 — Choosing the lag

**Text.**
> | Horizon | Guarantee |
> |---|---|
> | anywhere | safety |
> | at least 1 round below the current round | every block a peer still requires is retained |
> | at least 2 rounds below the current round | the attested base is complete |
>
> An equivocation whose two blocks both fall below the cut is no longer
> detected.

**Figure.** The table.

**Notes.** Safety: `decided_agree_chop`, `decided_agree_horizons`,
`bootstrap_agree`. One round: `viewUpto_subset_viewUpto_succ`,
`pruned_subset_peer_store` (LeanDag/GC/Horizon.lean:76, 94). Two rounds:
`accepted_mem_base` (LeanDag/GC/Bootstrap.lean:44). Forgotten equivocation:
`¬ ExposedIn (chop Umerge 1) 9 0` (LeanDagTest/GC/Chop.lean:105);
`dosValid_chop` (LeanDag/GC/Chop.lean:110). (informal) A cut above an
undecided slot leaves it undecided.

## IV.5 Crash recovery in one message (slides 80–83)

### Slide 80 — Crash recovery: the message

**Text.**
> - A validator `v₁` crashed after its block `B₁` and returns at round `r`. It
>   cannot create a block: a valid block needs its own previous block one round
>   below.
> - It sends one message: `B₁`, `r`, a donor validator `v₂`, and fresh
>   identifiers.
> - Every receiver computes a **filled** block for `v₁` at each missed round:
>   the donor's references and payload at that round, plus a reference to
>   `v₁`'s previous block.
>
> **Uses:** Banded (through Persist), Agree, SkipsUnsupported, Law 1.
> **Gives:** `v₁` producing again, with every earlier verdict unchanged.

**Figure.** Witness `ucrashMsg 4 4` (on `Ucrash 4`), stepped: (1) `v3`'s row
stops after block 3 at round 0; (2) the filled blocks of `v3`, hatched, each copying the donor
`v1`'s references and adding a self-reference; the round-1 filled block
references `{3, 0, 1, 2}`.

**Notes.** `GapData.hgap` (LeanDag/SafeSkip/Data.lean:49); `SkipData`
(:30–73); `SkipMsg` (LeanDag/SafeSkip/Basic.lean:52); `SkipData.fillBlock`
(Data.lean:159); `Integration.fill_refs_eq`
(LeanDag/Integration/CommonTarget.lean:74). `ucrashMsg`
(LeanDagTest/SafeSkip/Model.lean:124, 178). (informal) "Rebuilding costs one
round trip per missed round".

### Slide 81 — What the fill guarantees

**Text.**
> - The filled DAG is valid, and every old block is unchanged.
> - `v₁` has a block at every missed round, so it can produce again.
> - A slot led by `v₁` in the missed rounds is skipped at once, given a quorum
>   one round above (the **prompt skip**). No later view can commit it.
> - Every verdict reached before the fill agrees with every verdict after it.

**Figure.** The fill of witness `ucrashMsg 4 4` (slide 80) with the four
guarantees as callouts. The schedule of `Ucrash` places no slot led by `v3` in
the gap, so the prompt skip is drawn on slide 85 (witness `Ucr`).

**Notes.** `skipFill`, `skipFill_block_old`, `skipFill_populatedOn`
(LeanDag/SafeSkip/Basic.lean:166, 171, 184). Prompt skip:
`MysticetiProperties.decided_none_fresh` (LeanDag/Mysticeti/Record.lean:188);
generic `Arcs.decided_none_of_novel`, `decided_none_of_novel_agree`
(LeanDag/Properties/Arcs/SafeSkip.lean:32, 87), using SkipsUnsupported, and
for the second, Agree and Banded. Instances: Mysticeti, Odontoceti
(LeanDag/Odontoceti/Record.lean:61), Hybrid (LeanDag/Hybrid/Record.lean:67),
Hydrozoan (LeanDag/Integration/HydrozoanMechanisms.lean:79), Bluestreak
(LeanDag/Bluestreak/Record.lean:314). Verdicts: `decided_fill_of_persist`,
`decided_fill_agree_of_properties` (LeanDag/Mysticeti/Record.lean:150, 159).

### Slide 82 — Jumping rounds

**Text.**
> - A validator's own blocks form a chain, so the donor's whole line is fixed
>   by its top block.
> - The fill depends only on `B₁`, the donor's top block `B₂`, and the fresh
>   identifiers. The message carries only these.
> - A receiver that holds `B₂` holds the donor's whole line. After the one
>   message, `v₁` has a block at every round up to `B₂`'s round, so it can
>   produce at the next.

**Figure.** (diagram) The message `(v₁, B₁, v₂, B₂, fresh)` and the line it denotes.

**Notes.** `line_eq_lineOf` (LeanDag/SafeSkip/Jump.lean:174);
`skipFill_eq_of_core` (:238); `JumpMsg` (:282), `JumpMsg.denote` (:345);
`lineOf_mem_view` (:363); `ucrashJump`, `ucrashJump_denote_eq`
(LeanDagTest/SafeSkip/Model.lean:250). (informal) "Constant size": `fresh` is
an identifier supply.

### Slide 83 — Limits of the fill

**Text.**
> - With a horizon `Λ` rounds below, recovery in one message works for outages
>   of at most `Λ` rounds; for longer ones `B₁` has been discarded.
> - No old block references a filled block, so `v₁` is not covered in the
>   rounds it missed.
> - The storage rule must be re-checked; with a donor line whose blocks all
>   reach `B₁`, and `v₁` not equivocating, it is one reachability check per
>   round.
> - If the donor line is taken from blocks every receiver already holds,
>   nothing else needs to be sent.

**Figure.** (illustration of `outage_bounded_by_lag`) One axis with the
outage and the horizon: `r = 10`, `Λ = 5`, `G = 5`; `B₁` at round 5 kept,
`B₁` at round 4 crossed out.

**Notes.** `outage_bounded_by_lag` (LeanDag/Integration/Retention.lean:174),
`anchor_pruned` (:27). `not_synchronisedOn_skipFill`,
`synchronisedOn_skipFill_of_notMem` (LeanDag/Integration/Coverage.lean:37, 52).
`history_B1_subset_fill`, `dosValid_skipFill_of_covered`
(LeanDag/Integration/Exposure.lean:48, 170). `fill_refs_available`
(LeanDag/Integration/CommonTarget.lean:63; it covers the copied references,
not the self-reference).

## IV.6 Re-genesis and the chain fill (slides 84–85)

### Slide 84 — Re-genesis: recovering after a long outage

**Text.**
> - If all of `v₁`'s blocks are below the horizon, its chain of own blocks
>   cannot be continued.
> - Each validator adds a round-0 block for `v₁`, with no references, to its cut
>   DAG. This needs no exception to the self-parent rule.
> - Procedure: (1) join from the attested base to read; (2) re-genesis to write;
>   (3) one fill message from the genesis block to the current round.
> - While a quorum still produces blocks, at most `f` validators can be in
>   this state at once.
>
> **Uses:** Banded, Agree, Law 1, and the attested base (slide 78).
> **Gives:** a validator back in production after any outage.

**Figure.** Witness `Ucrash 2` (`n = 4`, validator 3 crashed after its
round-0 block), stepped: (1) the cut at round 1 (`Ucut`), validator 3's row
empty; (2) the re-genesis block 999 at round 0 (`Uregen`); (3) the recovery
message `urecover` with donor 1 (blocks 5, 9), filling to round 1.

**Notes.** `no_blocks_of_no_genesis`, `severed_of_pruned_anchor`
(LeanDag/Integration/Retention.lean:44, 65); `BlockRecord.addGenesis`
(LeanDag/Common/Record/Genesis.lean:20); `addGenesis_of_severed`
(LeanDag/Integration/ReGenesis.lean:95); `recoveryMsg`,
`hB1uniq_of_addGenesis`, `rejoin_populated` (ReGenesis.lean);
`card_severed_le` (LeanDag/Integration/Margin.lean:40). Witness:
`Ucut`, `ucut_severed`, `Uregen`, `urecover`
(LeanDagTest/Integration/Model.lean:102–160). The genesis block is
valid only in a DAG cut at `G` or above. (informal) "Derived locally, not
transmitted": `regenesis_converges` proves only that a later cut removes it.

### Slide 85 — The chain fill (Bluestreak)

**Text.**
> - Copying a donor's references would attribute to `v₁` claims it never
>   made.
> - Each filled block references only `v₁`'s previous block and carries no tag
>   and no claim. The message is `(v₁, B₁, r)`; no donor.
> - Verdicts do not change: slot 2 is committed and slot 3 skipped, before and
>   after.
>
> **Uses:** the same properties as the fill, and Bluestreak's claim
> discipline.
> **Gives:** recovery for a rule whose blocks carry claims.

**Figure.** Witness `Ucr`: validator 3 (correct) silent from round 2; filled
blocks 102 → 7 and 103 → 102; validator 0 shaded Byzantine. Slot 3, led by 3,
skipped: blocks 16, 17, 18 at round 4 do not reference 103.

**Notes.** `GapData.chainBlock` (LeanDag/SafeSkip/Data.lean:91); `chainFill`
(LeanDag/Bluestreak/Record.lean:174); `disciplined_chainFill` (:231).
LeanDagTest/Bluestreak/Recovery.lean: `rcFaults` (:28), `rcGap` (:73),
blocks 102, 103 (:93), `Ucr_slot2`, `Ufill_slot2`, `Ucr_slot3`,
`Ufill_slot3`, prompt skip (:134–150). (informal) The motivation in the first
bullet.

## IV.7 Composition (slides 86–87)

### Slide 86 — Every mechanism is one relation

**Text.**
> Each mechanism relates the DAG it reads to the DAG it writes: the same blocks
> from a settling round on, renumbered by `G` rounds, with the same creators
> and payloads, and the same references strictly above the settling round.
> - A cut is such a relation; so are a fill and a re-genesis (with `G = 0`).
> - A sequence of them is again one.
>
> **Uses:** Banded, Agree, Law 1.
> **Gives:** safety and liveness for any combination of cuts, fills and
> re-geneses (next slide).

**Figure.** (illustration of `stack_core`, which settles at
`max (r + 1, G)`) A stack: fill rounds 6–10, then cut at `G = 15`; the
composite settles at round 15.

**Notes.** `RebasedAbove` (LeanDag/Properties/Carrier.lean:68, references
:81); `Truncates` (LeanDag/Properties/Truncate.lean:43); `Sustains`
(LeanDag/Properties/Sustain.lean:89); `Stack`, `Stack.rebased`
(LeanDag/Properties/Arcs/Stack.lean:32, 40); `stack_core`
(LeanDag/Integration/StackRules.lean:42).

### Slide 87 — Safe and live across any stack

**Text.**
> From Banded, Agree and Law 1: across any stack, verdicts above the settling
> round are preserved, views agree, and the liveness precondition is
> preserved.
> The cut, fill and re-genesis are each built once, and serve all eleven
> rules.

**Figure.** A grid rules × mechanisms (cut, fill, re-genesis, prompt skip,
coverage, inclusion), ✓ / —.

**Notes.** `Stack.safe_and_live` (Stack.lean:109). `onRecord` instances for
Nemo, Mysticeti, Odontoceti, Hybrid, FinWhale, Hydrozoan, Optimal-Hydrozoan,
Bluestreak, Mahi-Mahi, Async BlueBottle, Steelhead.

## IV.8 Adaptive leaders (slides 88–90)

### Slide 88 — Leaders chosen from the committed prefix

**Text.**
> - A fixed schedule may continue to name a crashed leader.
> - A **configuration** fixes the leaders of each round and an interval.
> - It decides up to its **anchor** (the first committed slot more than one
>   interval past its start), but outputs only up to its boundary.
> - The next configuration is computed from the anchor's history and the
>   verdicts just output.
>
> **Uses:** Agree (safety); Law 2 and Indirect (liveness).
> **Gives:** a schedule every validator computes the same way.

**Figure.** Witness `segRun`: configuration 0 with boundary at round 1 and
anchor at slot 3 (round 3); verdicts at slots 1, 2, 3 are `5`, skip, `15`;
only `[5]` output; slot 3 decided again by the next configuration.

**Notes.** `Barnacle.Config` (LeanDag/Barnacle/Config.lean:28);
`Run.anchor_commits`, `anchor_least` (LeanDag/Barnacle/Model/Run.lean:90–96);
`Run.rangeLedger` (:139); `Boundary.atThreshold`
(LeanDag/Barnacle/Model/Rule.lean:204). `segRun`
(LeanDagTest/Adaptive/Asynchronous.lean:46–113, 121). (informal) The
crashed-leader motivation.

### Slide 89 — Safe for every anchored score

**Text.**
> - Two validators that start from the same configuration agree on every
>   configuration and every verdict.
> - No timing, fairness or window assumption, and any score, provided the
>   update reads the view only through the anchor's history.
> - For liveness the score must continue to assign reliable validators runs
>   of consecutive slots.

**Figure.** (diagram) Two validators' runs, configurations matching segment
by segment.

**Notes.** `Barnacle.Agreement.holds`
(LeanDag/Barnacle/Agreement/Proof.lean:16; Statement.lean:47–90): hypotheses
`Properties.Agree` and `Anchored R upd`. `Score.rule_anchored`,
`Adaptive.score_safe` (LeanDag/Adaptive/Headline.lean:55);
`Adaptive.score_live` (:102); `headsRun_of_cycle_weighted`
(LeanDag/Barnacle/Helpers/Heads.lean:297).

### Slide 90 — What a score may read

**Text.**
> - A score that reads only the anchor's history is unaffected by crash
>   recovery.
> - Under garbage collection the score must read verdicts relative to the
>   configuration: a score that names an absolute slot number gives different
>   answers before and after a cut.

**Figure.** (diagram) A score's read window drawn above the horizon, with a crossed-out
absolute slot number below it.

**Notes.** `UpdStable` (LeanDag/Adaptive/Helpers/Mechanisms.lean:140),
`Score.stable_of_readsHistory`, `swapScore_stable`; `HorizonStable`
(LeanDag/Adaptive/Helpers/Chop.lean:86), `horizonStable_relabel` (:140);
`commitScore_not_horizonStable` (LeanDagTest/Adaptive/Asynchronous.lean:226).

## IV.9 An adaptive leader count (slides 91–92)

### Slide 91 — The adaptive leader count

**Text.**
> More leaders per round lower latency, but one slow leader delays every
> later slot. At each anchor:
> 1. count the directly committed slots in the anchor's history;
> 2. healthy if `num · expected ≤ den · observed`;
> 3. healthy: one more leader; unhealthy: `2^backoff` fewer, between 1 and
>    `maxLeaders`; the backoff resets when healthy and grows otherwise.
>
> **Uses:** Agree, CommitsCandidate, CommitsDirect (the count reads direct
> commits).
> **Gives:** a leader count every validator computes the same way.

**Figure.** Leader count over five windows (healthy, healthy, unhealthy,
unhealthy, healthy): 1 → 2 → 3 → 2 → 1 → 2, backoff 0, 0, 0, 1, 2, with
`maxLeaders = 4`. Inset: witness `Usun`, the count rising from 1 to 2.

**Notes.** `observed` (LeanDag/Barnacle/Model/Window.lean); `Aimd.rule`,
`Aimd.count` (LeanDag/Barnacle/Aimd/Rule.lean). `expected` is
`C.cum (r + 1 − waveLength) − C.cum (r − interval)`; at uniform width `m` and
`r ≥ interval` it is `(interval − waveLength + 1)·m` (checked by `decide` at
`m = 2`, `interval = 4`, `waveLength = 3`: 4). `Usun`
(LeanDagTest/Barnacle/Agreement.lean:100). The plotted sequence is checked by
`decide` at `bnP` (`maxLeaders = 4`; LeanDagTest/Barnacle/Agreement.lean:263).
(informal) The latency motivation.

### Slide 92 — The leader count: findings

**Text.**
> - Safety holds for any anchored update rule, AIMD included.
> - If the interval is shorter than the wave, the expected count is 0, the test
>   always passes, and the count increases at every anchor.
> - Liveness under several leaders per round is proved for round-robin when
>   `waveLength · slack + 1 ≤ n`.

**Figure.** None.

**Notes.** `Barnacle.Agreement.holds` (as slide 89); `Healthy.Vacuous`
(LeanDag/Barnacle/Healthy/Statement.lean); `Live.runsExist_roundRobin`
(LeanDag/Barnacle/Live/Proof.lean:27). Base-rule witnesses:
LeanDagTest/Barnacle/Rules (Hydrozoan, Mysticeti, Nemo, Odontoceti,
Optimal-Hydrozoan, Orcaella).

## IV.10 Beyond ordering (slides 93–94)

### Slide 93 — Checkpoints

**Text.**
> - Correct online validators sign the checkpoint their deterministic state
>   machine reaches after each commit in their own view, and witness
>   certificates for what they signed.
> - A checkpoint certificate is at least `q` signatures on one proposal; a
>   finality certificate is at least `q` witnesses of one.
> - Two checkpoint certificates at one epoch and height agree.
> - A correctly led slot, with production and certification, is finalised.
> - At an epoch change, the highest validated checkpoint becomes the next
>   epoch's genesis.
>
> **Uses:** Agree, CommitsCandidate, Law 2.
> **Gives:** finalised application state, and its recovery across epochs.

**Figure.** (diagram) Commit → state machine → sign → certificate → witness → finality;
then the epoch boundary and recovery.

**Notes.** `SigningRule.proposes`, `.witnesses`
(LeanDag/Checkpoint/CommitSpec.lean:66); `CheckpointQC`, `FinalityQC`
(LeanDag/Checkpoint/BaseSpec.lean:117, 169); `checkpointQC_eq_of_same_height`
(LeanDag/Checkpoint/SafetyProofs.lean:89); `liveCommitFinalized`
(LeanDag/Checkpoint/CommitProofs.lean:88); `IsSelected`, `EpochTransition`
(LeanDag/Checkpoint/RecoverySpec.lean). Safety is within one epoch
(`checkpointQC_prefix`). Instances: LeanDag/Integration/HybridCheckpoint.lean,
LeanDag/Integration/BarnacleCheckpoint.lean.

### Slide 94 — Red Snapper: a fast path for owned objects

**Text.**
> - Validators state a **stance** on each object version inside their ordinary
>   blocks; certificates for transactions, skips and unlocks are read from the
>   DAG.
> - At `n ≥ 3f + 1`, uncontested transactions are decided from the DAG;
>   conflicts are resolved at a committed anchor.
> - At `n ≥ 5f + 1`, a validator may change its vote on `2f + 1` opposing
>   votes, coordinated by a coin.
> - Among any `n − f` votes one side reaches `2f + 1` exactly when
>   `n ≥ 5f + 1`. The `5f + 1` certificate lemmas themselves need only
>   `n ≥ 3f + 1`.
>
> **Uses:** only the committed anchor sequence of the underlying
> consensus.
> **Gives:** commits of owned-object transactions without waiting for
> consensus, except under conflict.

**Figure.** Two panels, `n = 4`, validator 0 Byzantine. Left, witness
`ULive`: one transaction, ACKed by validators 1, 2, 3, a fast quorum at round
3. Right, witness `UTri`: two conflicting transactions on one object, every
correct block declares `⊥`, an unlock at round 3, and anchor 12 releases the
object, dropping both.

**Notes.** `Faults.card_validators` (LeanDag/RedSnapper/Model/Faults.lean:52);
`Uncontested`, `ConflictResolution` (LeanDag/RedSnapper/);
`Revocation.ExposureAtQuorum` (LeanDag/RedSnapper/Revocation/Statement.lean:115:
`half ≤ (quorum + 1)/2 ↔ 5f + 1 ≤ n`); `FullCertSafety`
(LeanDag/RedSnapper/Five/FullCertSafety/Statement.lean:86, over `Faults`,
under `MoveDiscipline`). Witnesses `ULive`, `UTri`
(LeanDagTest/RedSnapper/Liveness.lean:82, 162).

## IV.11 Close (slides 95–97)

### Slide 95 — Open work

**Text.**
> - Adaptive leaders are proved generically; no rule has its own instance yet,
>   and no score that moves more than one slot per validator is shown live.
> - Barbouni (proposed): change the schedule only at verdicts already decided.
> - Checkpoints: the broadcast algorithm is assumed, not modelled.

**Figure.** None.

**Notes.** Generic adaptive liveness: `liveOfAnchored`
(LeanDag/Barnacle/Model/Anchored.lean:70); `Timed.descent_of_support`
(LeanDag/Timed/Coverage.lean:189), applied at 9 rules. `swapScore` and
`commitScore` are live as permutations (`liveOn_of_permuted`).
`AuthenticatedBroadcast` (LeanDag/Checkpoint/RecoverySpec.lean:29) is an
assumed contract. (informal) Barbouni is in `docs/barbouni.md` only.

### Slide 96 — The development

**Text.**
> - `LeanDag/Common/`: blocks, the decision relation, ledgers.
> - `LeanDag/Mysticeti/`, `LeanDag/Nemo/`, …: one directory per rule.
> - `LeanDag/Properties/`: the properties and the safety and liveness
>   headlines.
> - `LeanDag/GC/`, `SafeSkip/`, `Reactive/`, `DoS/`, `Adaptive/`, `Barnacle/`,
>   `Checkpoint/`, `Integration/`: the mechanisms.
> - `LeanDagTest/`: every witness in this deck.
> - `docs/report.md`: the full written account.

**Figure.** (diagram) The directory tree, with the parts of the deck marked
beside it.

**Notes.** `lake build` checks the library and the witnesses; every headline
theorem's axioms are printed in the test files and are Lean's standard three
(`propext`, `Classical.choice`, `Quot.sound`).

### Slide 97 — Summary

**Text.**
> - One decision relation; eleven rules proved, two refuted.
> - Four properties and a support per rule; every mechanism proved once
>   against them.
> - Safety with no network assumption; liveness from view convergence.

**Figure.** The three-column diagram of slide 2, filled with names.
