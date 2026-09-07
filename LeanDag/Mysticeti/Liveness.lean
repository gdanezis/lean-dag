import LeanDag.Mysticeti.Rule
import LeanDag.Common.Participation
/-!
# Liveness — results needing no new primitives

`liveness.md` §6, results **L0**–**L3**.

L0, L2 and L3 assume neither `Live` nor `Synchronised`, which is why they come
first: L0 is pure DAG structure, L2 and L3 are pure view reasoning. Every
modelling decision is deferred until something is already proved. **L1** is
the first result to need a new primitive.

- **L0** — the DAG is dense below its frontier. Validity alone; nothing here
  even mentions correctness. The content is not that the DAG grows but that
  it **cannot grow tall and thin**.
- **L2** — decisions are monotone in the view. A validator never *revises* a
  decision as its view grows.
- **L3** — commit propagation. L2 at the full view, which §4.2 identifies as
  every correct validator's eventual view.
- **L1** — no stall. The first result needing `Live`, and still needing no
  synchrony.
-/

namespace LeanDag

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {U : BlockUniverse Validator BlockId Payload}
variable {N : ℕ}

omit [DecidableEq BlockId] in
/-- A round with any author at all has a block. The bridge that lets L0's
induction step back down: a cardinality bound on `authorsAt` is turned into
a witness block, which the next step then references from. -/
theorem exists_mem_of_authorsAt_card_pos {n : ℕ} (h : 0 < (authorsAt U n).card) :
    ∃ i ∈ U.ids, (U.block i).round = n := by
  obtain ⟨v, hv⟩ := Finset.card_pos.mp h
  obtain ⟨i, hi, hir, _⟩ := mem_authorsAt.mp hv
  exact ⟨i, hi, hir⟩

omit [DecidableEq BlockId] in
/-- One step of L0: a block at round `n+1` forces a quorum of authors at
round `n`.

Immediate from validity — the block's references carry `2f+1` distinct
creators, and every one of them holds a round-`n` block. -/
theorem card_authorsAt_of_succ {n : ℕ} {i : BlockId}
    (hi : i ∈ U.ids) (hir : (U.block i).round = n + 1) :
    quorumCard Validator ≤ (authorsAt U n).card :=
  le_trans (U.creators_quorum hi (by omega))
    (Finset.card_le_card (creators_refs_subset_authorsAt hi hir))

omit [DecidableEq BlockId] in
/-- **L0 — the DAG is dense below its frontier.** If any block exists at
round `r`, then *every* round `n < r` has at least `2f+1` distinct authors.

Downward induction on the gap `r - n`. The step is where the two lemmas
above meet: the inductive hypothesis gives a quorum of authors one round
higher, that quorum is nonempty so some block sits there, and
`card_authorsAt_of_succ` walks it down one more round.

The induction runs on the gap rather than on `r` itself because the
statement is not about `r`: nothing distinguishes the block's own round, and
generalising over `n` is what lets the step re-enter at `n+1`. -/
theorem card_authorsAt_of_lt {r n : ℕ} (hn : n < r) {i : BlockId}
    (hi : i ∈ U.ids) (hir : (U.block i).round = r) :
    quorumCard Validator ≤ (authorsAt U n).card := by
  obtain ⟨d, rfl⟩ : ∃ d, r = n + 1 + d := ⟨r - n - 1, by omega⟩
  clear hn
  induction d generalizing n i with
  | zero => exact card_authorsAt_of_succ hi hir
  | succ d ih =>
      have h1 : quorumCard Validator ≤ (authorsAt U (n + 1)).card :=
        ih (n := n + 1) (i := i) hi (by omega)
      obtain ⟨j, hj, hjr⟩ := exists_mem_of_authorsAt_card_pos (U := U) (n := n + 1)
        (by have := F.card_validators; omega)
      exact card_authorsAt_of_succ hj hjr

/-! ## L1 — no stall

`liveness.md` §3(a), §4.4, §6. The first result here to need a primitive the
static model lacks.

`Correct` means only *does not equivocate* — a purely negative condition,
satisfied by a validator that crashes at round 0 and never speaks again. That
is deliberate: it is what lets every safety result hold for crashed
validators too. But it makes every liveness statement vacuous without a
positive rule, so `Live` supplies one.

**`Live` is an explicit argument, not a class.** `Faults` is a class because
it is *universal* — every theorem in the development carries it, so hiding it
changes nothing. `Live` is not: L0, L2 and L3 do without it and L1 does not.
When an assumption separates the unconditional results from the conditional
ones, hiding it is exactly backwards. For the same reason it is a structure
of its own rather than extra fields on `Faults`: folding it in would give
every safety theorem a liveness hypothesis it does not use, and `Faults`
cannot mention a `BlockUniverse` anyway, since `BlockUniverse`'s own type
requires `Faults`.
-/

/-! **What L4 actually needs of a round** is `PopulatedOn`
(`Participation.lean`): every validator in `T` has a block there. Local
and finite — no growth, no horizon — which is what keeps the horizon `N`
out of L4 entirely. And a set `T` rather than all of `Correct`: L4
counts to `2f+1` and never higher, so it needs a *quorum* of reliable
validators; demanding all of `Correct` would make the theorem lapse
when a single correct validator misses a single round (`liveness.md`
§8 Q2). -/

/-- The all-of-`Correct` case, which is what L1 produces. -/
abbrev Populated (U : BlockUniverse Validator BlockId Payload) (r : ℕ) : Prop :=
  PopulatedOn U (Correct : Finset Validator) r

/-! ## The delivery layer

`liveness.md` §8 questions 2 and 8. The model as first written could not say
what a validator *held* — only blocks and refs — so two different things had
to be stated on `refs` and hoped to coincide:

- `builds` said a correct validator builds once *any* quorum has round-`r`
  blocks. But a validator cannot act on blocks it has not received; the real
  rule is a **timeout plus a quorum in its own view**.
- `Synchronised` said correct blocks reference correct blocks, welding a
  protocol rule to a network guarantee.

`held` fixes both. Note what it does **not** contain: a clock. The timeout is
what decides how much lands in `held` beyond the `2f+1` minimum, and having no
time model, that is the only trace it can leave. `builds` therefore asks only
that a quorum be *in view*; waiting longer than that shows up as a larger
`held`, which is what `EventuallyDelivers` then demands after `R`. -/

/-- What each validator had in hand, one round at a time — and which of it it
chose to build on.

**Two fields, because delivery and policy are two things.** `held` is what the
network brought; `accepted` is what the validator will reference. Until
equivocation nothing forces them apart, and a structure carrying only `held`,
with `includes` demanding that a correct validator reference *everything* it
held, would be **unsatisfiable** the moment a correct
validator holds both halves of an equivocation: `distinct_creators` forbids
referencing two blocks by one author, so no valid block exists and the
validator cannot build at all. See `dos-equivocation-and-growth.md` §4.

`held` must *not* be deduplicated: `U` is defined as every block some correct validator held
(`liveness.md` §4.2), so pruning at the delivery layer would put the second
half of an equivocation outside the universe altogether. The choice of which
half to accept is left unspecified, exactly as the timeout is — the model says
what was in hand and what was built on, never how either was decided. -/
structure Delivery (U : BlockUniverse Validator BlockId Payload) where
  /-- What `v` held from round `n` when it built its round-`(n+1)` block. -/
  held : Validator → ℕ → Finset BlockId
  /-- Held ids are real blocks of the stated round — what keeps `Delivery`
  meaningful, since without it `held` could be junk and `includes` would
  demand blocks reference it. -/
  held_spec : ∀ v n, ∀ i ∈ held v n, i ∈ U.ids ∧ (U.block i).round = n
  /-- What `v` chose to build on: a subset of what it held. -/
  accepted : Validator → ℕ → Finset BlockId
  /-- You can only accept what arrived. -/
  accepted_sub : ∀ v n, accepted v n ⊆ held v n
  /-- **The acceptance rule**: at most one block per author. Forced by
  `distinct_creators` — a validator holding two blocks by one author must pick
  one, because it cannot reference both. -/
  accepted_inj : ∀ v n, ∀ i ∈ accepted v n, ∀ j ∈ accepted v n,
    (U.block i).creator = (U.block j).creator → i = j
  /-- A correct block is always accepted. It never conflicts with anything —
  its author has only the one block for that round (T1) — so nothing is ever
  given up by taking it, and L7 needs it. -/
  accepts_correct : ∀ v ∈ (Correct : Finset Validator), ∀ n, ∀ a ∈ held v n,
    (U.block a).creator ∈ (Correct : Finset Validator) → a ∈ accepted v n
  /-- **The protocol rule.** A correct validator references everything it
  accepted. Implementable and observable — unlike `Synchronised` itself. -/
  includes : ∀ v ∈ (Correct : Finset Validator), ∀ n, ∀ b ∈ U.ids,
    (U.block b).creator = v → (U.block b).round = n + 1 →
    accepted v n ⊆ (U.block b).refs


omit [DecidableEq BlockId] in
/-- A populated round carries a quorum of authors — the step that feeds a
production induction back into its build rule, and the first consumer
`card_correct` was kept for. -/
theorem card_authorsAt_of_populated {r : ℕ} (h : Populated U r) :
    quorumCard Validator ≤ (authorsAt U r).card := by
  refine le_trans card_correct (Finset.card_le_card ?_)
  intro w hw
  obtain ⟨b, hb, hbc, hbr⟩ := h w hw
  exact mem_authorsAt.mpr ⟨b, hb, hbr, hbc⟩


omit [DecidableEq BlockId] in
/-! **`SynchronisedOn`** (`Participation.lean`) is the post-stabilisation
coverage assumption: from round `R` on, every `T`-authored block
references every `T`-authored block of the round below.

**This does not follow from view convergence.** A block's references are
frozen when it is built: a correct validator waits for `2f+1` round-`n`
blocks, and the arrival of the `2f+1`st says nothing about the rest having
arrived. Views converging later does not retroactively enlarge blocks. So
this is an assumption, not a theorem — see `liveness.md` §4.3, and its
§8 question 8 for how it is meant to be split and derived. -/

/-- The all-of-`Correct` case. -/
abbrev Synchronised (U : BlockUniverse Validator BlockId Payload) (R : ℕ) : Prop :=
  SynchronisedOn U (Correct : Finset Validator) R

/-! ## L7 — `Synchronised`, derived

`liveness.md` §8 question 8. `Synchronised` welds two unlike things into one
object: a protocol rule and a network guarantee. It cannot be derived from
anything the static model has, because the model is blocks and refs — no
time, no delivery, no record of what a validator *held* when it built.
`Synchronised` is stated on `refs` because `refs` is all there is.

Adding that missing layer splits it. **The gain is not logical** — one
assumption becomes two and nothing turns unconditional, since with no time
model the chain must bottom out at delivery. The gain is that each piece is a
single kind of thing: `includes` is implementable and observable, which is
exactly what §3(b) notes `Synchronised` fails to be, and `EventuallyDelivers`
is pure network.

It also puts the timeout story somewhere real. A timeout governs *when you
build*, i.e. what lands in `held`; it has nothing to do with `refs`, which
§4.3 had to discuss next to a definition structurally unable to express it. -/

/-- **The network assumption**: after `R`, correct blocks reach correct
validators in time to be built on. This is eventual DAG synchrony proper —
pure delivery, no protocol content. -/
def EventuallyDelivers (D : Delivery U) (R : ℕ) : Prop :=
  ∀ n, R ≤ n → ∀ v ∈ (Correct : Finset Validator), ∀ a ∈ U.ids,
    (U.block a).round = n → (U.block a).creator ∈ (Correct : Finset Validator) →
    a ∈ D.held v n

/-! ## L2 — decisions are monotone in the view

`liveness.md` §6. If `V ⊆ V'` then every verdict `V` reaches, `V'` reaches
too. Combined with M1 this says a validator **never revises a decision** as
its view grows: the safety results say decisions do not *conflict*, not that
they do not *change*.

**This works only because `CertifiedIn` is universe-level.** The
`indirectSkip` case carries a negative premise — no candidate is certified in
reach of the anchor. Were the indirect check view-relative, that premise
would be *anti*-monotone: growing the view could reveal a certificate and
flip a skip into a commit. C1 defined `CertifiedIn` over `U`, with T6a
showing the view-restricted computation agrees, and that is what keeps the
premise stable under growth. Both indirect cases pass their certificate
premise through untouched below — that is the whole content of the remark.
-/

variable [S : Slots Validator]

/-! **L2 — decisions are monotone in the view** — and **L3, commit
propagation** — are the relation's `decided_mono` and `decided_full` at
`coreLaws`: a validator never revises a decision as its view grows, and
whatever any validator decides on any view holds on the full view, which
is every correct validator's eventual view. -/

/-! ## L3 — commit propagation

`liveness.md` §4.2, §6. Eventual DAG synchrony says anything one correct
validator holds, all eventually hold — so the union of the correct
validators' views *is* `U`, and every correct validator's eventual view is
the **full** view.

That is what turns "all correct validators eventually agree" from an appeal
into a theorem: the informal *eventually* is discharged by the framing, and
what remains is L2 instantiated. It also fixes what `U` means — not every
block anyone ever wrote, but every block some correct validator ever held. A
Byzantine block revealed to nobody is simply not in the universe. -/

/-! **A view caught up to round `N`** is `View.CoversUpto`
(`BlockRecord.lean`): it holds every block of the universe at a round at
or below `N`. Under eventual DAG synchrony (`liveness.md` §4.2) every
correct validator's view, once delivery has caught up that far, and the
hypothesis under which a liveness result holds of a validator's own view
rather than of the full view; `View.coversUpto_full` says the full view
satisfies it at every `N`. -/

/-! ## L4 — a correct leader commits

`liveness.md` §6. The one substantive proof in the liveness plan.

**Two layers of coverage, and nothing else.** Every correct round-`(r+1)`
block references `L`, because `L` is correct-authored and honest-to-honest
coverage applies. Every correct round-`(r+2)` block then references all of
*those*, so its votes for `L` come from every correct validator — a quorum —
and it certifies. Since there are `2f+1` correct validators, the certificates
themselves come from a quorum, which is `DirectCommit`.

**Only correct-to-correct coverage is used.** The argument never asks whether
a Byzantine block was produced or seen. That is what lets `Synchronised` stay
restricted to correct authors on both sides — an unavoidable restriction,
since a Byzantine validator may publish nothing, or publish and withhold
(§4.3).

**No horizon, no growth, no limit universe.** The hypotheses are three local
`Populated` facts. L1 supplies them from `Live U N` when `r + 2 ≤ N`, but L4
does not care where they come from — which is exactly why the horizon
question of §4.4 could be settled without touching this proof. -/

variable {L C : BlockId} {R r : ℕ} {k : ℕ} {T : Finset Validator}

omit S [DecidableEq BlockId] in
/-- **What the two-round rules count** — the targeted half of coverage: every
`T`-authored block one round above `r` references `L`. This is the meet
point of the pacing disciplines (report §11): full coverage implies it
outright (`votesAt_of_synchronisedOn`), and the reactive exit supplies it
directly (`ReactivePace.votes`), so the commit arguments below are stated
against it and proved once. Round-indexed and schedule-free, as L4's
round-level forms are. -/
def VotesAt (U : BlockUniverse Validator BlockId Payload)
    (T : Finset Validator) (r : ℕ) (L : BlockId) : Prop :=
  ∀ v ∈ T, ∀ c ∈ U.ids, (U.block c).creator = v →
    (U.block c).round = r + 1 → L ∈ (U.block c).refs

omit S in
/-- **What the three-round rule counts**: every `T`-authored block at the
decision round certifies `L`. Coverage implies it through the vote layer
(`certifiesAt_of_synchronisedOn`); the reactive certificate wait supplies
it directly (`ReactiveM.certifies`). -/
def CertifiesAt (U : BlockUniverse Validator BlockId Payload)
    (T : Finset Validator) (r : ℕ) (L : BlockId) : Prop :=
  ∀ v ∈ T, ∀ c ∈ U.ids, (U.block c).creator = v →
    (U.block c).round = r + 2 → Certifies U c L

omit S [DecidableEq BlockId] in
/-- Coverage gives the votes: the instantiation of `SynchronisedOn` at
`n = r`, with `L` the one block singled out. -/
theorem votesAt_of_synchronisedOn (hs : SynchronisedOn U T R) (hRr : R ≤ r)
    (hL : L ∈ U.ids) (hLr : (U.block L).round = r)
    (hLc : (U.block L).creator ∈ T) :
    VotesAt U T r L :=
  fun _v hv c hc hcc hcr => hs r hRr c hc hcr (hcc ▸ hv) L hL hLr hLc

omit S in
/-- A correct round-`(r+2)` block certifies any correct round-`r` block, once
round `r+1` is populated and synchrony has taken hold.

This is both layers at once: `q` references `L` by coverage at `n = r`, and
`C` references `q` by coverage at `n = r+1`. -/
theorem certifies_of_synchronisedOn (hcard : quorumCard Validator ≤ T.card)
    (hs : SynchronisedOn U T R) (hRr : R ≤ r)
    (hpop1 : PopulatedOn U T (r + 1))
    (hL : L ∈ U.ids) (hLr : (U.block L).round = r) (hLc : (U.block L).creator ∈ T)
    (hC : C ∈ U.ids) (hCr : (U.block C).round = r + 2)
    (hCc : (U.block C).creator ∈ T) :
    Certifies U C L := by
  refine le_trans hcard (Finset.card_le_card ?_)
  intro v hv
  obtain ⟨q, hq, hqc, hqr⟩ := hpop1 v hv
  have hqcorrect : (U.block q).creator ∈ T := by rw [hqc]; exact hv
  rw [mem_creatorsOf]
  refine ⟨q, ?_, hqc⟩
  simp only [votesIn, carriedVotes, Finset.mem_filter]
  exact ⟨hs (r + 1) (by omega) C hC (by omega) hCc q hq hqr hqcorrect,
         hs r hRr q hq hqr hqcorrect L hL hLr hLc⟩

omit S in
/-- Coverage gives the certificates, through the vote layer: the
`CertifiesAt` form of the lemma above. -/
theorem certifiesAt_of_synchronisedOn
    (hcard : quorumCard Validator ≤ T.card)
    (hs : SynchronisedOn U T R) (hRr : R ≤ r)
    (hpop1 : PopulatedOn U T (r + 1))
    (hL : L ∈ U.ids) (hLr : (U.block L).round = r)
    (hLc : (U.block L).creator ∈ T) :
    CertifiesAt U T r L :=
  fun _v hv C hC hCc hCr =>
    certifies_of_synchronisedOn hcard hs hRr hpop1 hL hLr hLc hC hCr (hCc ▸ hv)

omit S in
/-- **The commit argument, stated once.** A quorum-sized `T` whose
decision-round blocks all certify `L` directly commits it: each `v ∈ T`
has a round-`(r+2)` block by production, it certifies by hypothesis, and
`T`'s cardinality does the counting. Both pacing disciplines end here —
the full-timeout one arriving through `certifiesAt_of_synchronisedOn`,
the reactive one through `ReactiveM.certifies`. -/
theorem directCommit_of_certifiesAt
    (hcard : quorumCard Validator ≤ T.card)
    (hpop2 : PopulatedOn U T (r + 2))
    (hc : CertifiesAt U T r L) :
    DirectCommit U L r := by
  refine le_trans hcard (Finset.card_le_card ?_)
  intro v hv
  obtain ⟨C, hC, hCc, hCr⟩ := hpop2 v hv
  rw [mem_creatorsOf]
  exact ⟨C, mem_certificatesAt.mpr ⟨hC, hCr, hc v hv C hC hCc hCr⟩, hCc⟩

omit S in
/-- **L4, at the round level.** A correct block at round `r` is directly
committed, given coverage from `r` and correct blocks at `r+1` and `r+2`.

Stated without `Slots`: nothing in the argument cares that `L` is a leader
block, only that it is correct-authored — the same separation Stage A makes
for M1–M3. The proof is the composition through the targeted interface:
coverage supplies `CertifiesAt`, and the shared counting theorem does the
rest. -/
theorem directCommit_of_synchronisedOn (hcard : quorumCard Validator ≤ T.card)
    (hs : SynchronisedOn U T R) (hRr : R ≤ r)
    (hpop1 : PopulatedOn U T (r + 1)) (hpop2 : PopulatedOn U T (r + 2))
    (hL : L ∈ U.ids) (hLr : (U.block L).round = r) (hLc : (U.block L).creator ∈ T) :
    DirectCommit U L r :=
  directCommit_of_certifiesAt hcard hpop2
    (certifiesAt_of_synchronisedOn hcard hs hRr hpop1 hL hLr hLc)

omit [DecidableEq BlockId] in
/-- A correct leader has a candidate block, once its round is populated.
`Populated` at the leader's own round is needed for nothing else. -/
theorem exists_isLeaderBlock (hpop : PopulatedOn U T (S.slotRound k))
    (hlead : S.leader k ∈ T) :
    ∃ L, IsLeaderBlock U k L := by
  obtain ⟨L, hL, hLc, hLr⟩ := hpop (S.leader k) hlead
  exact ⟨L, hL, hLr, hLc⟩

/-- **L4.** A slot with a correct leader, whose three rounds are populated and
which sits after synchrony, is directly committed. -/
theorem directCommit_of_leader_mem (hcard : quorumCard Validator ≤ T.card)
    (hs : SynchronisedOn U T R) (hR : R ≤ S.slotRound k)
    (hpop0 : PopulatedOn U T (S.slotRound k))
    (hpop1 : PopulatedOn U T (S.slotRound k + 1))
    (hpop2 : PopulatedOn U T (S.slotRound k + 2))
    (hlead : S.leader k ∈ T) :
    ∃ L, IsLeaderBlock U k L ∧ DirectCommit U L (S.slotRound k) := by
  obtain ⟨L, hL, hLr, hLc⟩ := exists_isLeaderBlock hpop0 hlead
  exact ⟨L, ⟨hL, hLr, hLc⟩,
    directCommit_of_synchronisedOn hcard hs hR hpop1 hpop2 hL hLr
      (by rw [hLc]; exact hlead)⟩

/-- **L4 at `T := Correct`.** The original statement, recovered. -/
theorem directCommit_of_correct_leader (hs : Synchronised U R)
    (hR : R ≤ S.slotRound k)
    (hpop0 : Populated U (S.slotRound k))
    (hpop1 : Populated U (S.slotRound k + 1))
    (hpop2 : Populated U (S.slotRound k + 2))
    (hlead : S.leader k ∈ (Correct : Finset Validator)) :
    ∃ L, IsLeaderBlock U k L ∧ DirectCommit U L (S.slotRound k) :=
  directCommit_of_leader_mem card_correct hs hR hpop0 hpop1 hpop2 hlead

/-! ### From `DirectCommit` to an actual decision

L4 concludes the universe-level rule; the ledger is defined over `Decided`.
The full view closes the gap, since it holds every certificate there is. -/

omit S in
/-- A universe-level direct commit is one the full view also sees. -/
theorem directCommitIn_full (h : DirectCommit U L r) :
    DirectCommitIn U (View.full U) L r :=
  (HoldsAtLeast.full fun _ hC => (mem_certificatesAt.mp hC).1).mpr h

omit S in
/-- A view caught up to the certificate round sees every certificate, so
a direct commit in the universe is a direct commit in the view. -/
theorem directCommitIn_of_coversUpto {V : View Validator BlockId Payload U}
    (h : DirectCommit U L r) (hcov : V.CoversUpto (r + 2)) :
    DirectCommitIn U V L r :=
  HoldsAtLeast.of_coversUpto
    (fun C hC => ⟨(mem_certificatesAt.mp hC).1, (mem_certificatesAt.mp hC).2.1.le⟩) hcov h

omit S in
/-- **The commit argument at the view level.** `directCommit_of_certifiesAt`
counts `T`'s decision-round blocks in the universe; this counts the same
blocks in a view that holds them. The coverage asked for is `T`'s blocks
at one round, not the whole layer — which is what lets a rate-limited
validator commit, since a limiter may drop what an equivocator produced
but not what a correct quorum did (`Properties/Deliver.lean`). -/
theorem directCommitIn_of_certifiesAt {V : View Validator BlockId Payload U}
    (hcard : quorumCard Validator ≤ T.card)
    (hpop2 : PopulatedOn U T (r + 2))
    (hcov : ∀ b ∈ U.ids, (U.block b).creator ∈ T →
      (U.block b).round = r + 2 → b ∈ V.ids)
    (hc : CertifiesAt U T r L) :
    DirectCommitIn U V L r := by
  refine le_trans hcard (Finset.card_le_card ?_)
  intro v hv
  obtain ⟨C, hC, hCc, hCr⟩ := hpop2 v hv
  exact mem_heldAuthors.mpr ⟨C, mem_certificatesAt.mpr ⟨hC, hCr, hc v hv C hC hCc hCr⟩,
    hcov C hC (by rw [hCc]; exact hv) hCr, hCc⟩

/-- **L4, as a decision.** What L6 consumes and L3 propagates. -/
theorem decided_of_leader_mem (hcard : quorumCard Validator ≤ T.card)
    (hs : SynchronisedOn U T R) (hR : R ≤ S.slotRound k)
    (hpop0 : PopulatedOn U T (S.slotRound k))
    (hpop1 : PopulatedOn U T (S.slotRound k + 1))
    (hpop2 : PopulatedOn U T (S.slotRound k + 2))
    (hlead : S.leader k ∈ T) :
    ∃ L, IsLeaderBlock U k L ∧ Decided U (View.full U) k (some L) := by
  obtain ⟨L, hLb, hdc⟩ :=
    directCommit_of_leader_mem hcard hs hR hpop0 hpop1 hpop2 hlead
  exact ⟨L, hLb, Decided.directCommit hLb (directCommitIn_full hdc)⟩

/-- **L4, against a horizon.** The form every capstone uses: production is
available as a single hypothesis up to a horizon, and the three rounds L4
needs are read off it.

Stated separately because the capstones of report §§6–10 all reach L4 the same
way — read production off at `slotRound k`, `+1` and `+2` — and doing that
inline obscures which hypothesis is actually being consumed.

**Production is asked for over `T`, not over `Correct`.** The rule consumes
only `T`-authored blocks, so requiring a block from every correct validator
would be asking for more than is used; `PopulatedOn.mono` bridges the two for
callers holding the stronger `Populated`. The weaker hypothesis is what lets
the recurrence results run at a `T` that is a *proper* subset of `Correct` —
correct validators outside `T` may be starved, partitioned or silent, and the
ledger still commits, provided `T` itself is a quorum.

The subset hypothesis is now unused: with production asked over `T`, L4 needs
nothing but the cardinality of `T`, which is what `commits_recur_on`'s comment
already observed. It is kept in the signature because every capstone has it to
hand and threading it documents the setting. -/
theorem decided_of_leader_of_populated (_hT : T ⊆ (Correct : Finset Validator))
    (hcard : quorumCard Validator ≤ T.card)
    (hs : SynchronisedOn U T R) (hR : R ≤ S.slotRound k)
    (hpop : ∀ r, R ≤ r → r ≤ N → PopulatedOn U T r) (hN : S.slotRound k + 2 ≤ N)
    (hlead : S.leader k ∈ T) :
    ∃ L, IsLeaderBlock U k L ∧ Decided U (View.full U) k (some L) :=
  decided_of_leader_mem hcard hs hR
    (hpop _ (by omega) (by omega)) (hpop _ (by omega) (by omega))
    (hpop _ (by omega) (by omega)) hlead

/-- The same at `T := Correct`. -/
theorem decided_of_correct_leader (hs : Synchronised U R)
    (hR : R ≤ S.slotRound k)
    (hpop0 : Populated U (S.slotRound k))
    (hpop1 : Populated U (S.slotRound k + 1))
    (hpop2 : Populated U (S.slotRound k + 2))
    (hlead : S.leader k ∈ (Correct : Finset Validator)) :
    ∃ L, IsLeaderBlock U k L ∧ Decided U (View.full U) k (some L) :=
  decided_of_leader_mem card_correct hs hR hpop0 hpop1 hpop2 hlead

/-! ## L5 — an absent leader is skipped

`liveness.md` §6.

`Decided.directSkip` asks for a quorum of voting-round blocks referencing
no candidate of the slot. When the leader published nothing every
voting-round block qualifies, so the premise reduces to a quorum being
*present* at that round — which is the hypothesis below, and which a
validator can check against its own view.

**The count cannot be dropped.** A premise quantified over the candidates
the universe holds would be discharged vacuously here, and a validator
holding nothing at all would settle the slot; a leader block arriving
afterwards would then let another validator commit it, and the two
verdicts would stand in different universes, where no uniqueness theorem
compares them. What a validator can observe is that a quorum voted and
none of them saw a candidate, and that is what the rule asks for. -/

/-- A populated round, seen by a view that covers it, supplies the count
the skip rule asks for. -/
theorem quorate_of_populatedOn {V : View Validator BlockId Payload U}
    {T : Finset Validator} {r : ℕ} (hcard : quorumCard Validator ≤ T.card)
    (hpop : PopulatedOn U T r) (hcov : V.CoversUpto r) :
    quorumCard Validator ≤ (creatorsOf U.block (blocksAt U r ∩ V.ids)).card := by
  refine le_trans hcard (Finset.card_le_card ?_)
  intro t ht
  obtain ⟨b, hb, hbc, hbr⟩ := hpop t ht
  refine mem_creatorsOf.mpr ⟨b, ?_, hbc⟩
  exact Finset.mem_inter.mpr ⟨mem_blocksAt.mpr ⟨hb, hbr⟩, hcov b hb (le_of_eq hbr)⟩

/-- L5, in the form the `Decided` constructor wants. -/
theorem decided_none_of_no_candidate {V : View Validator BlockId Payload U}
    (h : ∀ L, ¬ IsLeaderBlock U k L)
    (hq : quorumCard Validator ≤
      (creatorsOf U.block (blocksAt U (S.slotRound k + 1) ∩ V.ids)).card) :
    Decided U V k none :=
  Decided.directSkip (directSkipSlotIn_of_no_candidate h hq)

/-- **L5 — an absent leader is skipped.** If the slot-`k` leader has no block
at its round, every view holding a quorum at the voting round decides
`none`. -/
theorem decided_none_of_leader_absent {V : View Validator BlockId Payload U}
    (h : ∀ b ∈ U.ids, (U.block b).round = S.slotRound k →
      (U.block b).creator ≠ S.leader k)
    (hq : quorumCard Validator ≤
      (creatorsOf U.block (blocksAt U (S.slotRound k + 1) ∩ V.ids)).card) :
    Decided U V k none :=
  decided_none_of_no_candidate (fun _ hL => h _ hL.1 hL.2.1 hL.2.2) hq

/-- **A slot every sufficiently grown synchronous execution commits.**

The conclusion the recurrence results share. Naming it keeps their
quantifier order visible — the slot is fixed by the schedule alone,
before any execution is named — and keeps production and coverage as the
two separate hypotheses they are, rather than bundling them.

**Both hypotheses are relative to the same `T`.** They were not: production
was asked over all of `Correct` while coverage was asked over `T`, which is
strictly more than anything downstream consumes — `decided_of_leader_of_populated`
discarded the excess immediately. Asking both over `T` makes this a statement
about *any* quorum-sized set of reliable validators: the correct validators
outside `T` may be permanently starved and the slot still commits. That is not
a vacuous generality — `reliable_set_is_forced_pace` (V12) exhibits a DAG in
which coverage over a proper subset of `Correct` holds and coverage over
`Correct` fails. It is a genuine weakening only below full fault load, since
`|byzantine| = f` forces `T = Correct` (`reliable_eq_correct`).

**Production is asked for only from `R` on.** The rule reads it off at three
rounds, all of them at or above `R`, so rounds below the synchrony round were
never consumed. Dropping them matters because that is exactly the range a
structure carrying the *build rule* rather than a total block function can
supply. With the hypothesis cut to the range that is used, P8 in its
conditional form reaches liveness — `ViewPace.commits_recur_via_pace`. -/
def CommitsAt (BlockId : Type*) [DecidableEq BlockId] (Payload : Type*)
    [S : Slots Validator] (T : Finset Validator) (R k : ℕ) : Prop :=
  ∀ (U : BlockUniverse Validator BlockId Payload) (N : ℕ),
    (∀ r, R ≤ r → r ≤ N → PopulatedOn U T r) → SynchronisedOn U T R →
    S.slotRound k + 2 ≤ N →
    ∃ L, IsLeaderBlock U k L ∧ Decided U (View.full U) k (some L)

/-! ## L6 — commits recur

`liveness.md` §6. The statement's **quantifier order is its whole content**.

The tempting form — *given `Live U N`, for every `k` there is a committing
`k' ≥ k` with `slotRound k' + 2 ≤ N`* — is **not provable**. Fairness promises
a correct leader *somewhere* beyond `k`, and that slot may lie past the
horizon, with nothing to let you ask for a nearer one. Fixing `U` and `N`
first therefore caps how far fairness may reach.

Stated as below the problem disappears, because `k'` depends only on the
**schedule**: `FairSchedule` and `slotRound` are properties of the `Slots`
instance, not of any DAG. The slot is named first and the DAG grows to it
second — which is also the correct reading of *"the ledger grows without
bound"*: not that one DAG commits infinitely often (no `Finset` can), but
that no slot is the last one a DAG can be grown far enough to commit. -/

/-- The schedule names a correct leader arbitrarily far out. Without it no
recurrence statement holds: `Slots.leader` is an arbitrary function and could
name Byzantine validators forever, however synchronous the network. -/
def FairScheduleOn (T : Finset Validator) : Prop :=
  ∀ k, ∃ k', k ≤ k' ∧ S.leader k' ∈ T

/-- The all-of-`Correct` case. -/
abbrev FairSchedule : Prop := FairScheduleOn (Correct : Finset Validator)

/-- **Every member of `T` leads arbitrarily far out** — per-validator
fairness, strictly stronger than `FairScheduleOn`, which promises only
*some* `T`-leader. Round-robin supplies it (`rrSlots_fairToEach`), and
the rotation-inclusion result of report §11.5 is what consumes it: a
straggler's block enters the ledger when its *own author* leads, so the
schedule must return to that author in particular. -/
def FairToEach (T : Finset Validator) : Prop :=
  ∀ v ∈ T, ∀ k, ∃ k', k ≤ k' ∧ S.leader k' = v

/-- Per-validator fairness is fairness. -/
theorem FairToEach.fairScheduleOn {T : Finset Validator}
    (h : FairToEach T) (hne : T.Nonempty) : FairScheduleOn T := by
  obtain ⟨v, hv⟩ := hne
  intro k
  obtain ⟨k', hk, hlead⟩ := h v hv k
  exact ⟨k', hk, hlead ▸ hv⟩

/-- **The schedule puts `c` consecutive `T`-led slots arbitrarily far out.**

Stronger than `FairScheduleOn`, which promises one `T`-led slot and no more, and
it is what P7′ needs: `decided_below_of_committed_run` is fed a *run* of commits,
and L4 turns a run of `T`-led slots into one.

Round-robin over `3f+1` satisfies it with `c = 3` for every `f ≥ 1`, whatever the
`f` Byzantine validators are and wherever they sit in the rotation. The `f` of
them cut the cycle into at most `f` arcs holding `2f+1` correct slots between
them, so some arc has at least `⌈(2f+1)/f⌉ = 3` — the ceiling being `3` for all
`f ≥ 1` since `(2f+1)/f = 2 + 1/f`. Three is exactly what pipelining asks for,
which is a pleasant coincidence rather than a designed one.

Like `FairScheduleOn` this is an assumption about the schedule, not a theorem:
`Slots.leader` is arbitrary and could name Byzantine validators for ever. -/
def FairRunOn (T : Finset Validator) (c : ℕ) : Prop :=
  ∀ k, ∃ k', k ≤ k' ∧ ∀ i, i < c → S.leader (k' + i) ∈ T

omit [Fintype Validator] [DecidableEq Validator] F in
/-- A run of `c` slots contains a `T`-led slot, so `FairRunOn` refines
`FairScheduleOn` and everything proved from the latter still applies. -/
theorem FairRunOn.fairScheduleOn {c : ℕ} (hc : 0 < c) (h : FairRunOn T c) :
    FairScheduleOn T := by
  intro k
  obtain ⟨k', hk', hrun⟩ := h k
  exact ⟨k', hk', by simpa using hrun 0 hc⟩

/-! A run of `c` slots spanning eligibility — every slot below the run
having its last slot as an eligible anchor — is the relation's
`SpansEligible` at the core. It holds with `c = 1` under three-round
spacing and with `c = 3` under pipelining: one commit against three
consecutive, the entire cost pipelining imposes on this property. -/

omit [Fintype Validator] [DecidableEq Validator] F in
/-- Some slot sits at or beyond any given round.

Under the old three-round spacing this was a theorem — slot rounds grew at
least as fast as `3k`. A merely monotone schedule may not grow at all, so it
is now the class field `unbounded`; this is only that field, in the shape L6
wants. L6 genuinely needs it: fairness must be applied at a slot already past
`R`, and nothing else says such a slot exists. -/
theorem exists_slotRound_ge (n : ℕ) : ∃ k, n ≤ S.slotRound k := S.unbounded n

variable (Validator) in
/-- The least slot proposed at or after round `n`.

A three-round-spaced schedule needs no such thing: `3 * k ≤ slotRound k` made slot `n`
itself sit past round `n`, so `n` could be used as its own slot index. That
coincidence is gone — under multiple leaders slot `n` may still be far below
round `n` — so the slot has to be named. -/
def slotAt (n : ℕ) : ℕ := Nat.find (S.unbounded n)

omit [Fintype Validator] [DecidableEq Validator] F in
/-- `slotAt n` names a slot at or past round `n` — the defining property of the index. -/
theorem le_slotRound_slotAt (n : ℕ) : n ≤ S.slotRound (slotAt Validator n) :=
  Nat.find_spec (S.unbounded n)

omit [Fintype Validator] [DecidableEq Validator] F in
/-- Round `0` is served by slot `0`. -/
@[simp]
theorem slotAt_zero : slotAt Validator 0 = 0 := by
  rw [slotAt, Nat.find_eq_zero]
  omega

omit [Fintype Validator] [DecidableEq Validator] F in
/-! **Every slot has an eligible anchor somewhere** — the relation's
`exists_eligible`, from `unbounded`: the restriction to slots past `k`'s
decision round would be worthless if no such slot existed. -/

/-- **L6 — commits recur.** For every slot `k` there is a later slot `k'`
that **every** sufficiently grown synchronous DAG commits.

Note the conclusion quantifies over `U` and `N` *inside* the existential: the
slot is fixed by the schedule alone, and any DAG grown past it commits it. -/
theorem commits_recur_on (hT : T ⊆ (Correct : Finset Validator))
    (hcard : quorumCard Validator ≤ T.card) (fair : FairScheduleOn T) (R : ℕ) (k : ℕ) :
    ∃ k', k ≤ k' ∧ R ≤ S.slotRound k' ∧
      CommitsAt BlockId Payload T R k' := by
  -- Some slot `k₀` already sits past round `R` (`unbounded`), and every slot
  -- from `k₀` on sits at least as late (`mono`). That is all this needs; the
  -- old proof got the same from `3 * k ≤ slotRound k`, which a pipelined or
  -- multi-leader schedule does not satisfy.
  obtain ⟨k₀, hk₀⟩ := S.unbounded R
  obtain ⟨k', hk', hlead⟩ := fair (max k k₀)
  have hRk' : R ≤ S.slotRound k' :=
    le_trans hk₀ (S.mono (le_trans (le_max_right k k₀) hk'))
  refine ⟨k', le_trans (le_max_left _ _) hk', hRk', ?_⟩
  intro U N hpop hs hN
  -- L1 populates all of `Correct`; `T` is a subset, so `.mono` bridges them.
  -- This is the one place `T ⊆ Correct` is genuinely needed: L4 alone cares
  -- only about `T.card`, but its population has to come from somewhere, and
  -- the only source is L1, which knows about correct validators.
  exact decided_of_leader_of_populated hT hcard hs hRk' hpop (by omega) hlead

/-- **L6 at `T := Correct`.** The original statement, recovered. -/
theorem commits_recur (fair : FairSchedule (Validator := Validator)) (R : ℕ) (k : ℕ) :
    ∃ k', k ≤ k' ∧ R ≤ S.slotRound k' ∧
      CommitsAt BlockId Payload (Correct : Finset Validator) R k' :=
  commits_recur_on Finset.Subset.rfl card_correct fair R k

/-! ## L8 — no undecided slot below a commit

L6 says commits recur. It does **not** say every slot is decided, and the
difference is what the ledger sees: `commitSeq` reads verdicts off in slot
order, so a single permanently undecided slot withholds delivery of everything
above it however many commits recur beyond. The Mysticeti paper calls this
backpressure and keeps it deliberately (§III-C).

The theorem below says the backpressure clears, under one hypothesis:
`helig`, that *every* later slot is an eligible anchor. That hypothesis is
exactly the old three-round spacing (`eligible_of_lt_of_spacing`), and
pipelining does destroy it — under `slotRound k = k` the two slots below any
anchor lie inside its decision round and cannot use it.

**But the conclusion survives pipelining**, and it is worth being precise about
why, because the tempting inference is wrong. It does *not* follow from "slot
`j - 1` cannot anchor on `j`" that `j - 1` must reach the next commit: nothing
strictly between `j - 1` and `j + 2` is *eligible*, so anchoring on `j + 2`
leaves the intermediate premise **vacuous**, and `j + 2` is ordinarily committed
too. `decided_of_first_eligible_commit` below is that argument, and it needs no
induction at all.

So `helig` is a convenience — it buys the nearest-anchor induction cheaply —
rather than the boundary of what is provable. The conclusion fails only when
commits are *isolated*, with no three consecutive: then `j - 1` really must
reach the next committed `j'`, whose own lower neighbour must reach past `j'`,
without end, and since `Decided` derivations are finite trees no derivation
exists. That configuration needs an adversarial *leader schedule* — Byzantine
leaders holding essentially three of every four consecutive slots — and fair
round-robin excludes it, correct validators holding runs of `2f+1 ≥ 3`
consecutive slots each of which commits directly after `R` by L4. L9 below is
the machine-checked form of the isolated-commit obstruction. -/

/-- **The escape.** If `j` is committed and *nothing strictly between `k` and
`j` is eligible to anchor `k`*, then `k` is decided outright: the
intermediate-skip premise is vacuous, so there is no induction and no appeal to
nearestness.

This is the fact that keeps pipelining live, and the one most easily
overlooked. Slot `j - 1` sitting immediately below a committed `j`
cannot anchor on `j` — one round on, inside its decision round — but it *can*
anchor on `j + 2`, and neither `j` nor `j + 1` is eligible for it, so the
premise is empty and the slot resolves at once. Under fair leader election
`j + 2` is committed whenever `j` is, correct validators holding runs of
`2f+1 ≥ 3` consecutive slots.

No hypothesis on the schedule, and none on synchrony: like L8 this is pure
decision-relation combinatorics. -/
theorem decided_of_first_eligible_commit {V : View Validator BlockId Payload U}
    {k j : ℕ} {A : BlockId}
    (helig : (coreAnchored Validator BlockId Payload).Eligible k j)
    (hfirst : ∀ i, k < i → i < j → ¬ (coreAnchored Validator BlockId Payload).Eligible k i)
    (hj : Decided U V j (some A)) :
    ∃ v, Decided U V k v := by
  classical
  have hmid : ∀ i, k < i → i < j → (coreAnchored Validator BlockId Payload).Eligible k i →
      Decided U V i none :=
    fun i h1 h2 h3 => absurd h3 (hfirst i h1 h2)
  by_cases hc : ∃ L, IsLeaderBlock U k L ∧ CertifiedIn U A L (S.slotRound k)
  · obtain ⟨L, hL, hcert⟩ := hc
    exact ⟨some L, AnchoredRule.Decided.indirectCommit_single rfl (fun _ _ h => h)
      (AnchoredRule.lt_of_eligible _ helig) helig hj hmid hL hcert⟩
  · push Not at hc
    exact ⟨none, AnchoredRule.Decided.indirectSkip_single rfl
      (AnchoredRule.lt_of_eligible _ helig) helig hj hmid
      (fun L hL ⟨C, hC, hre⟩ => hc L hL C hC hre)⟩

open Classical in
/-- **L8.** Given a committed slot, every slot below it is decided — provided
every later slot may anchor an earlier one.

No synchrony, no timing, no fairness: this is pure decision-relation
combinatorics, which is why it is worth isolating. The work is choosing the
*nearest* committed slot above `i` and reading the intermediate premise off the
induction hypothesis — an intermediate slot is decided by induction, and cannot
be decided `some` without contradicting nearestness, so it is decided `none`.

Note the proof never consults the direct rules. It does not need to: where the
direct rule commits, M2 puts the certificate in reach of the anchor, so the
indirect branch taken here agrees with it — and M6 guarantees as much in any
case. -/
theorem decided_of_committed_above
    (helig : ∀ a b : ℕ, a < b → (coreAnchored Validator BlockId Payload).Eligible a b)
    {V : View Validator BlockId Payload U} {n : ℕ} {A : BlockId}
    (hn : Decided U V n (some A)) :
    ∀ i, i ≤ n → ∃ v, Decided U V i v := by
  classical
  have key : ∀ d i, i ≤ n → n - i ≤ d → ∃ v, Decided U V i v := by
    intro d
    induction d with
    | zero =>
      intro i hi hd
      exact ⟨some A, (by omega : i = n) ▸ hn⟩
    | succ d ih =>
      intro i hi hd
      rcases eq_or_lt_of_le hi with heq | hlt
      · exact ⟨some A, heq ▸ hn⟩
      -- The nearest committed slot strictly above `i`, which exists since `n`
      -- is one. `Nat.find` needs classical decidability: `Decided` is a Prop.
      have hex : ∃ j, i < j ∧ j ≤ n ∧ ∃ A', Decided U V j (some A') :=
        ⟨n, hlt, le_refl _, A, hn⟩
      obtain ⟨hij, hjn, A', hA'⟩ := Nat.find_spec hex
      -- Every slot between is decided by induction, and `none` by nearestness.
      have hmid : ∀ i', i < i' → i' < Nat.find hex →
          (coreAnchored Validator BlockId Payload).Eligible i i' → Decided U V i' none := by
        intro i' h1 h2 _
        have hi'n : i' ≤ n := by omega
        obtain ⟨v, hv⟩ := ih i' hi'n (by omega)
        cases v with
        | none => exact hv
        | some B => exact absurd ⟨h1, hi'n, B, hv⟩ (Nat.find_min hex h2)
      by_cases hc : ∃ L, IsLeaderBlock U i L ∧ CertifiedIn U A' L (S.slotRound i)
      · obtain ⟨L, hL, hcert⟩ := hc
        exact ⟨some L, AnchoredRule.Decided.indirectCommit_single rfl (fun _ _ h => h) hij
          (helig i _ hij) hA' hmid hL hcert⟩
      · push Not at hc
        exact ⟨none, AnchoredRule.Decided.indirectSkip_single rfl hij (helig i _ hij) hA' hmid
          (fun L hL ⟨C, hC, hre⟩ => hc L hL C hC hre)⟩
  intro i hi
  exact key (n - i) i hi (le_refl _)

/-- **L8 under the old three-round spacing.** Combining L6 with L8: for every
slot `k` there is a slot `n ≥ k` such that a sufficiently grown synchronous DAG
decides *every* slot up to `n` — so the ledger does not stall below it.

`hsp` is the field the `Slots` class used to carry. A pipelined or multi-leader
schedule does not satisfy it, and the counterexample above is why this is
stated conditionally rather than dropped. -/
theorem all_decided_below_of_spacing
    (hsp : ∀ k, S.slotRound k + 3 ≤ S.slotRound (k + 1))
    (hT : T ⊆ (Correct : Finset Validator)) (hcard : quorumCard Validator ≤ T.card)
    (fair : FairScheduleOn T) (R : ℕ) (k : ℕ) :
    ∃ n, k ≤ n ∧ R ≤ S.slotRound n ∧
      ∀ (U : BlockUniverse Validator BlockId Payload) (N : ℕ),
        (∀ r, R ≤ r → r ≤ N → PopulatedOn U T r) → SynchronisedOn U T R →
        S.slotRound n + 2 ≤ N →
        ∀ i, i ≤ n → ∃ v, Decided U (View.full U) i v := by
  obtain ⟨n, hkn, hRn, hcommit⟩ := commits_recur_on (BlockId := BlockId) (Payload := Payload)
    hT hcard fair R k
  refine ⟨n, hkn, hRn, ?_⟩
  intro U N hpop hs hN
  obtain ⟨L, _, hdec⟩ := hcommit U N hpop hs hN
  exact decided_of_committed_above (fun _ _ h => eligibleAt_of_lt_of_spacing hsp h) hdec

/-! ## L9 — the obstruction: when slots are stuck for good

L8 clears the backpressure under `helig`. This is the converse direction, and
the reason `helig` is stated as a hypothesis rather than dropped: a set of slots
that is *stuck* stays stuck.

`X` is stuck when three things hold of every slot in it: no candidate has a
certificate anywhere (so neither the direct nor the indirect rule can commit
it), some candidate is not directly skippable (so the direct skip cannot fire
either — a slot with no candidate at all would be skipped vacuously, which is
why a candidate must be assumed to exist), and every *committed eligible* anchor
has another member of `X` eligibly between it and the slot.

**The third clause is about the leader schedule, not about pipelining.** It
requires commits to be *isolated*: with three consecutive commits available the
escape (`decided_of_first_eligible_commit`) gives a vacuous intermediate range
and the clause fails. Under the old three-round spacing it cannot hold at all,
which `stuck_empty_below_commit_of_spacing` below turns into a theorem; under a
pipelined schedule it holds only where Byzantine leaders take essentially three
of every four consecutive slots, which fair round-robin excludes.

So this theorem bounds *when* a stall is possible. It is not a deficiency of
pipelined Mysticeti as deployed. Two things it does not supply: a concrete
universe satisfying the first two clauses — that needs a DAG in which a
Byzantine leader's candidate collects `2f` votes and `2f` blames, one short of
each threshold — and a schedule satisfying the third, which no fair schedule
can. -/

/-- **L9.** Nothing in a stuck set is ever decided, on any view.

Induction on the derivation. Three of the four cases die immediately: a direct
commit and an indirect commit both produce a certificate, and a direct skip
contradicts the unskippable candidate. The fourth, indirect skip, is the
content: its intermediate premise is a *sub-derivation* at some slot which the
regress clause places back inside `X`, so the induction hypothesis applies. A
derivation is a finite tree, so the descent cannot continue for ever — which is
precisely the informal argument, discharged by structural induction rather than
by hand. -/
theorem notMem_stuck_of_decided {V : View Validator BlockId Payload U} {X : Set ℕ}
    (hcert : ∀ i ∈ X, ∀ L, IsLeaderBlock U i L → certificates U L (S.slotRound i) = ∅)
    (hskip : ∀ i ∈ X, ∃ L, IsLeaderBlock U i L ∧ ¬ DirectSkipIn U V L (S.slotRound i))
    (hregress : ∀ i ∈ X, ∀ j, (coreAnchored Validator BlockId Payload).Eligible i j →
      (∃ A, Decided U V j (some A)) →
      ∃ i', i' ∈ X ∧ i < i' ∧ i' < j ∧ (coreAnchored Validator BlockId Payload).Eligible i i')
    {i : ℕ} {v : Option BlockId} (h : Decided U V i v) : i ∉ X := by
  induction h with
  | @directCommit k L hL hdc =>
    intro hk
    obtain ⟨C, hC⟩ := certificates_nonempty_of_directCommit (directCommit_of_directCommitIn hdc)
    rw [hcert k hk L hL] at hC
    exact absurd hC (Finset.notMem_empty C)
  | @directSkip k hall =>
    intro hk
    obtain ⟨L, hL, hns⟩ := hskip k hk
    exact hns (directSkipIn_of_directSkipSlotIn hall hL)
  | @indirectCommit k j A L i _ _ _ _ _ _ hL hcertIn _ _ _ =>
    intro hk
    obtain ⟨C, hC⟩ := certificates_nonempty_of_certifiedIn hcertIn
    rw [hcert k hk L hL] at hC
    exact absurd hC (Finset.notMem_empty C)
  | @indirectSkip k j A _ helig hj _ _ _ ihmid =>
    intro hk
    obtain ⟨i', hi'X, h1, h2, h3⟩ := hregress k hk j helig ⟨A, hj⟩
    exact ihmid i' h1 h2 h3 hi'X

/-! **P7′ — a committed run decides everything below it** — is the
relation's `decided_below_of_committed_run` at `exists_least`: L8 with
`helig` removed, the shape liveness actually needs. Given the slots
`b … n` committed and every slot below `b` having `n` as an *eligible*
anchor — which under pipelining just says the run spans three rounds —
every slot below `b` is decided, with no synchrony, no timing, no
fairness and no hypothesis on the schedule. The anchor is the nearest
**eligible** committed slot, and an eligible intermediate lies below `b`
— in the run it would be committed, contradicting minimality — which is
what lets the induction hypothesis reach it. That second step is the
whole content, and why three consecutive commits suffice where a single
one does not. -/

/-- **L8 and L9 are consistent, and their hypotheses are jointly exhaustive.**

Under the old three-round spacing a stuck set has no member below a committed
slot — so the counterexample of L9 cannot be built there, however the DAG is
arranged. Composing the two results: L8 decides the slot, L9 says a decided
slot is outside `X`.

This is also the check that neither theorem is vacuous. L9 is not the
observation that its hypotheses are unsatisfiable; it is that they are
unsatisfiable *under `helig`*, and satisfiable without it. -/
theorem stuck_empty_below_commit_of_spacing
    (hsp : ∀ k, S.slotRound k + 3 ≤ S.slotRound (k + 1))
    {V : View Validator BlockId Payload U} {X : Set ℕ}
    (hcert : ∀ i ∈ X, ∀ L, IsLeaderBlock U i L → certificates U L (S.slotRound i) = ∅)
    (hskip : ∀ i ∈ X, ∃ L, IsLeaderBlock U i L ∧ ¬ DirectSkipIn U V L (S.slotRound i))
    (hregress : ∀ i ∈ X, ∀ j, (coreAnchored Validator BlockId Payload).Eligible i j →
      (∃ A, Decided U V j (some A)) →
      ∃ i', i' ∈ X ∧ i < i' ∧ i' < j ∧ (coreAnchored Validator BlockId Payload).Eligible i i')
    {n : ℕ} {A : BlockId} (hn : Decided U V n (some A)) :
    ∀ i, i ≤ n → i ∉ X := by
  intro i hi
  obtain ⟨v, hv⟩ :=
    decided_of_committed_above (fun _ _ h => eligibleAt_of_lt_of_spacing hsp h) hn i hi
  exact notMem_stuck_of_decided hcert hskip hregress hv

end LeanDag
