import LeanDag.DoS.Exposure
import LeanDag.Liveness
import LeanDag.CommonCore

/-!
# Liveness survives exclusion

`dos-equivocation-and-growth.md` §4, **D15b**, and §7 S8.

D15a says each caught equivocator costs one unit of the margin over the quorum,
and that at the fault bound a block must reference every correct block of the
round below. This file is the other half, and the one that settles the design:
**exclusion can never make the quorum threshold unreachable.**

The reason is the one `card_correct` was always for. Correct validators are
never exposed (D15), so they are admissible to every block, forever; and there
are at least `2f+1` of them. So the correct population's blocks are, on their
own, an admissible quorum for anybody — whatever has been excluded, and however
much of the fault budget has been used.

**The threshold does not change; the pool it is drawn from does.**

Note the hypothesis. `card_correct` counts correct *validators*, not their
blocks, so something has to say they built: `Populated U n`. That places the
result — it is the induction step of L1 under the condition, not a standalone
claim that building always succeeds. Before `R` the adversary can withhold, and
the step does not fire; after `R`, `EventuallyDelivers` supplies it. Which is
why, under the condition, L1 holds from `R` rather than from round 0.
-/

namespace LeanDag

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {U : BlockUniverse Validator BlockId Payload}
variable {b : BlockId} {n : ℕ}

/-- Decidable on concrete data: `PopulatedOn` is a bounded quantifier over two
`Finset`s, so a model can settle it by `decide`. Stated here rather than beside
the definition because it is the witnesses of `dos-equivocation-and-growth.md` §4 that need it. -/
instance decidablePopulatedOn (T : Finset Validator) (r : ℕ) :
    Decidable (PopulatedOn U T r) :=
  inferInstanceAs (Decidable (∀ v ∈ T, ∃ b ∈ U.ids,
    (U.block b).creator = v ∧ (U.block b).round = r))

omit [DecidableEq BlockId] in
/-- A populated round carries every correct validator among its correct blocks'
authors. -/
theorem correct_subset_creators_correctBlocksAt (h : Populated U n) :
    (Correct : Finset Validator) ⊆ creatorsOf U.block (correctBlocksAt U n) := by
  intro v hv
  obtain ⟨i, hi, hic, hir⟩ := h v hv
  exact mem_creatorsOf.mpr ⟨i, mem_correctBlocksAt.mpr ⟨hi, hir, by rw [hic]; exact hv⟩, hic⟩

omit [DecidableEq BlockId] in
/-- The correct blocks of a populated round carry a quorum of authors. -/
theorem card_creators_correctBlocksAt (h : Populated U n) :
    quorumCard Validator ≤ (creatorsOf U.block (correctBlocksAt U n)).card :=
  le_trans card_correct (Finset.card_le_card (correct_subset_creators_correctBlocksAt h))

/-- No correct block's author is ever excluded — D15, in the form a builder
needs. -/
theorem creator_notMem_exposedTo_of_mem_correctBlocksAt (hb : b ∈ U.ids) {i : BlockId}
    (hi : i ∈ correctBlocksAt U n) : (U.block i).creator ∉ exposedTo U b := by
  intro hmem
  exact (mem_exposedTo.mp hmem).not_correct hb (mem_correctBlocksAt.mp hi).2.2

/-- **D15b — the threshold is met by the correct set alone.**

Given a populated round `n`, its correct blocks are an admissible quorum for
*every* block `b`: they carry `2f+1` distinct authors, and not one of those
authors is exposed to `b`, whoever else is.

So a validator that has heard from the correct population can always build,
and exclusion never starves it. What the adversary can force is the pool down
to exactly `Correct` (D15a) — which is precisely the situation
`|Correct| ≥ 2f+1` was there to survive. -/
theorem correctBlocksAt_admissible_quorum (h : Populated U n) (hb : b ∈ U.ids) :
    quorumCard Validator ≤ (creatorsOf U.block (correctBlocksAt U n)).card ∧
      ∀ i ∈ correctBlocksAt U n, (U.block i).creator ∉ exposedTo U b :=
  ⟨card_creators_correctBlocksAt h, fun _ hi =>
    creator_notMem_exposedTo_of_mem_correctBlocksAt hb hi⟩

/-- The same, phrased as the DoS condition permits it: a block whose references
are correct round-`n` blocks satisfies the reference constraint outright,
because the constraint only ever forbids exposed authors. -/
theorem dosValid_refs_of_correctBlocksAt (hb : b ∈ U.ids)
    (hrefs : ∀ i ∈ (U.block b).refs, i ∈ correctBlocksAt U n) :
    ∀ i ∈ (U.block b).refs, ¬ ExposedIn U b (U.block i).creator := by
  intro i hi hexp
  exact creator_notMem_exposedTo_of_mem_correctBlocksAt hb (hrefs i hi)
    (mem_exposedTo.mpr hexp)

/-! ## The acceptance policy, and where the quorum comes from after `R`

`Delivery` is deliberately free of the DoS vocabulary — it says what arrived
and what was built on, in either regime. The condition enters as a *policy* on
a given delivery: a correct validator declines to build on authors its own next
block would expose. -/

/-- The policy: nothing a correct validator accepts is exposed to the block it
goes on to build. -/
def DoSAccepting (D : Delivery U) : Prop :=
  ∀ v ∈ (Correct : Finset Validator), ∀ n, ∀ b ∈ U.ids,
    (U.block b).creator = v → (U.block b).round = n + 1 →
    ∀ i ∈ D.accepted v n, ¬ ExposedIn U b (U.block i).creator

/-- The tight half of `includes`: a correct validator references *exactly* what
it accepted, no more. `Delivery.includes` gives the other inclusion, and D3's
sharp bound wants both. -/
def ReferencesAccepted (D : Delivery U) : Prop :=
  ∀ v ∈ (Correct : Finset Validator), ∀ n, ∀ b ∈ U.ids,
    (U.block b).creator = v → (U.block b).round = n + 1 →
    (U.block b).refs ⊆ D.accepted v n

/-- **The condition is implementable.** A correct validator following the
policy produces blocks that satisfy the DoS reference constraint.

Only the correct half of `DoSValid` is derivable, and necessarily so: no
delivery assumption constrains what a Byzantine validator publishes. That the
condition is a *validity* rule is what covers the other half — a Byzantine
block breaking it is not in the universe at all. -/
theorem not_exposedIn_refs_of_policy (D : Delivery U) (hacc : DoSAccepting D)
    (href : ReferencesAccepted D) {b : BlockId} (hb : b ∈ U.ids)
    (hbc : (U.block b).creator ∈ (Correct : Finset Validator)) :
    ∀ i ∈ (U.block b).refs, ¬ ExposedIn U b (U.block i).creator := by
  intro i hi
  rcases Nat.eq_zero_or_pos (U.block b).round with hr | hr
  · -- a genesis block references nothing
    rw [(U.valid b hb).refs_empty_of_round_zero hr] at hi
    exact absurd hi (Finset.notMem_empty i)
  · obtain ⟨n, hn⟩ : ∃ n, (U.block b).round = n + 1 := ⟨(U.block b).round - 1, by omega⟩
    exact hacc _ hbc n b hb rfl hn i (href _ hbc n b hb rfl hn hi)

omit [DecidableEq BlockId] in
/-- **Where the quorum comes from after `R`** — and the settled answer to the
plan's Q1.

`Live.builds` needs a quorum of *accepted* creators. After `R` that is not an
extra assumption: `EventuallyDelivers` puts every correct block in every
correct validator's hands, `Delivery.accepts_correct` accepts them, and a
populated round supplies `2f+1` of them. `DeliversQuorum` is therefore a
**consequence** from `R` on, not a hypothesis.

Before `R` it is not, and that is exactly the cost the condition carries: L1
holds from `R` rather than from round 0. -/
theorem card_creators_accepted_of_eventuallyDelivers {R : ℕ} (D : Delivery U)
    (hd : EventuallyDelivers D R) (hn : R ≤ n) (hpop : Populated U n)
    {v : Validator} (hv : v ∈ (Correct : Finset Validator)) :
    quorumCard Validator ≤ (creatorsOf U.block (D.accepted v n)).card := by
  refine le_trans card_correct (Finset.card_le_card ?_)
  intro w hw
  obtain ⟨a, ha, hac, har⟩ := hpop w hw
  have hheld : a ∈ D.held v n := hd n hn v hv a ha har (by rw [hac]; exact hw)
  exact mem_creatorsOf.mpr ⟨a, D.accepts_correct v hv n a hheld (by rw [hac]; exact hw), hac⟩

/-! ## Exclusion after `R` (§4)

D16 produces the exposure, D17 propagates it to every valid block, and D18 is
the companion about what an author gives up by publishing honestly. Only D16
uses synchrony; D17's propagation needs nothing but the fact that every block,
however authored, leans on `f+1` correct blocks. -/

omit [DecidableEq BlockId] in
/-- Every non-genesis block references a **correct** block of the round below.

`2f+1` distinct creators, at most `f` of them Byzantine. This is the fact D17
and D18 both run on, and it holds of Byzantine blocks as much as correct ones —
which is what makes exclusion total rather than a convention. -/
theorem exists_correct_mem_refs {b : BlockId} (hb : b ∈ U.ids)
    (hround : 0 < (U.block b).round) :
    ∃ i ∈ (U.block b).refs, i ∈ U.ids ∧
      (U.block i).creator ∈ (Correct : Finset Validator) ∧
      (U.block i).round + 1 = (U.block b).round := by
  obtain ⟨v, hv, hvc⟩ := exists_correct_of_card
    (S := creatorsOf U.block (U.block b).refs)
    (le_trans (by have := F.card_validators; omega) (U.creators_quorum hb hround))
  obtain ⟨i, hi, rfl⟩ := mem_creatorsOf.mp hv
  exact ⟨i, hi, U.complete b hb i hi, hvc, U.round_of_mem_refs hb hi⟩

/-- **D17 — exclusion is total, and permanent.** If every correct block of
round `n+1` is exposed to `X`, then so is every block from round `n+2` on,
whoever authored it — and under the condition none of them may name `X`.

The induction is one round at a time and uses no synchrony: a block leans on a
correct block below (`exists_correct_mem_refs`), that one is exposed, and
exposure passes upward (D12). Synchrony is what produces the antecedent (D16),
not what propagates it. -/
theorem exposedIn_of_correct_exposed {X : Validator} {n : ℕ}
    (hexp : ∀ c ∈ U.ids, (U.block c).round = n + 1 →
      (U.block c).creator ∈ (Correct : Finset Validator) → ExposedIn U c X) :
    ∀ k, ∀ b ∈ U.ids, (U.block b).round = n + 2 + k → ExposedIn U b X := by
  intro k
  induction k with
  | zero =>
      intro b hb hbr
      obtain ⟨i, hi, hi_ids, hi_correct, hi_round⟩ :=
        exists_correct_mem_refs hb (by omega)
      exact (hexp i hi_ids (by omega) hi_correct).of_mem_refs hb hi
  | succ k ih =>
      intro b hb hbr
      obtain ⟨i, hi, hi_ids, _, hi_round⟩ := exists_correct_mem_refs hb (by omega)
      exact (ih i hi_ids (by omega)).of_mem_refs hb hi

/-- The form the condition consumes: from `n+2` on, nobody may name `X`. -/
theorem not_mem_creators_refs_of_correct_exposed (hdos : DoSValid U) {X : Validator} {n : ℕ}
    (hexp : ∀ c ∈ U.ids, (U.block c).round = n + 1 →
      (U.block c).creator ∈ (Correct : Finset Validator) → ExposedIn U c X)
    {b : BlockId} (hb : b ∈ U.ids) (hbr : n + 2 ≤ (U.block b).round) :
    X ∉ creatorsOf U.block (U.block b).refs := by
  obtain ⟨k, hk⟩ : ∃ k, (U.block b).round = n + 2 + k := ⟨(U.block b).round - (n + 2), by omega⟩
  intro hX
  obtain ⟨i, hi, rfl⟩ := mem_creatorsOf.mp hX
  exact hdos b hb i hi (exposedIn_of_correct_exposed hexp k b hb hk)

/-- **D16 — after `R`, agree or be exposed.** If the histories of two correct
round-`n` blocks between them hold an equivocation by `X`, then *every* correct
round-`(n+1)` block is exposed to `X`.

`SynchronisedOn` puts both round-`n` blocks into the references of every correct
block one round up, so each of the latter inherits the union of their histories.
No tie-break policy can avoid this: correct validators either agree about `X` —
in which case D11 says it gained nothing — or they are all exposed one round
later. -/
theorem exposedIn_of_correct_disagree {R n : ℕ} {X : Validator}
    (hs : SynchronisedOn U (Correct : Finset Validator) R) (hn : R ≤ n)
    {c₁ c₂ : BlockId} (hc₁ : c₁ ∈ U.ids) (hc₁r : (U.block c₁).round = n)
    (hc₁c : (U.block c₁).creator ∈ (Correct : Finset Validator))
    (hc₂ : c₂ ∈ U.ids) (hc₂r : (U.block c₂).round = n)
    (hc₂c : (U.block c₂).creator ∈ (Correct : Finset Validator))
    {i j : BlockId} (hi : i ∈ history U c₁) (hj : j ∈ history U c₂)
    (hpair : EquivPair U X i j)
    {b : BlockId} (hb : b ∈ U.ids) (hbr : (U.block b).round = n + 1)
    (hbc : (U.block b).creator ∈ (Correct : Finset Validator)) :
    ExposedIn U b X :=
  ⟨i, history_subset_of_reaches hb
      (Reaches.single (hs n hn b hb hbr hbc c₁ hc₁ hc₁r hc₁c)) hi,
   j, history_subset_of_reaches hb
      (Reaches.single (hs n hn b hb hbr hbc c₂ hc₂ hc₂r hc₂c)) hj,
   hpair⟩

/-- **D18 — pinning.** If all but at most `f` correct validators put `A` into
their round-`(j+1)` block, then every block from round `j+2` on holds `A` in its
history.

A block leans on `f+1` correct blocks of the round below, and there are not
`f+1` correct validators lacking `A` to draw them all from. So the honest
publisher loses the freedom to be disagreed about later — while an author that
publishes to a strict subset keeps it, which is `liveness.md` §4.3 showing up as
the selective-publication gap that `dos-equivocation-and-growth.md` §5's doubling family exploits. -/
theorem mem_history_of_pinned {A : BlockId} {j : ℕ}
    (hpin : ((Correct : Finset Validator).filter
      (fun v => ¬ ∃ c ∈ U.ids, (U.block c).round = j + 1 ∧ (U.block c).creator = v ∧
        A ∈ (U.block c).refs)).card ≤ F.f) :
    ∀ k, ∀ b ∈ U.ids, (U.block b).round = j + 2 + k → A ∈ history U b := by
  intro k
  induction k with
  | zero =>
      intro b hb hbr
      -- the `f+1` correct creators `b` names cannot all lack `A`
      have hquorum : F.f + 1 ≤
          (creatorsOf U.block (U.block b).refs ∩ (Correct : Finset Validator)).card :=
        card_inter_correct_of_quorum (U.creators_quorum hb (by omega))
      have hnsub : ¬ (creatorsOf U.block (U.block b).refs ∩ (Correct : Finset Validator)) ⊆
          (Correct : Finset Validator).filter
            (fun v => ¬ ∃ c ∈ U.ids, (U.block c).round = j + 1 ∧ (U.block c).creator = v ∧
              A ∈ (U.block c).refs) := by
        intro hsub
        have := Finset.card_le_card hsub
        omega
      obtain ⟨v, hv, hvnot⟩ := Finset.not_subset.mp hnsub
      rw [Finset.mem_inter] at hv
      obtain ⟨i, hi, hic⟩ := mem_creatorsOf.mp hv.1
      have hi_ids : i ∈ U.ids := U.complete b hb i hi
      have hi_round : (U.block i).round = j + 1 := by
        have := U.round_of_mem_refs hb hi; omega
      -- `v` does publish `A`, and by T1 that block is `i` itself
      obtain ⟨c, hc, hcr, hcc, hcA⟩ : ∃ c ∈ U.ids, (U.block c).round = j + 1 ∧
          (U.block c).creator = v ∧ A ∈ (U.block c).refs := by
        by_contra hcon
        exact hvnot (Finset.mem_filter.mpr ⟨hv.2, hcon⟩)
      have : c = i := U.eq_of_creator_eq hc hi_ids hv.2 hcc (by rw [hic]) (by omega)
      exact history_subset_of_reaches hb (Reaches.single hi)
        (mem_history_of_mem_refs hi_ids (this ▸ hcA))
  | succ k ih =>
      intro b hb hbr
      obtain ⟨i, hi, hi_ids, _, hi_round⟩ := exists_correct_mem_refs hb (by omega)
      exact history_subset_of_reaches hb (Reaches.single hi) (ih i hi_ids (by omega))

/-! ## D8a — exposure is structural, not accidental

D8 says the reference graph cannot *report* an equivocation, which reads as
making exposure a matter of luck. It is not. A validator accepts one block per
author and references what it accepted, so if any two authors it accepts carry
different halves in their histories, the validator performs the merge itself,
in its own next block, as a matter of course.

Note what the two accepted blocks are: they have **different authors**. The
acceptance rule forbids accepting both halves directly (`accepted_inj`), so the
equivocation is never in the accepted set — it is one layer down, in the
histories of two blocks that disagree. Which is exactly `Umerge`. -/

/-- **D8a.** A validator whose accepted set spans two disagreeing histories
exposes the author in its own next block. -/
theorem exposedIn_of_accepted_span (D : Delivery U) {v : Validator}
    (hv : v ∈ (Correct : Finset Validator)) {n : ℕ} {b : BlockId} (hb : b ∈ U.ids)
    (hbc : (U.block b).creator = v) (hbr : (U.block b).round = n + 1)
    {p q : BlockId} (hp : p ∈ D.accepted v n) (hq : q ∈ D.accepted v n)
    {X : Validator} {i j : BlockId} (hi : i ∈ history U p) (hj : j ∈ history U q)
    (hpair : EquivPair U X i j) : ExposedIn U b X :=
  ⟨i, history_subset_of_reaches hb (Reaches.single (D.includes v hv n b hb hbc hbr hp)) hi,
   j, history_subset_of_reaches hb (Reaches.single (D.includes v hv n b hb hbc hbr hq)) hj,
   hpair⟩

/-! ## The intersection lemma

A sharpening of D18, kept for its own sake. Two blocks that both *name* `X` are both `X`-clean, and
each leans on `f+1` correct blocks; when the correct validators number at most
`2f+1` those two sets must meet, and a correct validator has one block per round
(T1), so meeting in a *creator* means meeting in a *block*. Both then contain
that block's history, and being clean, both must agree with it about `X`.

This strictly strengthens D18: the hypothesis becomes *some shared ancestor
heard from `X`*, rather than *`X` published to all but `f` correct validators*.

Its scope is a case split that may be the whole proof. The intersection needs
`|Correct| ≤ 2f+1`, i.e. the adversary spending its full budget — and when it
spends less, D9's branching factor, which is the *number* of Byzantine authors,
falls by the same amount. The adversary cannot have both. -/

omit [DecidableEq BlockId] in
/-- Two blocks of the same round share a correct reference, when the correct
validators are as few as the fault bound permits. -/
theorem exists_shared_correct_ref (hcard : (Correct : Finset Validator).card ≤ quorumCard Validator)
    {c₁ c₂ : BlockId} (hc₁ : c₁ ∈ U.ids) (hc₂ : c₂ ∈ U.ids)
    (hround : (U.block c₁).round = (U.block c₂).round) (hpos : 0 < (U.block c₁).round) :
    ∃ w, w ∈ (U.block c₁).refs ∧ w ∈ (U.block c₂).refs ∧
      (U.block w).creator ∈ (Correct : Finset Validator) := by
  -- each names at least `n - f - b` correct authors out of the `n - b`
  -- correct validators, and two such sets cannot miss each other:
  -- `2(n-f-b) - (n-b) = n - 2f - b ≥ f+1-b ≥ 1`.
  have hq₁ := U.creators_quorum hc₁ hpos
  have hq₂ := U.creators_quorum hc₂ (by omega)
  have h₁ := card_le_card_inter_correct_add_byzantine
    (creatorsOf U.block (U.block c₁).refs)
  have h₂ := card_le_card_inter_correct_add_byzantine
    (creatorsOf U.block (U.block c₂).refs)
  obtain ⟨hcb, hbf, hnv⟩ := faults_arith (Validator := Validator)
  have hsub : (creatorsOf U.block (U.block c₁).refs ∩ (Correct : Finset Validator)) ∪
      (creatorsOf U.block (U.block c₂).refs ∩ (Correct : Finset Validator)) ⊆
      (Correct : Finset Validator) :=
    Finset.union_subset Finset.inter_subset_right Finset.inter_subset_right
  have hunion := Finset.card_le_card hsub
  have hadd := Finset.card_union_add_card_inter
    (creatorsOf U.block (U.block c₁).refs ∩ (Correct : Finset Validator))
    (creatorsOf U.block (U.block c₂).refs ∩ (Correct : Finset Validator))
  obtain ⟨v, hv⟩ := Finset.card_pos.mp (show 0 <
    ((creatorsOf U.block (U.block c₁).refs ∩ (Correct : Finset Validator)) ∩
      (creatorsOf U.block (U.block c₂).refs ∩ (Correct : Finset Validator))).card from by
    omega)
  rw [Finset.mem_inter, Finset.mem_inter, Finset.mem_inter] at hv
  obtain ⟨⟨hv₁, hvc⟩, hv₂, -⟩ := hv
  obtain ⟨i₁, hi₁, hi₁c⟩ := mem_creatorsOf.mp hv₁
  obtain ⟨i₂, hi₂, hi₂c⟩ := mem_creatorsOf.mp hv₂
  -- one block per correct author per round, so the two references coincide
  have : i₁ = i₂ :=
    U.eq_of_creator_eq (U.complete c₁ hc₁ i₁ hi₁) (U.complete c₂ hc₂ i₂ hi₂) hvc hi₁c hi₂c
      (by have := U.round_of_mem_refs hc₁ hi₁; have := U.round_of_mem_refs hc₂ hi₂; omega)
  exact ⟨i₁, hi₁, this ▸ hi₂, by rw [hi₁c]; exact hvc⟩

/-- **The intersection lemma.** Two blocks that both name `X` agree about `X`
wherever their shared correct reference speaks about it.

`A` is the shared ancestor's `X`-block at some round; each namer, being
`X`-clean, can hold only one `X`-block at that round, and already holds `A`. So
whatever either of them holds there *is* `A`.

Where the shared ancestor is silent about `X` the two may still differ —
which is why the per-round count ultimately needs the pedigree machinery of
`dos-equivocation-and-growth.md` §5. -/
theorem eq_of_both_name_of_shared (hdos : DoSValid U)
    {c₁ c₂ w : BlockId} (hc₁ : c₁ ∈ U.ids) (hc₂ : c₂ ∈ U.ids)
    (hw₁ : w ∈ (U.block c₁).refs) (hw₂ : w ∈ (U.block c₂).refs)
    {X : Validator} (hn₁ : X ∈ creatorsOf U.block (U.block c₁).refs)
    (hn₂ : X ∈ creatorsOf U.block (U.block c₂).refs)
    {A A₁ A₂ : BlockId} (hA : A ∈ history U w)
    (hA₁ : A₁ ∈ history U c₁) (hA₂ : A₂ ∈ history U c₂)
    (hAc : (U.block A).creator = X) (hA₁c : (U.block A₁).creator = X)
    (hA₂c : (U.block A₂).creator = X)
    (hA₁r : (U.block A₁).round = (U.block A).round)
    (hA₂r : (U.block A₂).round = (U.block A).round) : A₁ = A₂ := by
  -- naming `X` forces cleanliness about `X` (D19b), which forces uniqueness
  have hclean₁ : ¬ ExposedIn U c₁ X := by
    obtain ⟨i, hi, rfl⟩ := mem_creatorsOf.mp hn₁; exact hdos c₁ hc₁ i hi
  have hclean₂ : ¬ ExposedIn U c₂ X := by
    obtain ⟨i, hi, rfl⟩ := mem_creatorsOf.mp hn₂; exact hdos c₂ hc₂ i hi
  have hAw₁ : A ∈ history U c₁ := history_subset_of_reaches hc₁ (Reaches.single hw₁) hA
  have hAw₂ : A ∈ history U c₂ := history_subset_of_reaches hc₂ (Reaches.single hw₂) hA
  have e₁ : A₁ = A := by
    by_contra hne
    exact hclean₁ ⟨A₁, hA₁, A, hAw₁, hne, hA₁c, hAc, hA₁r⟩
  have e₂ : A₂ = A := by
    by_contra hne
    exact hclean₂ ⟨A₂, hA₂, A, hAw₂, hne, hA₂c, hAc, hA₂r⟩
  rw [e₁, e₂]

/-! ## The correct backbone

After `R`,
`SynchronisedOn` makes every correct block reference every correct block one
round below — and that composes: **a correct block's history contains every
correct block of every round from `R` to its own.**

The induction needs no population hypothesis. A block references `2f+1`
distinct creators of which at most `f` are Byzantine, so a correct block one
round up always exists to step through (`exists_correct_mem_refs`). -/

/-- **The backbone lemma.** After `R`, correct histories contain the whole
correct past. -/
theorem mem_history_of_correct {R : ℕ} (hs : SynchronisedOn U (Correct : Finset Validator) R) :
    ∀ d : ℕ, ∀ c ∈ U.ids, ∀ a ∈ U.ids,
      (U.block c).creator ∈ (Correct : Finset Validator) →
      (U.block a).creator ∈ (Correct : Finset Validator) →
      R ≤ (U.block a).round → (U.block a).round + 1 + d = (U.block c).round →
      a ∈ history U c := by
  intro d
  induction d with
  | zero =>
      intro c hc a ha hcc hac hR hround
      exact mem_history_of_mem_refs hc
        (hs (U.block a).round hR c hc (by omega) hcc a ha rfl hac)
  | succ d ih =>
      intro c hc a ha hcc hac hR hround
      -- step down one round through a correct reference, which always exists
      obtain ⟨w, hw, hw_ids, hw_correct, hw_round⟩ :=
        exists_correct_mem_refs hc (by omega)
      exact history_subset_of_reaches hc (Reaches.single hw)
        (ih w hw_ids a ha hw_correct hac hR (by omega))

/-! ## Two delivery policies, and what they do and do not yield

`dos-equivocation-and-growth.md` §5. Two policies making explicit what the
model otherwise leaves to prose; with them, nothing an author publishes is
invisible to the correct population. -/

/-- **What `U` means, made explicit.** §4.2 of `liveness.md` defines `U` as
every block some correct validator held; the model has never said so. -/
def HeldByCorrect (D : Delivery U) : Prop :=
  ∀ i ∈ U.ids, ∃ v ∈ (Correct : Finset Validator), i ∈ D.held v (U.block i).round

/-- **A stronger acceptance policy**: a validator that holds a block by some
author accepts *some* block by that author. `Delivery.accepts_correct` demands
this only of correct authors. -/
def AcceptsSome (D : Delivery U) : Prop :=
  ∀ v ∈ (Correct : Finset Validator), ∀ n, ∀ a ∈ D.held v n,
    ∃ i ∈ D.accepted v n, (U.block i).creator = (U.block a).creator

omit [DecidableEq BlockId] in
/-- What the two policies do yield: **nothing an author publishes is invisible to
the correct population.** If any block by `X` at round `n` exists at all, some
correct validator accepted a block by `X` at round `n` — and so referenced one,
if it built.

Kept because it stands on its own; the C1′ proof itself goes through the
pedigree machinery of
`dos-equivocation-and-growth.md` §5. -/
theorem exists_accepted_of_mem_ids (D : Delivery U) (hheld : HeldByCorrect D)
    (hsome : AcceptsSome D) {A : BlockId} (hA : A ∈ U.ids) :
    ∃ v ∈ (Correct : Finset Validator), ∃ i ∈ D.accepted v (U.block A).round,
      (U.block i).creator = (U.block A).creator := by
  obtain ⟨v, hv, hheldA⟩ := hheld A hA
  obtain ⟨i, hi, hic⟩ := hsome v hv (U.block A).round A hheldA
  exact ⟨v, hv, i, hi, hic⟩

end LeanDag
