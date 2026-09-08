import LeanDag.Common.History
/-!
# Exposure, and the DoS-protection condition

`dos-equivocation-and-growth.md` §3, results D11-D13. `X` is exposed in
`b`'s history when the history holds two distinct blocks by `X` at one
round, a local checkable test, and `DoSValid` forbids a block from
referencing an exposed author. D11 says being inflated by `X` and
exposing `X` are the same condition; D12 says exposure is inherited
upward, so exclusion is permanent; D13 says the test is
view-independent.
-/

namespace LeanDag

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {U : BlockUniverse Validator BlockId Payload}

/-- Two ids witnessing an equivocation by `X`: distinct, both authored by
`X`, both at one round. -/
def EquivPair (U : BlockUniverse Validator BlockId Payload) (X : Validator) (i j : BlockId) :
    Prop :=
  i ≠ j ∧ (U.block i).creator = X ∧ (U.block j).creator = X ∧
    (U.block i).round = (U.block j).round

instance decidableEquivPair (X : Validator) (i j : BlockId) : Decidable (EquivPair U X i j) :=
  inferInstanceAs (Decidable (i ≠ j ∧ _ ∧ _ ∧ _))

omit [DecidableEq BlockId] in
theorem EquivPair.symm {X : Validator} {i j : BlockId} (h : EquivPair U X i j) :
    EquivPair U X j i :=
  ⟨h.1.symm, h.2.2.1, h.2.1, h.2.2.2.symm⟩

/-- **`X` is exposed in `b`'s history**: two distinct blocks by `X` at one
round lie below `b`. -/
def ExposedIn (U : BlockUniverse Validator BlockId Payload) (b : BlockId) (X : Validator) :
    Prop :=
  ∃ i ∈ history U b, ∃ j ∈ history U b, EquivPair U X i j

/-- The pair is sought among `X`'s own blocks. Filtering the history by
author first turns a scan over every pair of the history into one over
the pairs a single validator authored, which is what a `decide` witness
over a concrete DAG pays for; the proposition is unchanged. -/
instance decidableExposedIn (b : BlockId) (X : Validator) : Decidable (ExposedIn U b X) :=
  decidable_of_iff
    (∃ i ∈ (history U b).filter (fun x => (U.block x).creator = X),
      ∃ j ∈ (history U b).filter (fun x => (U.block x).creator = X),
        i ≠ j ∧ (U.block i).round = (U.block j).round)
    (by
      constructor
      · rintro ⟨i, hi, j, hj, hij, hr⟩
        rw [Finset.mem_filter] at hi hj
        exact ⟨i, hi.1, j, hj.1, hij, hi.2, hj.2, hr⟩
      · rintro ⟨i, hi, j, hj, hij, hci, hcj, hr⟩
        exact ⟨i, Finset.mem_filter.mpr ⟨hi, hci⟩, j, Finset.mem_filter.mpr ⟨hj, hcj⟩, hij, hr⟩)

theorem exposedIn_iff_reaches {b : BlockId} {X : Validator} (hb : b ∈ U.ids) :
    ExposedIn U b X ↔
      ∃ i j, Reaches U b i ∧ Reaches U b j ∧ EquivPair U X i j := by
  constructor
  · rintro ⟨i, hi, j, hj, hpair⟩
    exact ⟨i, j, (mem_history_iff hb).mp hi, (mem_history_iff hb).mp hj, hpair⟩
  · rintro ⟨i, j, hi, hj, hpair⟩
    exact ⟨i, (mem_history_iff hb).mpr hi, j, (mem_history_iff hb).mpr hj, hpair⟩

/-- **The DoS-protection condition** (`dos-equivocation-and-growth.md` §3):
a block may not reference an author exposed in its own history. A
predicate on the universe, not a field of `ValidWrt`, so results that need
it take it as an extra hypothesis. -/
def DoSValid (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ b ∈ U.ids, ∀ i ∈ (U.block b).refs, ¬ ExposedIn U b (U.block i).creator

/-- Decidable on concrete data, so a small DAG can be checked by `decide`. -/
instance decidableDoSValid : Decidable (DoSValid U) :=
  inferInstanceAs (Decidable (∀ b ∈ U.ids, ∀ i ∈ (U.block b).refs,
    ¬ ExposedIn U b (U.block i).creator))

/-! ## D11 — inflation *is* exposure -/

/-- The blocks of `b`'s history authored by `X` at round `n`. The thing the
size results count. -/
def historyBlocksOf (U : BlockUniverse Validator BlockId Payload) (b : BlockId)
    (X : Validator) (n : ℕ) : Finset BlockId :=
  (history U b).filter (fun i => (U.block i).creator = X ∧ (U.block i).round = n)

/-- Membership in `historyBlocksOf`, unfolded. -/
theorem mem_historyBlocksOf {b i : BlockId} {X : Validator} {n : ℕ} :
    i ∈ historyBlocksOf U b X n ↔
      i ∈ history U b ∧ (U.block i).creator = X ∧ (U.block i).round = n := by
  simp [historyBlocksOf]

/-- **Not exposed** and **at most one block per round** are the same
condition — the counting form of `ExposedIn`, and the content of D11. -/
theorem not_exposedIn_iff_card_le_one {b : BlockId} {X : Validator} :
    ¬ ExposedIn U b X ↔ ∀ n, (historyBlocksOf U b X n).card ≤ 1 := by
  constructor
  · intro h n
    rw [Finset.card_le_one]
    intro i hi j hj
    by_contra hne
    obtain ⟨hi_hist, hi_creator, hi_round⟩ := mem_historyBlocksOf.mp hi
    obtain ⟨hj_hist, hj_creator, hj_round⟩ := mem_historyBlocksOf.mp hj
    exact h ⟨i, hi_hist, j, hj_hist, hne, hi_creator, hj_creator, by rw [hi_round, hj_round]⟩
  · rintro h ⟨i, hi, j, hj, hne, hi_creator, hj_creator, hround⟩
    have hcard := h (U.block i).round
    rw [Finset.card_le_one] at hcard
    exact hne (hcard i (mem_historyBlocksOf.mpr ⟨hi, hi_creator, rfl⟩)
      j (mem_historyBlocksOf.mpr ⟨hj, hj_creator, hround.symm⟩))

/-- **D11.** Under the DoS condition, an author either contributed at most
one block per round to a block's history, or that block does not reference
it. -/
theorem card_le_one_or_not_mem_refs (hdos : DoSValid U) {b : BlockId} (hb : b ∈ U.ids)
    (X : Validator) :
    (∀ n, (historyBlocksOf U b X n).card ≤ 1) ∨
      (∀ i ∈ (U.block b).refs, (U.block i).creator ≠ X) := by
  by_cases hexp : ExposedIn U b X
  · refine Or.inr fun i hi hcreator => hdos b hb i hi ?_
    rwa [hcreator]
  · exact Or.inl (not_exposedIn_iff_card_le_one.mp hexp)

/-! ## D7, D8 — an equivocation is only ever visible at a merge -/

omit [DecidableEq BlockId] in
/-- **D7, the no-equivocation half.** A block's references carry distinct
authors, so the layer immediately below a block is equivocation-free. -/
theorem eq_of_mem_refs_of_creator_eq {b i j : BlockId} (hb : b ∈ U.ids)
    (hi : i ∈ (U.block b).refs) (hj : j ∈ (U.block b).refs)
    (hcreator : (U.block i).creator = (U.block j).creator) : i = j :=
  (U.valid b hb).distinct_creators i hi j hj hcreator

/-- **D8.** An equivocation shows up in a history only two rounds above the
round it happened at: neither witness can sit at `b`'s round or the one
below, whose authors are distinct by validity. -/
theorem round_add_two_le_of_equivPair {b i j : BlockId} {X : Validator} (hb : b ∈ U.ids)
    (hi : i ∈ history U b) (hj : j ∈ history U b) (hpair : EquivPair U X i j) :
    (U.block i).round + 2 ≤ (U.block b).round := by
  obtain ⟨hne, hic, hjc, hround⟩ := hpair
  have hi_le := round_le_of_mem_history hb hi
  have hj_le := round_le_of_mem_history hb hj
  rcases Nat.lt_or_ge ((U.block i).round + 1) (U.block b).round with hlt | hge
  · omega
  -- the pair sits at `b`'s round or one below; both are impossible
  rcases Nat.eq_or_lt_of_le hi_le with heq | hlt'
  · exact absurd ((eq_of_mem_history_of_round_eq hb hi heq).trans
      (eq_of_mem_history_of_round_eq hb hj (by omega)).symm) hne
  · have hi_refs := mem_refs_of_mem_history_of_round_succ hb hi (by omega)
    have hj_refs := mem_refs_of_mem_history_of_round_succ hb hj (by omega)
    exact absurd (eq_of_mem_refs_of_creator_eq hb hi_refs hj_refs (hic.trans hjc.symm)) hne

/-- Nothing is exposed below round 2: there is not room for a merge. -/
theorem not_exposedIn_of_round_le_one {b : BlockId} {X : Validator} (hb : b ∈ U.ids)
    (hr : (U.block b).round ≤ 1) : ¬ ExposedIn U b X := by
  rintro ⟨i, hi, j, hj, hpair⟩
  have := round_add_two_le_of_equivPair hb hi hj hpair
  omega

/-! ## D12 — exposure is permanent -/

/-- **D12.** Exposure is inherited by everything above: what one block's
history reveals, every block reaching it reveals too. -/
theorem ExposedIn.mono {c b : BlockId} {X : Validator} (hc : c ∈ U.ids)
    (hreach : Reaches U c b) (h : ExposedIn U b X) : ExposedIn U c X := by
  obtain ⟨i, hi, j, hj, hpair⟩ := h
  have hsub := history_subset_of_reaches hc hreach
  exact ⟨i, hsub hi, j, hsub hj, hpair⟩

/-- Exposure passes up a single reference. -/
theorem ExposedIn.of_mem_refs {c b : BlockId} {X : Validator} (hc : c ∈ U.ids)
    (hb : b ∈ (U.block c).refs) (h : ExposedIn U b X) : ExposedIn U c X :=
  h.mono hc (Reaches.single hb)

/-! ## D15, D15a — who can be excluded, and what it costs (§4). Exposure
never lands on a correct validator; each exposed author costs one unit
of the margin over the quorum. -/

/-- **D15 — exclusion is sound.** An exposed author is Byzantine: T1
contraposed, since a correct validator cannot have two ids at one round. -/
theorem ExposedIn.not_correct {b : BlockId} {X : Validator} (hb : b ∈ U.ids)
    (h : ExposedIn U b X) : X ∉ (Correct : Finset Validator) := by
  obtain ⟨i, hi, j, hj, hne, hic, hjc, hround⟩ := h
  intro hX
  exact hne (U.eq_of_creator_eq (history_subset_ids hb hi) (history_subset_ids hb hj)
    hX hic hjc hround)

/-- The authors a block's history has caught. -/
def exposedTo (U : BlockUniverse Validator BlockId Payload) (b : BlockId) : Finset Validator :=
  Finset.univ.filter (fun X => ExposedIn U b X)

/-- `exposedTo` collects exactly the authors exposed in the block's history — the `Finset` form of `ExposedIn`. -/
@[simp]
theorem mem_exposedTo {b : BlockId} {X : Validator} :
    X ∈ exposedTo U b ↔ ExposedIn U b X := by simp [exposedTo]

theorem exposedTo_subset_byzantine {b : BlockId} (hb : b ∈ U.ids) :
    exposedTo U b ⊆ F.byzantine := by
  intro X hX
  simpa using (mem_exposedTo.mp hX).not_correct hb

/-- At most `f` authors can be exposed, since exposure requires
equivocation. -/
theorem card_exposedTo_le {b : BlockId} (hb : b ∈ U.ids) : (exposedTo U b).card ≤ F.f :=
  le_trans (Finset.card_le_card (exposedTo_subset_byzantine hb)) F.card_byzantine

/-- A block never names an author its own history has caught. -/
theorem creators_refs_disjoint_exposedTo (hdos : DoSValid U) {b : BlockId} (hb : b ∈ U.ids) :
    Disjoint (creatorsOf U.block (U.block b).refs) (exposedTo U b) := by
  rw [Finset.disjoint_right]
  intro X hX hXc
  rw [mem_creatorsOf] at hXc
  obtain ⟨i, hi, rfl⟩ := hXc
  exact hdos b hb i hi (mem_exposedTo.mp hX)

/-- **D15a — the margin.** The authors a block references and the authors
it has caught are disjoint, so together they fit inside `n`: `k` caught
equivocators leave a margin of `f − k` over the `n−f` a block must name. -/
theorem card_creators_refs_add_card_exposedTo_le (hdos : DoSValid U) {b : BlockId}
    (hb : b ∈ U.ids) :
    (creatorsOf U.block (U.block b).refs).card + (exposedTo U b).card ≤ Fintype.card Validator := by
  have hdisj := creators_refs_disjoint_exposedTo hdos hb
  have hadd := Finset.card_union_add_card_inter
    (creatorsOf U.block (U.block b).refs) (exposedTo U b)
  have hinter : (creatorsOf U.block (U.block b).refs ∩ exposedTo U b) = ∅ :=
    Finset.disjoint_iff_inter_eq_empty.mp hdisj
  have huniv := Finset.card_le_univ
    (creatorsOf U.block (U.block b).refs ∪ exposedTo U b)
  rw [hinter] at hadd
  simp only [Finset.card_empty] at hadd
  omega

/-- **D15a at the bound.** Once a block has caught the whole fault budget,
its references are exactly the correct validators. -/
theorem creators_refs_eq_correct (hdos : DoSValid U) {b : BlockId} (hb : b ∈ U.ids)
    (hround : 0 < (U.block b).round) (hk : F.f ≤ (exposedTo U b).card) :
    creatorsOf U.block (U.block b).refs = (Correct : Finset Validator) := by
  -- the exposed set has caught everyone there is to catch
  have hbyz : exposedTo U b = F.byzantine :=
    Finset.eq_of_subset_of_card_le (exposedTo_subset_byzantine hb)
      (le_trans F.card_byzantine hk)
  have hcard_byz : F.byzantine.card = F.f :=
    le_antisymm F.card_byzantine (hbyz ▸ hk)
  have hcorrect : (Correct : Finset Validator).card = quorumCard Validator := by
    have := card_correct_add_byzantine (Validator := Validator)
    omega
  -- references avoid the exposed set, which is now the Byzantine set
  have hsub : creatorsOf U.block (U.block b).refs ⊆ (Correct : Finset Validator) := by
    intro X hX
    have := Finset.disjoint_left.mp (creators_refs_disjoint_exposedTo hdos hb) hX
    rw [hbyz] at this
    simpa using this
  refine Finset.eq_of_subset_of_card_le hsub ?_
  rw [hcorrect]
  exact U.creators_quorum hb hround

/-! ## D13 — exposure is view-independent (T6a): a causal-history
question gives the same answer whether or not confined to a view. -/

/-- Causal history never escapes a view — T6a in `Finset` form. -/
theorem history_subset_view {V : View Validator BlockId Payload U} {b : BlockId}
    (hb : b ∈ V.ids) : history U b ⊆ V.ids :=
  fun _ hi => View.mem_of_reaches hb ((mem_history_iff (V.subset_ids hb)).mp hi)

/-- **D13.** Restricting the search for an equivocation to a view that
holds `b` changes nothing, so two correct validators with different views
never disagree about `DoSValid`. -/
theorem exposedIn_iff_of_view {V : View Validator BlockId Payload U} {b : BlockId}
    {X : Validator} (hb : b ∈ V.ids) :
    (∃ i ∈ V.ids, ∃ j ∈ V.ids, i ∈ history U b ∧ j ∈ history U b ∧ EquivPair U X i j) ↔
      ExposedIn U b X := by
  constructor
  · rintro ⟨i, _, j, _, hi, hj, hpair⟩
    exact ⟨i, hi, j, hj, hpair⟩
  · rintro ⟨i, hi, j, hj, hpair⟩
    exact ⟨i, history_subset_view hb hi, j, history_subset_view hb hj, hi, hj, hpair⟩

end LeanDag
