import LeanDag.Hybrid.Faults
import LeanDag.Mysticeti.Rule
import LeanDag.Common.History
/-!
# The hybrid two-round rules, and the arithmetic core

The Odontoceti rules at the hybrid thresholds. The direct rules count
`q = n − fb − fc` distinct authors — the derived instance's quorum,
written out so the arithmetic is visible to `omega` — and the indirect
test `ThickLink k` carries its threshold as a parameter: any

    2·fb + fc + 1  ≤  k  ≤  n − 3·fb − 2·fc

is admissible, the lower end consumed by the skip-side conflicts
(H3, H5), the upper end supplied by link integrity (H4), and the
interval nonempty exactly at the class bound `n ≥ 5·fb + 3·fc + 1`.
`hybrid.md`'s tight constant and the `n`-relative house choice are the
two named instantiations (`kTight`, `kRel`).

Every safety theorem here threads `HonestNoEquiv`: the counting
discounts against the *honest* population `n − fb` (crash-prone
validators cannot face both ways either), while every quorum is taken
against the derived population `n − fb − fc`. This split is the whole
difference from the pure-Byzantine arithmetic; the proof skeletons are
the Odontoceti ones with the discount moved.
-/

namespace LeanDag

namespace Hybrid

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [H : HybridFaults Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {U : BlockUniverse Validator BlockId Payload}
variable {L A : BlockId} {r k : ℕ}

/-! ## Thresholds -/

variable (Validator) in
/-- The hybrid quorum `q = n − fb − fc` — the derived instance's
`n − F.f`, spelled out. -/
def q : ℕ := Fintype.card Validator - (H.fb + H.fc)

variable (Validator) in
/-- `hybrid.md`'s tight indirect threshold. -/
def kTight : ℕ := 2 * H.fb + H.fc + 1

variable (Validator) in
/-- The `n`-relative indirect threshold, mirroring the house
generalization of `2f + 1` to `n − 3f`; equal to `kTight` at the tight
committee. -/
def kRel : ℕ := Fintype.card Validator - (3 * H.fb + 2 * H.fc)

variable (Validator) in
/-- **The admissible interval.** The two inequalities the rule theorems
consume; nonempty exactly when `n ≥ 5·fb + 3·fc + 1`. -/
def Admissible (k : ℕ) : Prop :=
  2 * H.fb + H.fc + 1 ≤ k ∧ k + 3 * H.fb + 2 * H.fc ≤ Fintype.card Validator

instance : Decidable (Admissible Validator k) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Both named thresholds are admissible exactly at the committee
bound — which is the content of the bound: a working threshold exists
iff `n ≥ 5·fb + 3·fc + 1`. -/
theorem admissible_kTight
    (hn : 5 * H.fb + 3 * H.fc + 1 ≤ Fintype.card Validator) :
    Admissible Validator (kTight Validator) := by
  unfold Admissible kTight
  omega

theorem admissible_kRel
    (hn : 5 * H.fb + 3 * H.fc + 1 ≤ Fintype.card Validator) :
    Admissible Validator (kRel Validator) := by
  unfold Admissible kRel
  omega

/-- **The committee bound is the existence of a threshold.** The admissible
interval is nonempty exactly when `n ≥ 5·fb + 3·fc + 1`, so the bound is not a
separate hypothesis of the hybrid arc: every safety result consumes an
admissible `k`, and having one is the bound. -/
theorem exists_admissible_iff :
    (∃ k, Admissible Validator k) ↔
      5 * H.fb + 3 * H.fc + 1 ≤ Fintype.card Validator := by
  constructor
  · rintro ⟨k, hk⟩
    unfold Admissible at hk
    omega
  · exact fun hn => ⟨kTight Validator, admissible_kTight hn⟩

/-- The converse: an admissible threshold forces the committee bound.
Nonemptiness of the interval *is* `n ≥ 5·fb + 3·fc + 1`. -/
theorem committee_bound_of_admissible {k : ℕ}
    (hk : Admissible Validator k) :
    5 * H.fb + 3 * H.fc + 1 ≤ Fintype.card Validator := by
  obtain ⟨h1, h2⟩ := hk
  omega

/-! ## The direct rules -/

/-- **Direct commit**: `q` distinct authors support `L` at its decision
round. -/
def DirectCommit (U : BlockUniverse Validator BlockId Payload)
    (L : BlockId) (r : ℕ) : Prop :=
  q Validator ≤ (supporters U L (r + 1)).card

/-- **Direct skip**: `q` distinct authors blame `L` at its decision
round. -/
def DirectSkip (U : BlockUniverse Validator BlockId Payload)
    (L : BlockId) (r : ℕ) : Prop :=
  q Validator ≤ (blames U L (r + 1)).card

instance : Decidable (DirectCommit U L r) :=
  inferInstanceAs (Decidable (_ ≤ _))

instance : Decidable (DirectSkip U L r) :=
  inferInstanceAs (Decidable (_ ≤ _))

/-! ## The indirect test -/

/-- The authors of decision-round support blocks for `L` visible in
`A`'s cone — by distinct authors, the count equivocation cannot
inflate. -/
def coneSupports (U : BlockUniverse Validator BlockId Payload)
    (A L : BlockId) (r : ℕ) : Finset Validator :=
  creatorsOf U.block
    ((blocksAt U (r + 1)).filter
      (fun p => L ∈ (U.block p).refs ∧ p ∈ history U A))

theorem mem_coneSupports {v : Validator} :
    v ∈ coneSupports U A L r ↔
      ∃ p ∈ U.ids, (U.block p).round = r + 1 ∧ L ∈ (U.block p).refs ∧
        p ∈ history U A ∧ (U.block p).creator = v := by
  simp only [coneSupports, mem_creatorsOf, Finset.mem_filter, mem_blocksAt]
  tauto

/-- In-cone supporters are supporters. -/
theorem coneSupports_subset_supporters :
    coneSupports U A L r ⊆ supporters U L (r + 1) := by
  intro v hv
  obtain ⟨p, hp, hpr, hpL, -, hpc⟩ := mem_coneSupports.mp hv
  exact mem_supporters.mpr ⟨p, hp, hpr, hpL, hpc⟩

/-- Cones nest, so in-cone support does. -/
theorem coneSupports_subset_of_reaches {B : BlockId} (hB : B ∈ U.ids)
    (h : Reaches U B A) :
    coneSupports U A L r ⊆ coneSupports U B L r := by
  intro v hv
  obtain ⟨p, hp, hpr, hpL, hpA, hpc⟩ := mem_coneSupports.mp hv
  have hA : A ∈ U.ids := mem_ids_of_reaches hB h
  exact mem_coneSupports.mpr
    ⟨p, hp, hpr, hpL, history_subset_of_reaches hB h hpA, hpc⟩

/-- **The indirect test** at threshold `k`: at least `k` distinct
authors of support blocks in the anchor's cone. -/
def ThickLink (k : ℕ) (U : BlockUniverse Validator BlockId Payload)
    (A L : BlockId) (r : ℕ) : Prop :=
  k ≤ (coneSupports U A L r).card

instance : Decidable (ThickLink k U A L r) :=
  inferInstanceAs (Decidable (_ ≤ _))

/-! ## H2 — commit versus skip, and twin uniqueness -/

/-- **H2 (O1's mirror).** No leader block is both directly committed
and directly skipped: honest supporters and blamers together number at
most `n + fb`, and two `q`-quorums are more. Needs only
`n > 3·fb + 2·fc`. -/
theorem not_directSkip_of_directCommit (hne : HonestNoEquiv U)
    (hc : DirectCommit U L r) (hk : DirectSkip U L r) : False := by
  have := card_supporters_add_card_blames_le hne card_compl_honest_le (L := L) (n := r + 1)
  have h5 := H.card_validators
  unfold DirectCommit at hc
  unfold DirectSkip at hk
  unfold q at hc hk
  omega

/-- **Twin uniqueness for direct commits (O1′'s mirror).** Needs only
`n > 3·fb + 2·fc`. -/
theorem eq_of_directCommit (hne : HonestNoEquiv U) {L₁ L₂ : BlockId}
    (h₁ : DirectCommit U L₁ r) (h₂ : DirectCommit U L₂ r)
    (hcr : (U.block L₁).creator = (U.block L₂).creator) : L₁ = L₂ :=
  eq_of_card_supporters hne card_compl_honest_le hcr (n := r + 1)
    (by unfold DirectCommit at h₁ h₂; unfold q at h₁ h₂; have := H.card_validators; omega)

/-! ## H3 — a skipped leader cannot muster the indirect threshold -/

/-- **H3, the counting half.** A directly skipped leader's supporters —
anywhere in the universe — number at most `2·fb + fc`: supporters and
blamers together number at most `n + fb`, and the blamers are `q`. -/
theorem card_supporters_le_of_directSkip (hne : HonestNoEquiv U)
    (hk : DirectSkip U L r) :
    (supporters U L (r + 1)).card ≤ 2 * H.fb + H.fc := by
  have := card_supporters_add_card_blames_le hne card_compl_honest_le (L := L) (n := r + 1)
  have h5 := H.card_validators
  unfold DirectSkip at hk
  unfold q at hk
  omega

/-- **H3 (O2's mirror).** A directly skipped leader fails the indirect
test against every anchor, at every admissible threshold: its
supporters number at most `2·fb + fc`, below the interval's lower end.
This is where the lower half of admissibility is consumed. -/
theorem not_thickLink_of_directSkip (hne : HonestNoEquiv U)
    (hka : 2 * H.fb + H.fc + 1 ≤ k) (hk : DirectSkip U L r)
    (A : BlockId) : ¬ ThickLink k U A L r := by
  intro ht
  have h1 := Finset.card_le_card
    (coneSupports_subset_supporters (U := U) (A := A) (L := L) (r := r))
  have h2 := card_supporters_le_of_directSkip hne hk
  unfold ThickLink at ht
  omega

/-! ## H4 — link integrity: every anchor's cone is the certificate -/

private theorem thickLink_of_directCommit_aux (hne : HonestNoEquiv U)
    (hkb : k + 3 * H.fb + 2 * H.fc ≤ Fintype.card Validator)
    (h : DirectCommit U L r) :
    ∀ d, ∀ A, A ∈ U.ids → (U.block A).round = r + 2 + d →
      ThickLink k U A L r := by
  intro d
  induction d with
  | zero =>
      intro A hA hround
      -- the parent quorum meets the supporter quorum past the Byzantine
      -- class; each honest member's parent *is* its support block
      have hval := U.valid A hA
      have hq : (Fintype.card Validator - (H.fb + H.fc)) ≤
          (creatorsOf U.block (U.block A).refs).card := hval.quorum (by omega)
      have hsub : (creatorsOf U.block (U.block A).refs ∩
          supporters U L (r + 1)) ∩ Honest Validator ⊆
            coneSupports U A L r := by
        intro v hv
        obtain ⟨hvPS, hvH⟩ := Finset.mem_inter.mp hv
        obtain ⟨hvP, hvS⟩ := Finset.mem_inter.mp hvPS
        obtain ⟨p, hp, hpc⟩ := mem_creatorsOf.mp hvP
        obtain ⟨s, hs_ids, hs_round, hsL, hsc⟩ := mem_supporters.mp hvS
        have hp_ids : p ∈ U.ids := U.complete A hA p hp
        have hp_round : (U.block p).round = r + 1 := by
          have := U.round_of_mem_refs hA hp
          omega
        have hps : p = s :=
          hne.eq_of_creator_eq hp_ids hs_ids hvH hpc hsc (by omega)
        exact mem_coneSupports.mpr
          ⟨p, hp_ids, hp_round, hps ▸ hsL,
            mem_history_of_mem_refs hA hp, hpc⟩
      have h1 := Finset.card_union_add_card_inter
        (creatorsOf U.block (U.block A).refs) (supporters U L (r + 1))
      have h2 := Finset.card_le_univ
        (creatorsOf U.block (U.block A).refs ∪ supporters U L (r + 1))
      have h3 : (creatorsOf U.block (U.block A).refs ∩
          supporters U L (r + 1)).card ≤
            ((creatorsOf U.block (U.block A).refs ∩
              supporters U L (r + 1)) ∩ Honest Validator).card +
              H.byzantine.card := by
        refine le_trans (Finset.card_le_card (t :=
          (creatorsOf U.block (U.block A).refs ∩ supporters U L (r + 1)) ∩
            Honest Validator ∪ H.byzantine) ?_)
          (Finset.card_union_le _ _)
        intro v hv
        by_cases hvH : v ∈ Honest Validator
        · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hv, hvH⟩)
        · exact Finset.mem_union_right _ (by simpa [mem_honest] using hvH)
      have h4 := Finset.card_le_card hsub
      have h5 := H.card_byzantine
      unfold DirectCommit at h
      unfold q at h
      unfold ThickLink
      omega
  | succ d ih =>
      intro A hA hround
      obtain ⟨p, hp⟩ := U.refs_nonempty hA (by omega)
      have hp_ids : p ∈ U.ids := U.complete A hA p hp
      have hp_round : (U.block p).round = r + 2 + d := by
        have := U.round_of_mem_refs hA hp
        omega
      have := ih p hp_ids hp_round
      unfold ThickLink at this ⊢
      exact le_trans this (Finset.card_le_card
        (coneSupports_subset_of_reaches hA (Reaches.single hp)))

/-- **H4 (O3's mirror) — link integrity.** If `L` is directly
committed, every block from two rounds above it on carries at least `k`
distinct support authors in its cone, for every admissible `k`: one hop
is quorum intersection at `2q − n − fb = n − 3·fb − 2·fc ≥ k` — the
interval's upper end, consumed exactly here — and depth is cone
monotonicity. -/
theorem thickLink_of_directCommit (hne : HonestNoEquiv U)
    (hkb : k + 3 * H.fb + 2 * H.fc ≤ Fintype.card Validator)
    (h : DirectCommit U L r) {A : BlockId}
    (hA : A ∈ U.ids) (hround : r + 2 ≤ (U.block A).round) :
    ThickLink k U A L r :=
  thickLink_of_directCommit_aux hne hkb h ((U.block A).round - (r + 2)) A hA
    (by omega)

/-! ## H5 — a direct commit excludes every rival candidate -/

/-- **H5 (O4′'s mirror).** A directly committed block is the only
same-author block that can pass the indirect test at any anchor:
`q` supporters of `L₁` and `k` in-cone supporters of `L₂` overlap past
the Byzantine class — `q + k > n + fb` is the interval's lower end
again — and an honest overlap member supports two twins, which P2 and
honesty jointly forbid. -/
theorem eq_of_directCommit_of_thickLink (hne : HonestNoEquiv U)
    (hka : 2 * H.fb + H.fc + 1 ≤ k) {L₁ L₂ : BlockId}
    (h₁ : DirectCommit U L₁ r) (ht : ThickLink k U A L₂ r)
    (hcr : (U.block L₁).creator = (U.block L₂).creator) : L₁ = L₂ := by
  by_contra hd
  have hsub : supporters U L₁ (r + 1) ∩ coneSupports U A L₂ r ⊆
      H.byzantine := by
    intro v hv
    obtain ⟨hv₁, hv₂⟩ := Finset.mem_inter.mp hv
    have := not_mem_of_supports_two hne hd hcr hv₁ (coneSupports_subset_supporters hv₂)
    simpa [mem_honest] using this
  have h1 := Finset.card_union_add_card_inter
    (supporters U L₁ (r + 1)) (coneSupports U A L₂ r)
  have h2 := Finset.card_le_univ
    (supporters U L₁ (r + 1) ∪ coneSupports U A L₂ r)
  have h3 := Finset.card_le_card hsub
  have h4 := H.card_byzantine
  have h5 := H.card_validators
  unfold DirectCommit at h₁
  unfold q at h₁
  unfold ThickLink at ht
  omega

end Hybrid

end LeanDag
