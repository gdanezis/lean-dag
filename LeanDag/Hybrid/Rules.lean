import LeanDag.Hybrid.Faults
import LeanDag.Mysticeti.Rule
import LeanDag.Common.History
import LeanDag.Common.Rules
/-!
# The hybrid two-round rules, and the arithmetic core

**A commit rule** (`Protocols`). Byzantine and crash faults kept
apart, on the core's universes under the invariant `HonestNoEquiv`.
The rule is `hybridAnchored`; the carrier and properties are
`Properties.lean`; the record witness, the self-referencing fill and
the prompt skip are `Record.lean`.

The Odontoceti rules at the hybrid thresholds: direct rules count
`q = n − fb − fc` authors, and `ThickLink k` is admissible for
`2fb + fc + 1 ≤ k ≤ n − 3fb − 2fc`, nonempty exactly at
`n ≥ 5fb + 3fc + 1`. Every safety theorem threads `HonestNoEquiv`,
discounting against `Honest` (`n − fb`) while quorums are taken against
`n − fb − fc` — the one difference from the pure-Byzantine arithmetic.
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
/-- The tight indirect threshold. -/
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

/-- The authors of decision-round support blocks for `L` in `A`'s cone,
by distinct authors. -/
abbrev coneSupports (U : BlockUniverse Validator BlockId Payload)
    (A L : BlockId) (r : ℕ) : Finset Validator :=
  coneSupporters U A L (r + 1)

/-- **The indirect test** at threshold `k`: at least `k` distinct
authors of support blocks in the anchor's cone. -/
def ThickLink (k : ℕ) (U : BlockUniverse Validator BlockId Payload)
    (A L : BlockId) (r : ℕ) : Prop :=
  coneLink k U A L r

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
    (coneSupporters_subset_supporters (U := U) (A := A) (L := L) (n := r + 1))
  have h2 := card_supporters_le_of_directSkip hne hk
  unfold ThickLink coneLink at ht
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
        exact mem_coneSupporters.mpr
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
      unfold ThickLink coneLink coneSupports at *
      omega
  | succ d ih =>
      intro A hA hround
      obtain ⟨p, hp⟩ := U.refs_nonempty hA (by omega)
      have hp_ids : p ∈ U.ids := U.complete A hA p hp
      have hp_round : (U.block p).round = r + 2 + d := by
        have := U.round_of_mem_refs hA hp
        omega
      have := ih p hp_ids hp_round
      unfold ThickLink coneLink at this ⊢
      exact le_trans this (Finset.card_le_card
        (coneSupporters_subset_of_reaches hA (Reaches.single hp)))

/-- **H4 (O3's mirror) — link integrity.** If `L` is directly
committed, every block two or more rounds above it carries at least `k`
distinct support authors in its cone: one hop is quorum intersection at
`n − 3fb − 2fc ≥ k`, the interval's upper end; depth is cone
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
same-author block that can pass the indirect test at any anchor: `q`
supporters of `L₁` and `k` in-cone supporters of `L₂` overlap past the
Byzantine class, and an honest overlap member supporting two twins is
what P2 and honesty jointly forbid. -/
theorem eq_of_directCommit_of_thickLink (hne : HonestNoEquiv U)
    (hka : 2 * H.fb + H.fc + 1 ≤ k) {L₁ L₂ : BlockId}
    (h₁ : DirectCommit U L₁ r) (ht : ThickLink k U A L₂ r)
    (hcr : (U.block L₁).creator = (U.block L₂).creator) : L₁ = L₂ := by
  by_contra hd
  have hsub : supporters U L₁ (r + 1) ∩ coneSupports U A L₂ r ⊆
      H.byzantine := by
    intro v hv
    obtain ⟨hv₁, hv₂⟩ := Finset.mem_inter.mp hv
    have := not_mem_of_supports_two hne hd hcr hv₁ (coneSupporters_subset_supporters hv₂)
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
  unfold ThickLink coneLink coneSupports at *
  omega

end Hybrid

end LeanDag
