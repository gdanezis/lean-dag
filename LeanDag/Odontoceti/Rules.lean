import LeanDag.Mysticeti.Rule
import LeanDag.Common.History
import LeanDag.Common.Rules
/-!
# Odontoceti: the two-round rule layer

`odontoceti.md` §3, OP1–OP2. The decision primitives of the two-round
protocol and the arithmetic core behind them — O1, O1′, O2, O3, O4′.

The DAG layer is consumed as-is: at `n ≥ 5f+1` the Odontoceti quorums
are `n − f`, which is literally what every existing definition uses, so
`supporters`/`blames` *are* the protocol's support/blame and the
universe machinery applies unchanged. Everything here is stated at the
generalized thresholds — direct rules at `n − f`, the indirect test at
`n − 3f` — which specialize to the thesis's `4f+1` / `2f+1` at the
boundary `n = 5f+1`.

Where each `f` is used, in one place:

* **O1** (commit vs skip) and **O1′** (twin uniqueness for direct
  commits) need only `n ≥ 3f+1`: two `n−f` quorums over `n` authors
  share `n−2f ≥ f+1`, all of whom must be equivocators.
* **O3** (propagation — the heart): `n−f` supports at the decision
  round put `n−3f` of the *support blocks* in every deeper cone — the
  parent quorum meets the supporter set in `n−2f` authors, of whom up
  to `f` are Byzantine equivocators whose referenced block may be a
  non-supporting twin. Cone monotonicity then carries the bound to any
  depth. Every anchor's cone *is* the certificate.
* **O2** (skip vs indirect commit): a directly skipped leader's
  supporters number `≤ 2f` — by the **exact complement identity**
  `|Correct| = n − |byzantine|`; the naive `|Correct| ≤ n` bounding
  yields `3f` and dies at the boundary — and `2f < n−3f` is exactly
  `n ≥ 5f+1`. This is where the fifth `f` is used.
* **O4′** (a direct commit excludes every rival): `n−f` supports for
  `L₁` and `n−3f` in-cone supports for a same-author `L₂` overlap in
  `≥ n−5f ≥ 1` correct authors, who cannot support two twins
  (`distinct_creators`) — the other place `n ≥ 5f+1` bites, and what
  replaces Mysticeti's M5′ in the direct-vs-indirect crossings.
-/

namespace LeanDag

/-- The Odontoceti committee: `n ≥ 5f+1`. An extension of `Faults`, so
every existing theorem applies to the same types unchanged; the new
bound is consumed only where the two-round arithmetic needs it. -/
class Faults5 (Validator : Type*) [Fintype Validator] [DecidableEq Validator]
    extends Faults Validator where
  /-- There are at least `5f+1` validators. -/
  card_validators5 : 5 * f + 1 ≤ Fintype.card Validator

namespace Odontoceti

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults5 Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {U : BlockUniverse Validator BlockId Payload}
variable {L A : BlockId} {r : ℕ}

/-! ## The direct rules

Support and blame are the existing `supporters`/`blames` — a block
supports a leader block iff it references it as a parent. The decision
round of a leader at round `r` is `r+1`; there is no certificate
round. -/

/-- **Direct commit**: a quorum of distinct authors support `L` at its
decision round. -/
def DirectCommit (U : BlockUniverse Validator BlockId Payload)
    (L : BlockId) (r : ℕ) : Prop :=
  quorumCard Validator ≤ (supporters U L (r + 1)).card

/-- **Direct skip**: a quorum of distinct authors blame `L` at its
decision round. -/
def DirectSkip (U : BlockUniverse Validator BlockId Payload)
    (L : BlockId) (r : ℕ) : Prop :=
  quorumCard Validator ≤ (blames U L (r + 1)).card

instance : Decidable (DirectCommit U L r) :=
  inferInstanceAs (Decidable (_ ≤ _))

instance : Decidable (DirectSkip U L r) :=
  inferInstanceAs (Decidable (_ ≤ _))

/-! ## The indirect test -/

/-- The authors of decision-round support blocks for `L` in `A`'s cone,
by distinct authors — the count equivocation cannot inflate. -/
abbrev coneSupports (U : BlockUniverse Validator BlockId Payload)
    (A L : BlockId) (r : ℕ) : Finset Validator :=
  coneSupporters U A L (r + 1)

/-- **The indirect test** (the thesis's ThickLink): at least `n − 3f`
distinct authors of support blocks for `L` in the anchor's cone. At
`n = 5f+1` this is the thesis's `2f+1`. -/
def ThickLink (U : BlockUniverse Validator BlockId Payload)
    (A L : BlockId) (r : ℕ) : Prop :=
  coneLink (Fintype.card Validator - 3 * F.f) U A L r

instance : Decidable (ThickLink U A L r) :=
  inferInstanceAs (Decidable (_ ≤ _))

/-! ## O1 — commit versus skip, and twin uniqueness -/

/-- **O1 (thesis Lemma 1).** No leader block is both directly committed
and directly skipped: supporters and blamers together number at most
`n + f`, and two quorums are more. Needs only `n ≥ 3f+1`. -/
theorem not_directSkip_of_directCommit (hc : DirectCommit U L r)
    (hk : DirectSkip U L r) : False := by
  have := card_supporters_add_card_blames_le U.noEquivOn_honest card_compl_correct_le
    (L := L) (n := r + 1)
  have h5 := F.card_validators
  unfold DirectCommit at hc
  unfold DirectSkip at hk
  omega

/-- **O1′ (M5 analogue).** Two directly committed blocks by one author
at one round are equal: their support quorums together exceed `n + f`.
Needs only `n ≥ 3f+1`. -/
theorem eq_of_directCommit {L₁ L₂ : BlockId}
    (h₁ : DirectCommit U L₁ r) (h₂ : DirectCommit U L₂ r)
    (hcr : (U.block L₁).creator = (U.block L₂).creator) : L₁ = L₂ :=
  eq_of_card_supporters U.noEquivOn_honest card_compl_correct_le hcr (n := r + 1)
    (by unfold DirectCommit at h₁ h₂; have := F.card_validators; omega)

/-! ## O2 — a skipped leader cannot muster the indirect threshold -/

/-- **O2, the counting half.** A directly skipped leader's supporters —
anywhere in the universe — number at most `2f`: supporters and blamers
together number at most `n + f`, and the blamers are `n − f`. -/
theorem card_supporters_le_of_directSkip (hk : DirectSkip U L r) :
    (supporters U L (r + 1)).card ≤ 2 * F.f := by
  have := card_supporters_add_card_blames_le U.noEquivOn_honest card_compl_correct_le
    (L := L) (n := r + 1)
  have h5 := F.card_validators
  unfold DirectSkip at hk
  omega

/-- **O2 (thesis Lemma 2).** A directly skipped leader fails the
indirect test against **every** anchor: `≤ 2f < n − 3f`. This is where
`n ≥ 5f+1` is used. -/
theorem not_thickLink_of_directSkip (hk : DirectSkip U L r)
    (A : BlockId) : ¬ ThickLink U A L r := by
  intro ht
  have h1 := Finset.card_le_card
    (coneSupporters_subset_supporters (U := U) (A := A) (L := L) (n := r + 1))
  have h2 := card_supporters_le_of_directSkip hk
  have h5 := F.card_validators5
  unfold ThickLink coneLink at ht
  omega

/-! ## O3 — propagation: every anchor's cone is the certificate -/

private theorem thickLink_of_directCommit_aux (h : DirectCommit U L r) :
    ∀ d, ∀ A, A ∈ U.ids → (U.block A).round = r + 2 + d →
      ThickLink U A L r := by
  intro d
  induction d with
  | zero =>
      intro A hA hround
      -- the parent quorum meets the supporter quorum in `n−2f` authors,
      -- of whom the `≥ n−3f` correct ones put their (unique, hence
      -- supporting) block into `A`'s cone
      have hval := U.valid A hA
      have hq : quorumCard Validator ≤
          (creatorsOf U.block (U.block A).refs).card := hval.quorum (by omega)
      have hsub : (creatorsOf U.block (U.block A).refs ∩
          supporters U L (r + 1)) ∩ (Correct : Finset Validator) ⊆
            coneSupports U A L r := by
        intro v hv
        obtain ⟨hvPS, hvC⟩ := Finset.mem_inter.mp hv
        obtain ⟨hvP, hvS⟩ := Finset.mem_inter.mp hvPS
        obtain ⟨p, hp, hpc⟩ := mem_creatorsOf.mp hvP
        obtain ⟨q, hq_ids, hq_round, hqL, hqc⟩ := mem_supporters.mp hvS
        have hp_ids : p ∈ U.ids := U.complete A hA p hp
        have hp_round : (U.block p).round = r + 1 := by
          have := U.round_of_mem_refs hA hp
          omega
        have hpq : p = q :=
          U.eq_of_creator_eq hp_ids hq_ids hvC hpc hqc (by omega)
        exact mem_coneSupporters.mpr
          ⟨p, hp_ids, hp_round, hpq ▸ hqL,
            mem_history_of_mem_refs hA hp, hpc⟩
      have h1 := Finset.card_union_add_card_inter
        (creatorsOf U.block (U.block A).refs) (supporters U L (r + 1))
      have h2 := Finset.card_le_univ
        (creatorsOf U.block (U.block A).refs ∪ supporters U L (r + 1))
          -- intersect with `Correct`: lose at most `|byzantine| ≤ f`
      have h3 : (creatorsOf U.block (U.block A).refs ∩
          supporters U L (r + 1)).card ≤
            ((creatorsOf U.block (U.block A).refs ∩
              supporters U L (r + 1)) ∩ (Correct : Finset Validator)).card +
              F.byzantine.card := by
        refine le_trans (Finset.card_le_card (t :=
          (creatorsOf U.block (U.block A).refs ∩ supporters U L (r + 1)) ∩
            (Correct : Finset Validator) ∪ F.byzantine) ?_)
          (Finset.card_union_le _ _)
        intro v hv
        by_cases hvC : v ∈ (Correct : Finset Validator)
        · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hv, hvC⟩)
        · exact Finset.mem_union_right _ (by simpa [mem_correct] using hvC)
      have h4 := Finset.card_le_card hsub
      have h5 := F.card_byzantine
      unfold DirectCommit at h
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

/-- **O3 (thesis Lemma 3) — propagation, the heart.** If `L` is
directly committed, then **every** block from two rounds above it on —
Byzantine-authored included, validity is structural — carries at least
`n − 3f` distinct authors of support blocks in its cone. One hop is
quorum intersection minus the twin discount; depth is cone
monotonicity. Every anchor's cone *is* the certificate. -/
theorem thickLink_of_directCommit (h : DirectCommit U L r) {A : BlockId}
    (hA : A ∈ U.ids) (hround : r + 2 ≤ (U.block A).round) :
    ThickLink U A L r :=
  thickLink_of_directCommit_aux h ((U.block A).round - (r + 2)) A hA
    (by omega)

/-! ## O4′ — a direct commit excludes every rival candidate -/

/-- **O4′.** A directly committed block is the **only** same-author
block that can pass the indirect test, at any anchor: `n−f` supporters
of `L₁` and `n−3f` in-cone supporters of `L₂` would overlap in
`≥ n−5f ≥ 1` correct authors, each supporting two twins — impossible.
The second place `n ≥ 5f+1` bites, and the replacement for Mysticeti's
M5′ in every direct-versus-indirect crossing. -/
theorem eq_of_directCommit_of_thickLink {L₁ L₂ : BlockId}
    (h₁ : DirectCommit U L₁ r) (ht : ThickLink U A L₂ r)
    (hcr : (U.block L₁).creator = (U.block L₂).creator) : L₁ = L₂ := by
  by_contra hne
  have hsub : supporters U L₁ (r + 1) ∩ coneSupports U A L₂ r ⊆
      F.byzantine := by
    intro v hv
    obtain ⟨hv₁, hv₂⟩ := Finset.mem_inter.mp hv
    have := not_mem_of_supports_two U.noEquivOn_honest hne hcr hv₁
      (coneSupporters_subset_supporters hv₂)
    simpa [mem_correct] using this
  have h1 := Finset.card_union_add_card_inter
    (supporters U L₁ (r + 1)) (coneSupports U A L₂ r)
  have h2 := Finset.card_le_univ
    (supporters U L₁ (r + 1) ∪ coneSupports U A L₂ r)
  have h3 := Finset.card_le_card hsub
  have h4 := F.card_byzantine
  have h5 := F.card_validators5
  unfold DirectCommit at h₁
  unfold ThickLink coneLink coneSupports at *
  omega

end Odontoceti

end LeanDag
