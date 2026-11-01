import LeanDag.GC.Chop
import LeanDag.DoS.Exclusion
/-!
# The attested base: the inexact certificate

`garbage.md` §6, **G10**. A joining validator adopts a new genesis layer
from others rather than fetching the pruned prefix, and correct
presenters need not agree block-for-block on it, only on the correct
core: the certificate keeps a round-`G` block once `f + 1` distinct
authors attest it, an author's attestation being simply its own block
(D13, no signatures). Soundness and completeness give the sandwich:
everything kept has an honest attester, at any block record with at most
`f` validators outside its honest set, and nothing reliable is filtered,
at a record whose quorum `q` the reliable set `T` holds, with
`n + f + 1 ≤ 2q`. The backbone they rest on (`mem_history_of_correct`)
reads the record's quorum as the reliability `quorumReliability`.
-/

namespace LeanDag

section Record

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {P : Validity Validator BlockId Payload} {honest : Finset Validator}
variable {U : BlockRecord Validator BlockId Payload P honest}
variable {f t G : ℕ} {y : BlockId}

/-- The authors attesting `y` at round `t`: those with a round-`t` block
whose cone holds `y`. An author's block *is* its attestation. -/
def attesters (U : BlockRecord Validator BlockId Payload P honest) (t : ℕ)
    (y : BlockId) : Finset Validator :=
  creatorsOf U.block ((blocksAt U t).filter fun a => y ∈ history U a)

/-- Membership in `attesters`, unfolded: an attester is the author of a
round-`t` block whose history reaches `y`. -/
theorem mem_attesters {v : Validator} :
    v ∈ attesters U t y ↔
      ∃ a ∈ U.ids, (U.block a).round = t ∧ y ∈ history U a ∧
        (U.block a).creator = v := by
  unfold attesters
  simp only [mem_creatorsOf, Finset.mem_filter, mem_blocksAt]
  tauto

/-- **The inexact certificate**: the round-`G` blocks attested by more
than `f` distinct authors at round `t`. -/
def Base (U : BlockRecord Validator BlockId Payload P honest) (f t G : ℕ) :
    Finset BlockId :=
  (blocksAt U G).filter fun y => f + 1 ≤ (attesters U t y).card

/-- Membership in `Base`, unfolded: a round-`G` block attested by more
than `f` validators. -/
theorem mem_base :
    y ∈ Base U f t G ↔
      (y ∈ U.ids ∧ (U.block y).round = G) ∧
        f + 1 ≤ (attesters U t y).card := by
  unfold Base
  rw [Finset.mem_filter, mem_blocksAt]

/-- **The reliability a quorum gives**: a set `T` holding the record's
quorum `q`, with slack `n − q`, a minority since `n < 2q`. -/
def quorumReliability [Fintype Validator] (T : Finset Validator) {q : ℕ} (hT : q ≤ T.card)
    (hq : Fintype.card Validator < 2 * q) : Reliability Validator where
  correct := T
  slack := Fintype.card Validator - q
  covers := by
    have := Finset.card_add_card_compl T
    omega
  minority := by
    have := Finset.card_le_univ T
    omega

/-- **The backbone lemma.** After `R`, at a record whose quorum `q` the
set `T` holds, with `n < 2q`, the history of a block by a member of `T`
holds every block by a member of `T` of every round from `R` below it. -/
theorem mem_history_of_correct [Fintype Validator] [P.Mechanised] {q : ℕ} [P.Quorate q]
    {T : Finset Validator} (hT : q ≤ T.card) (hq : Fintype.card Validator < 2 * q) {R : ℕ}
    (hs : SynchronisedOn U T R) :
    ∀ d : ℕ, ∀ c ∈ U.ids, ∀ a ∈ U.ids,
      (U.block c).creator ∈ T → (U.block a).creator ∈ T →
      R ≤ (U.block a).round → (U.block a).round + 1 + d = (U.block c).round →
      a ∈ history U c :=
  mem_historyFrom_of_correct (rel := quorumReliability T hT hq) U.causal
    (fun b hb hr => by
      have h₁ := U.creators_quorum hb hr
      have h₂ := Finset.card_le_univ T
      show Fintype.card Validator - (Fintype.card Validator - q) ≤ _
      omega) hs

/-- **G10, soundness.** With at most `f` validators outside the honest
set, everything in the base has an honest attester, and so lies in an
honest cone. The adversary cannot smuggle fabrications into anyone's
base. -/
theorem exists_honest_attester_of_mem_base (hf : honestᶜ.card ≤ f) (hy : y ∈ Base U f t G) :
    ∃ a ∈ U.ids, (U.block a).round = t ∧ (U.block a).creator ∈ honest ∧ y ∈ history U a := by
  obtain ⟨-, hcard⟩ := mem_base.mp hy
  obtain ⟨v, hv, hvc⟩ := exists_mem_of_card hf hcard
  obtain ⟨a, ha, har, hya, hac⟩ := mem_attesters.mp hv
  exact ⟨a, ha, har, by rw [hac]; exact hvc, hya⟩

/-- A set holding the quorum `q`, with `n + f + 1 ≤ 2q`, has more than `f`
members. -/
theorem le_card_of_quorum [Fintype Validator] {q : ℕ} {T : Finset Validator}
    (hT : q ≤ T.card) (hq : Fintype.card Validator + f + 1 ≤ 2 * q) : f + 1 ≤ T.card := by
  have := Finset.card_le_univ T
  omega

/-- **G10, completeness.** Post-`R`, every reliable block of the layer is
in every reliable attestation (the backbone), so it clears the `f+1` bar
in *every* sample — the shared reliable layer is in every base, and the
adversary cannot filter it out. -/
theorem correct_mem_base [Fintype Validator] [P.Mechanised] {q : ℕ} [P.Quorate q]
    {T : Finset Validator} (hT : q ≤ T.card) (hq : Fintype.card Validator + f + 1 ≤ 2 * q)
    {R : ℕ} (hs : SynchronisedOn U T R) (hR : R ≤ G)
    (hGt : G < t) (hpop : PopulatedOn U T t) (hy : y ∈ U.ids)
    (hyr : (U.block y).round = G) (hyc : (U.block y).creator ∈ T) :
    y ∈ Base U f t G := by
  refine mem_base.mpr ⟨⟨hy, hyr⟩, ?_⟩
  have hsub : T ⊆ attesters U t y := by
    intro w hw
    obtain ⟨a, ha, hac, har⟩ := hpop w hw
    refine mem_attesters.mpr ⟨a, ha, har, ?_, hac⟩
    exact mem_history_of_correct hT (by omega) hs (t - G - 1) a ha y hy
      (by rw [hac]; exact hw) hyc (by omega) (by omega)
  have := Finset.card_le_card hsub
  have := le_card_of_quorum hT hq
  omega

end Record

end LeanDag
