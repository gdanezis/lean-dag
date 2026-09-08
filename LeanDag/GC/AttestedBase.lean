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
everything kept has a correct attester, and nothing correct is filtered.
-/

namespace LeanDag

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {U : BlockUniverse Validator BlockId Payload}
variable {t G : ℕ} {y : BlockId}

/-- The authors attesting `y` at round `t`: those with a round-`t` block
whose cone holds `y`. An author's block *is* its attestation. -/
def attesters (U : BlockUniverse Validator BlockId Payload) (t : ℕ)
    (y : BlockId) : Finset Validator :=
  creatorsOf U.block ((blocksAt U t).filter fun a => y ∈ history U a)

/-- Membership in `attesters`, unfolded: an attester is a correct author of a round-`t` block whose history reaches `y`. -/
theorem mem_attesters {v : Validator} :
    v ∈ attesters U t y ↔
      ∃ a ∈ U.ids, (U.block a).round = t ∧ y ∈ history U a ∧
        (U.block a).creator = v := by
  unfold attesters
  simp only [mem_creatorsOf, Finset.mem_filter, mem_blocksAt]
  tauto

/-- **The inexact certificate**: the round-`G` blocks attested by more
than `f` distinct authors at round `t`. -/
def Base (U : BlockUniverse Validator BlockId Payload) (t G : ℕ) :
    Finset BlockId :=
  (blocksAt U G).filter fun y => F.f + 1 ≤ (attesters U t y).card

/-- Membership in `Base`, unfolded: a round-`G` block attested by at least `f+1` validators. -/
theorem mem_base :
    y ∈ Base U t G ↔
      (y ∈ U.ids ∧ (U.block y).round = G) ∧
        F.f + 1 ≤ (attesters U t y).card := by
  unfold Base
  rw [Finset.mem_filter, mem_blocksAt]

/-- **G10, soundness.** Everything in the base has a correct attester —
`f+1` authors always include one — and so lies in a correct cone. The
adversary cannot smuggle fabrications into anyone's base. -/
theorem exists_correct_attester_of_mem_base (hy : y ∈ Base U t G) :
    ∃ a ∈ U.ids, (U.block a).round = t ∧
      (U.block a).creator ∈ (Correct : Finset Validator) ∧
      y ∈ history U a := by
  obtain ⟨-, hcard⟩ := mem_base.mp hy
  obtain ⟨v, hv, hvc⟩ := exists_correct_of_card hcard
  obtain ⟨a, ha, har, hya, hac⟩ := mem_attesters.mp hv
  exact ⟨a, ha, har, by rw [hac]; exact hvc, hya⟩

/-- **G10, completeness.** Post-`R`, every correct block of the layer is
in every correct attestation (the backbone), so it clears the `f+1` bar in
*every* sample — the shared correct layer `C` is in every base, and the
adversary cannot filter it out. -/
theorem correct_mem_base {R : ℕ} (hs : Synchronised U R) (hR : R ≤ G)
    (hGt : G < t) (hpop : Populated U t) (hy : y ∈ U.ids)
    (hyr : (U.block y).round = G)
    (hyc : (U.block y).creator ∈ (Correct : Finset Validator)) :
    y ∈ Base U t G := by
  refine mem_base.mpr ⟨⟨hy, hyr⟩, ?_⟩
  have hsub : (Correct : Finset Validator) ⊆ attesters U t y := by
    intro w hw
    obtain ⟨a, ha, hac, har⟩ := hpop w hw
    refine mem_attesters.mpr ⟨a, ha, har, ?_, hac⟩
    exact mem_history_of_correct hs (t - G - 1) a ha y hy
      (by rw [hac]; exact hw) hyc (by omega) (by omega)
  have h2 := two_f_add_one_le_card_correct (Validator := Validator)
  have := Finset.card_le_card hsub
  omega

end LeanDag
