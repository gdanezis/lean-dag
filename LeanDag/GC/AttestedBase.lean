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
`f` validators outside its honest set, and nothing correct is filtered,
on the core's universe.
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

end Record

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {U : BlockUniverse Validator BlockId Payload}
variable {t G : ℕ} {y : BlockId}

/-- **G10, completeness.** Post-`R`, every correct block of the layer is
in every correct attestation (the backbone), so it clears the `f+1` bar in
*every* sample — the shared correct layer `C` is in every base, and the
adversary cannot filter it out. -/
theorem correct_mem_base {R : ℕ} (hs : Synchronised U R) (hR : R ≤ G)
    (hGt : G < t) (hpop : Populated U t) (hy : y ∈ U.ids)
    (hyr : (U.block y).round = G)
    (hyc : (U.block y).creator ∈ (Correct : Finset Validator)) :
    y ∈ Base U F.f t G := by
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
