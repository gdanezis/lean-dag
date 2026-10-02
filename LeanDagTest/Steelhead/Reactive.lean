import LeanDag.Steelhead.Model.Reactive
import LeanDag.Steelhead.Helpers.MahiMahiPair.Liveness
import LeanDagTest.Reactive.Model
/-!
# Steelhead witnesses: the reactive discipline, inhabited

`ReactiveS` is the pacing that SH-MM6k and SH-BB6k assume, and this file shows it is not
vacuous: `ugrowReactiveS` instantiates it on `Ugrow`, at every wavelength function and every
choice of the rounds that carry the leader wait. The trunk and the leader-wait clause are the
core's reactive witness `ugrowReactive`, unchanged: builds at spacing `6` inside a timeout of `9`,
so no validator ever waits a timeout out. The certificate clause is Steelhead's own, over
Mahi-Mahi's vote through the cone rather than the core's direct reference, and it is discharged
by its reactive exit: `Ugrow`'s blocks reference the whole round below, so every block votes for
every block two rounds down through its parent, and every block two rounds above a leader block
certifies it.
-/

namespace LeanDagTest

open LeanDag LeanDag.Steelhead

attribute [local instance 2000] rrSlots

/-- In `Ugrow` a validator has one block per round. -/
theorem ugrow_unique {N L L' : ℕ} (_hL' : L' ∈ (Ugrow N).ids)
    (hr : ((Ugrow N).block L').round = ((Ugrow N).block L).round)
    (hc : ((Ugrow N).block L').creator = ((Ugrow N).block L).creator) : L' = L := by
  simp only [ugrow_block, rrBlock_round] at hr
  have hcv := congrArg Fin.val hc
  simp only [ugrow_block, rrBlock_creator_val] at hcv
  omega

/-- **Every block two rounds above a leader block certifies it, with Mahi-Mahi's vote.** Every
block of the round in between references the leader block, so it votes for it, and the
certifier references the whole of that round. -/
theorem ugrow_mm_certifies {N c L : ℕ} (hc : c ∈ (Ugrow N).ids) (hL : L ∈ (Ugrow N).ids)
    (hcr : ((Ugrow N).block c).round = ((Ugrow N).block L).round + 2) :
    MahiMahi.Certifies (Ugrow N) c L := by
  simp only [ugrow_ids, Finset.mem_range] at hc hL
  simp only [ugrow_block, rrBlock_round] at hcr
  change (Fintype.card (Fin 4) - Faults.f (Fin 4)) ≤ _
  have hsub : ({0, 1, 2, 3} : Finset (Fin 4)) ⊆
      creatorsOf (Ugrow N).block (carriedVotes (Ugrow N) (MahiMahi.Votes (Ugrow N)) c L) := by
    intro x _
    have hx4 := x.isLt
    refine mem_creatorsOf.mpr ⟨4 * (L / 4 + 1) + (x : ℕ), ?_, ?_⟩
    · refine mem_carriedVotes.mpr ⟨?_, ?_⟩
      · simp only [ugrow_block, mem_growBlock_refs]
        omega
      · refine MahiMahiPair.votes_of_reaches_of_unique
          (by simp only [ugrow_ids, Finset.mem_range]; omega)
          (by simp only [ugrow_ids, Finset.mem_range]; omega)
          (fun L' hL' hr hcr' => ugrow_unique hL' hr hcr') (Reaches.single ?_)
        simp only [ugrow_block, mem_growBlock_refs]
        omega
    · apply Fin.ext
      simp only [ugrow_block, rrBlock_creator_val]
      omega
  have hcard : ({0, 1, 2, 3} : Finset (Fin 4)).card = 4 := by decide
  have := Finset.card_le_card hsub
  have hf : Faults.f (Fin 4) = 1 := rfl
  have hn : Fintype.card (Fin 4) = 4 := rfl
  omega

/-- **The reactive discipline, inhabited.** Steelhead's `ReactiveS` on `Ugrow`, at any
wavelength function `w` and any rounds `waits`: the core's reactive witness for the trunk, the
deadline and the leader wait, and the reactive exit for the certificate wait. -/
def ugrowReactiveS (N : ℕ) (w : ℕ → ℕ) (waits : ℕ → Prop) :
    ReactiveS (Ugrow N) {1, 2, 3} N w waits :=
  { (ugrowReactive N).toPaceCore with
    built_lt := (ugrowReactive N).built_lt
    deadline := (ugrowReactive N).deadline
    vote_or_wait := fun v hv k _ hN hlead L hL c hc hcc hcr =>
      (ugrowReactive N).vote_or_wait v hv k hN hlead L hL c hc hcc hcr
    cert_or_wait := fun _ _ _ _ _ _ _ L hL c hc _ hcr =>
      Or.inl (ugrow_mm_certifies hc hL.1 (by rw [hcr, hL.2.1])) }

/-- The witness at Steelhead's own schedule shape: the leader wait at every round, wave `3`
throughout. -/
example (N : ℕ) : ReactiveS (Ugrow N) {1, 2, 3} N (fun _ => 3) (fun _ => True) :=
  ugrowReactiveS N _ _

end LeanDagTest

#print axioms LeanDagTest.ugrow_mm_certifies
#print axioms LeanDagTest.ugrowReactiveS
