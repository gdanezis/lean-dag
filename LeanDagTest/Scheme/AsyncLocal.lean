import LeanDag.Scheme.AsyncLocal.Proof
import LeanDagTest.Scheme.ReactiveHybrid
import LeanDag.Scheme.Async.Proof
/-!
# The family on a validator's own view, paced asynchronously, on data

The hybrid committee of `LeanDagTest/Scheme/ReactiveHybrid.lean`: three
replicas, replica `0` crashed, replicas `1` and `2` building every round
and referencing both blocks of the round below. Its timed run, with the
clock forgotten (`AsyncPace.ofPaceCore`), is an asynchronous run at
`q = 2`. Every leader block is safe, since every block of the round above
references it, so every slot commits on each live replica's own view from
some time on, and so does every window of one slot.

On the starving execution of four validators, one Byzantine, at the
Mahi-Mahi row of wave five (two buffer rounds), a uniform coin names a
leader whose slot commits on every honest validator's own view with
probability at least `(q − f)/n = 1/2`.
-/

namespace LeanDagTest

namespace Scheme

open LeanDag LeanDag.Scheme

attribute [local instance 2000] hySlots

/-- **The hybrid run, paced asynchronously at `q = 2`.** -/
def hyAsync (N : ℕ) : AsyncPace 2 (Uhy N) Thy N :=
  letI : Faults (Fin 3) := noFaults
  AsyncPace.ofPaceCore (hyReactive N).toPaceCore (hyReactive N).advancesAt

theorem hySlots_slotRound (k : ℕ) : hySlots.slotRound k = 3 * k := by simp

/-- **Every leader is safe**: the round above references its block. -/
theorem hy_safe (N k : ℕ) (hN : hySlots.slotRound k + 1 ≤ N) :
    hySlots.leader k ∈ safe hyP (Uhy N) k := by
  have hs := hySlots_slotRound k
  have hvo : hyP.voteOffset = 1 := by decide
  refine mem_safeAt.mpr ⟨by change _ ∈ (∅ : Finset (Fin 3))ᶜ; simp, 2 * (3 * k) + k % 2,
    ?_, ?_, ?_, ?_⟩
  · simp only [uhy_ids, Finset.mem_range]; omega
  · change (2 * (3 * k) + k % 2) / 2 = hySlots.slotRound k
    omega
  · exact Fin.ext (by
      simp only [uhy_block, hyBlock_creator_val]
      change _ = k % 2 + 1
      omega)
  · intro b _ hbr
    rw [hvo] at hbr
    have hbr' : b / 2 = hySlots.slotRound k + 1 := hbr
    exact Reaches.single (by
      change _ ∈ (hyBlock b).refs
      exact mem_hyBlock_refs.mpr (by omega))

/-- **Every slot commits on each live replica's own view**, from some time
on. -/
theorem hyAsync_commits (N k : ℕ) (hN : hySlots.slotRound k + 2 ≤ N) :
    (hyAsync N).EventuallyCommits hyP σH k :=
  AsyncLocal.safeCommits (Fin 3) ℕ Unit HybridValid (Hydrozoan.q (Fin 3))
    Hydrozoan.NonByzantine hyP σH (Uhy N) Thy N 2 (hyAsync N) k (by decide)
    (fun _ => ⟨by decide, by decide⟩) (by decide) (by decide)
    (by have : hyP.waveLength - 1 = 2 := rfl; omega) (hy_safe N k (by omega))

/-- **Every window of one slot commits on each live replica's own view**,
from some time on. -/
theorem hyAsync_commitsWithin (N : ℕ) :
    ∃ t, ∀ t', t ≤ t' → ∀ v (hv : v ∈ Thy), ∀ k,
      (schemeAnchored hyP σH).decisionRound (k + 1) ≤ N →
      ∃ k', k ≤ k' ∧ k' < k + 1 ∧ ∃ L, IsLeaderBlock (Uhy N) k' L ∧
        (schemeAnchored hyP σH).Decided (Uhy N) ((hyAsync N).viewAt hv t') k' (some L) :=
  AsyncLocal.commitsWithin (Fin 3) ℕ Unit HybridValid (Hydrozoan.q (Fin 3))
    Hydrozoan.NonByzantine hyP σH (Uhy N) Thy N 2 (hyAsync N) 1 (by decide)
    (fun _ => ⟨by decide, by decide⟩) (by decide) (by decide) fun k hk => by
      have hdec : (schemeAnchored hyP σH).decisionRound (k + 1) =
          hySlots.slotRound (k + 1) + (hyP.waveLength - 1) := rfl
      have : hyP.waveLength - 1 = 2 := rfl
      have h1 := hySlots_slotRound k
      have h2 := hySlots_slotRound (k + 1)
      exact ⟨k, le_rfl, by omega, hy_safe N k (by omega)⟩

/-- The starving execution's records are quorate at `q = 3`. -/
instance starveQuorate :
    Validity.Quorate (ValidAt (Validator := Fin 4) (BlockId := Lex (ℕ × Fin 4))
      (Payload := Unit) 3 (Clause.distinct.and Clause.selfParent)) 3 :=
  Validity.Quorate.of_validAt (by omega) fun _ _ => Iff.rfl

/-- **The coin's leader commits with probability at least `1/2`** on the
starving execution. -/
example : ((3 - 1 : ℕ) : ENNReal) / 4 ≤
    (PMF.uniformOfFintype (Fin 4)).toOuterMeasure
      {v | (Starve.starvePace (f := 1) (q := 3) (hqn := by omega) 4).EventuallyCommits
        (S := Slots.uniformSingle 1 one_pos fun _ => v) (Params.mahiMahi 5 4 1) leastSel 0} :=
  (AsyncLocal.coinLive (Fin 4) (Lex (ℕ × Fin 4)) Unit _ 3 (Starve.honestSet 4 1) 1
    (Params.mahiMahi 5 4 1) leastSel (Starve.record (by omega) 4) _ 4
    (Starve.starvePace (hqn := by omega) 4) (fun v => Slots.uniformSingle 1 one_pos fun _ => v)
    2 0 0 (by rw [Starve.card_compl_honestSet (by omega)])
    (by simp [Params.AsyncReady, Params.voteOffset, Params.mahiMahi])
    (by decide) (fun v => ⟨rfl, by simp⟩) (by decide)).2 (by omega)

end Scheme

end LeanDagTest

#print axioms LeanDag.Scheme.AsyncLocal.holds
