import LeanDag.DoS.Novelty
import LeanDag.GC.Bootstrap
import LeanDag.Mysticeti.Properties
/-!
# The novelty budget delivers

`Properties/Deliver.lean` states what a view-level mechanism owes, and
this is the witness. `Properties.Delivers`, holding every block of the
universe, has no model but `View.full`: an equivocator's dropped pair
already breaks it. `Properties.CoversOn`, the blocks of a reliable set
over a window, is what `Delivery.accepts_correct` and
`EventuallyDelivers` supply — after the settling round a correct
validator holds and accepts every correct block — with no appeal to the
novelty budget. `directCommitIn_of_certifiesAt` then reaches the verdict
from that coverage.
-/

namespace LeanDag

namespace DoS

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {U : BlockUniverse Validator BlockId Payload}
variable {D : Delivery U} {v : Validator} {n : ℕ}

/-- **A retained store is a view.** It holds only real blocks
(`viewUpto_subset_ids`) and is closed under references
(`mem_viewUpto_of_mem_refs`), which are the two things a view is. -/
def View.ofViewUpto (D : Delivery U) (v : Validator) (n : ℕ) :
    View Validator BlockId Payload U where
  ids := viewUpto D v n
  subset_ids := viewUpto_subset_ids
  complete := fun _ hi _ hj => mem_viewUpto_of_mem_refs hi hj

@[simp] theorem View.ofViewUpto_ids : (View.ofViewUpto D v n).ids = viewUpto D v n := rfl

/-- **What a rate-limited store holds.** After the settling round a
correct validator's store contains every correct block up to its own
round. -/
theorem correct_mem_viewUpto {R : ℕ} (hED : EventuallyDelivers D R)
    (hv : v ∈ (Correct : Finset Validator)) {a : BlockId} (ha : a ∈ U.ids)
    (hac : (U.block a).creator ∈ (Correct : Finset Validator))
    (hlo : R ≤ (U.block a).round) (hhi : (U.block a).round ≤ n) :
    a ∈ viewUpto D v n := by
  have hheld : a ∈ D.held v (U.block a).round :=
    hED (U.block a).round hlo v hv a ha rfl hac
  have hacc : a ∈ D.accepted v (U.block a).round :=
    D.accepts_correct v hv (U.block a).round a hheld hac
  exact history_subset_viewUpto hhi hacc ((mem_history_iff ha).mpr Relation.ReflTransGen.refl)

/-- **The witness.** The novelty budget's stores cover the correct
validators from the settling round on, in the sense `Properties.DeliversOn`
names. -/
theorem deliversOn_viewUpto {R : ℕ} (hED : EventuallyDelivers D R)
    (hv : v ∈ (Correct : Finset Validator)) :
    Properties.DeliversOn (MysticetiProperties.mysticetiRule (Payload := Payload))
      (fun t => View.ofViewUpto D v t) (Correct : Finset Validator) R :=
  fun hi => ⟨hi, fun a ha hac hlo hhi => correct_mem_viewUpto hED hv ha hac hlo hhi⟩

/-- **A rate-limited validator commits.** Given a reliable quorum whose
decision-round blocks certify `L`, a store that has settled reaches the
direct commit. -/
theorem directCommitIn_viewUpto [S : Slots Validator] {R r : ℕ} {L : BlockId}
    {T : Finset Validator} (hED : EventuallyDelivers D R)
    (hv : v ∈ (Correct : Finset Validator)) (hT : T ⊆ (Correct : Finset Validator))
    (hcard : quorumCard Validator ≤ T.card) (hR : R ≤ r + 2) (hn : r + 2 ≤ n)
    (hpop2 : PopulatedOn U T (r + 2)) (hc : CertifiesAt U T r L) :
    DirectCommitIn U (View.ofViewUpto D v n) L r :=
  directCommitIn_of_certifiesAt hcard hpop2
    (fun b hb hbc hbr => correct_mem_viewUpto hED hv hb (hT hbc) (by omega) (by omega)) hc

end DoS

end LeanDag
