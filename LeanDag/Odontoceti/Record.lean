import LeanDag.Properties.Record
import LeanDag.Odontoceti.Properties
import LeanDag.Properties.Arcs.SafeSkip
import LeanDag.Mysticeti.Record
/-!
# Odontoceti on the record

The witness that Odontoceti runs on the core's universes, from which the cut, the copy fill and
re-genesis are the record's own and every verdict cell is
`Properties/Arcs/Record.lean` at this instance.
-/

namespace LeanDag

namespace OdontocetiProperties

open LeanDag.MysticetiProperties
open LeanDag.Properties
open LeanDag.Properties.Arcs

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}

section OdontocetiRecord

variable [Faults5 Validator] {B : Type} [LinearOrder B]

/-- **Odontoceti's carrier, read as block records**: the core's, at its
fault model. -/
def onRecord :
    (OdontocetiProperties.odontocetiRule (Validator := Validator) (BlockId := B)
      (Payload := Payload)).OnRecord ValidWrt (Correct : Finset Validator) BlockRecord.Any where
  toRec := fun U => U
  inv := fun _ => True.intro
  ofRec := fun W _ => W
  ids_to := fun _ => rfl
  block_to := fun _ => rfl
  ids_of := fun _ _ => rfl
  block_of := fun _ _ => rfl
  toRec_ofRec := fun _ _ => rfl
  toView := fun V => V
  ofView := fun V => V
  viewIds_to := fun _ => rfl
  viewIds_of := fun _ => rfl

end OdontocetiRecord

/-! ### The prompt skip, for Odontoceti

The fill's verdict cells are `Arcs/Record.lean` at `OdontocetiProperties.onRecord`;
what is stated here is the prompt skip, which reads the rule's
`SkipsUnsupported`. -/

section Odontoceti

variable [Faults5 Validator] {B : Type} [LinearOrder B]
variable {W : BlockUniverse Validator B Payload}

/-- **SS3 for Odontoceti**: the slot the recovering replica leads at a
gap round is skipped at once, from its `SkipsUnsupported`. -/
theorem decided_none_fresh_odontoceti [S : Slots Validator] (sk : SkipMsg W)
    {V : View Validator B Payload W} {T : Finset Validator} {k : ℕ}
    (hcard : quorumCard Validator ≤ T.card)
    (hlead : S.leader k = sk.v1) (hk1 : sk.r0 < S.slotRound k) (hk2 : S.slotRound k ≤ sk.r)
    (hpres : PresentAt (OdontocetiProperties.odontocetiRule (Payload := Payload)) V T
      (S.slotRound k + 1)) :
    Odontoceti.Decided (U := sk.skipFill) (sk.liftView V) k none :=
  decided_none_of_novel OdontocetiProperties.skipsUnsupported
    (extends_of_skipFill (OdontocetiProperties.odontocetiRule (Payload := Payload)) sk
      (U := W) (U' := sk.skipFill) rfl rfl rfl rfl) S hcard
    (fun v hv => by
      obtain ⟨c, hcV, hcc, hcr⟩ := hpres v hv
      have hcU : c ∈ W.ids := V.subset_ids hcV
      refine ⟨c, hcV, ?_, ?_⟩
      · show (sk.skipFill.block c).creator = v
        rw [sk.skipFill_block_old hcU]; exact hcc
      · show (sk.skipFill.block c).round = S.slotRound k + 1
        rw [sk.skipFill_block_old hcU]; exact hcr)
    (fun L hL => candidates_fresh sk hlead hk1 hk2 hL)
    (fun c hcV _ _ => V.subset_ids hcV)

/-- **And it conflicts with no verdict.** -/
theorem decided_none_fresh_agree_odontoceti [S : Slots Validator] (sk : SkipMsg W)
    {V : View Validator B Payload W} {T : Finset Validator} {k : ℕ}
    (hcard : quorumCard Validator ≤ T.card)
    (hlead : S.leader k = sk.v1) (hk1 : sk.r0 < S.slotRound k) (hk2 : S.slotRound k ≤ sk.r)
    (hpres : PresentAt (OdontocetiProperties.odontocetiRule (Payload := Payload)) V T
      (S.slotRound k + 1))
    {U'' : BlockUniverse Validator B Payload}
    (he' : Extends (OdontocetiProperties.odontocetiRule (Payload := Payload)) sk.skipFill U'')
    {V'' Y : View Validator B Payload U''} (hsub : (sk.liftView V).ids ⊆ V''.ids)
    {v : Option B} (hY : Odontoceti.Decided U'' Y k v) : v = none :=
  (decided_agree_extends OdontocetiProperties.agree
    (Persist.of_banded OdontocetiProperties.banded) he' (V := sk.liftView V) (V' := V'') hsub
    (decided_none_fresh_odontoceti sk hcard hlead hk1 hk2 hpres) hY).symm

end Odontoceti

end OdontocetiProperties

end LeanDag
