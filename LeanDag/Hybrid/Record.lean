import LeanDag.Properties.Arcs.Record
import LeanDag.Integration.Preservation
import LeanDag.Hybrid.Properties
/-!
# Garbage collection, crash recovery and re-genesis for Hybrid

Hybrid's universe is the core's record under `HonestNoEquiv`, mechanised
in `Integration/Preservation.lean`, so the carrier reads as records
under it and every mechanism cell is `Arcs/Record.lean` at that
instance. Beyond the constructions, this file states the prompt skip
from Hybrid's `SkipsUnsupported`.
-/

namespace LeanDag

namespace HybridProperties

open LeanDag.Properties LeanDag.Properties.Arcs LeanDag.Integration

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [H : HybridFaults Validator]
variable {BlockId : Type} [LinearOrder BlockId] {Payload : Type}
variable {S : Slots Validator} {G d : ℕ} {kt : ℕ}

/-- **Hybrid's carrier, on the record**: the identity maps, under
`HonestNoEquiv`. -/
def onRecord :
    (HybridProperties.hybridRule (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload) kt).OnRecord ValidWrt (Correct : Finset Validator) HonestNoEquiv where
  toRec := fun U => U.val
  inv := fun U => U.property
  ofRec := fun W h => ⟨W, h⟩
  ids_to := fun _ => rfl
  block_to := fun _ => rfl
  ids_of := fun _ _ => rfl
  block_of := fun _ _ => rfl
  toView := fun V => V
  ofView := fun V => V
  viewIds_to := fun _ => rfl
  viewIds_of := fun _ => rfl

variable {U : (HybridProperties.hybridRule (Validator := Validator) (BlockId := BlockId)
  (Payload := Payload) kt).Universe}

/-- **The fill, at Hybrid's carrier**: the core's self-referencing fill
through `onRecord`, with `honestNoEquiv_fill` as the invariant. -/
def fill (U : (HybridProperties.hybridRule (Validator := Validator)
    (BlockId := BlockId) (Payload := Payload) kt).Universe) (sk : SkipMsg U.val) :
    (HybridProperties.hybridRule (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload) kt).Universe :=
  onRecord.fill U sk (sk.selfBlocks U.val.complete)
    (fun _ hk1 hk2 => sk.fillBlock_valid hk1 hk2) (honestNoEquiv_fill sk _ _ U.property)

/-- **The fill is an extension of Hybrid's carrier.** -/
theorem extends_fill (sk : SkipMsg U.val) :
    Extends (HybridProperties.hybridRule (Validator := Validator) (BlockId := BlockId)
        (Payload := Payload) kt) U (fill U sk) :=
  onRecord.extends_fill

/-! ## Promptness: the fill cannot conjure a commit, for Hybrid -/

/-- **SS3 for Hybrid**, from its `SkipsUnsupported`: the slot the
recovering replica leads at a gap round is skipped at once. -/
theorem decided_none_fresh {U : (HybridProperties.hybridRule (Validator := Validator)
    (BlockId := BlockId) (Payload := Payload) kt).Universe} (sk : SkipMsg U.val)
    {V : View Validator BlockId Payload U.val} {T : Finset Validator} {k : ℕ}
    (hq : Hybrid.q Validator ≤ T.card)
    (hlead : S.leader k = sk.v1) (hk1 : sk.r0 < S.slotRound k) (hk2 : S.slotRound k ≤ sk.r)
    (hpres : PresentAt (HybridProperties.hybridRule (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload) kt) V T (S.slotRound k + 1)) :
    (HybridProperties.hybridRule (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload) kt).Decided S (U := fill U sk) (sk.liftView V) k none :=
  decided_none_of_novel (HybridProperties.skipsUnsupported kt) (extends_fill sk) S hq
    (fun v hv => by
      obtain ⟨c, hcV, hcc, hcr⟩ := hpres v hv
      have hcU : c ∈ U.val.ids := V.subset_ids hcV
      refine ⟨c, hcV, ?_, ?_⟩
      · show (sk.skipFill.block c).creator = v
        rw [sk.skipFill_block_old hcU]; exact hcc
      · show (sk.skipFill.block c).round = S.slotRound k + 1
        rw [sk.skipFill_block_old hcU]; exact hcr)
    (fun L hL => candidates_fresh (S := S) sk hlead hk1 hk2 hL)
    (fun c hcV _ _ => V.subset_ids hcV)

/-- **And it conflicts with no verdict**, at an admissible threshold. -/
theorem decided_none_fresh_agree {U : (HybridProperties.hybridRule (Validator := Validator)
    (BlockId := BlockId) (Payload := Payload) kt).Universe} (sk : SkipMsg U.val)
    (hpos : 0 < kt) (hk : Hybrid.Admissible Validator kt)
    {V : View Validator BlockId Payload U.val} {T : Finset Validator} {k : ℕ}
    (hq : Hybrid.q Validator ≤ T.card)
    (hlead : S.leader k = sk.v1) (hk1 : sk.r0 < S.slotRound k) (hk2 : S.slotRound k ≤ sk.r)
    (hpres : PresentAt (HybridProperties.hybridRule (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload) kt) V T (S.slotRound k + 1))
    {U'' : (HybridProperties.hybridRule (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload) kt).Universe}
    (he' : Extends (HybridProperties.hybridRule (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload) kt) (fill U sk) U'')
    {V'' W : View Validator BlockId Payload U''.val} (hsub : (sk.liftView V).ids ⊆ V''.ids)
    {v : Option BlockId}
    (hW : (HybridProperties.hybridRule (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload) kt).Decided S (U := U'') W k v) : v = none :=
  (decided_agree_extends (HybridProperties.agree hk)
    (Persist.of_banded (HybridProperties.banded hpos)) he' (V := sk.liftView V) (V' := V'') hsub
    (decided_none_fresh sk hq hlead hk1 hk2 hpres) hW).symm

end HybridProperties

end LeanDag
