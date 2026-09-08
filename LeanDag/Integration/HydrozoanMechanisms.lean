import LeanDag.Hydrozoan.Helpers.Commit
import LeanDag.Hydrozoan.Helpers.Skippability
import LeanDag.Hydrozoan.Helpers.Record
import LeanDag.Properties.Arcs.Record
import LeanDag.Properties.Arcs.Liveness
import LeanDag.Timed.Extension
/-!
# Garbage collection, crash recovery and re-genesis for Hydrozoan

Hydrozoan's universe is a block record through the adapter of
`Hydrozoan/Helpers/Record.lean`, so its carrier reads as records by
that adapter and its inverse, and every mechanism cell is
`Arcs/Record.lean` at `Hydrozoan.onRecord`. Beyond the constructions,
this file states the shape of a truncated block (which
Optimal-Hydrozoan's exclusion proof reads), the coverage refutation at
the copy fill, and the prompt skip from `SkipsUnsupported`.
-/

namespace LeanDag

namespace Integration

open LeanDag.Properties LeanDag.Properties.Arcs

variable {Replica : Type} [Fintype Replica] [DecidableEq Replica]
variable {BlockId : Type} [DecidableEq BlockId] [LinearOrder BlockId]
variable [F : LeanDag.Hydrozoan.Faults Replica]
variable {S : Slots Replica} {G d : ℕ}

/-! ## The cut -/

/-! The cut, the copy fill and re-genesis at Hydrozoan's universe are the
record's, `Hydrozoan.onRecord` being the identity: `BlockRecord.chop`,
`BlockRecord.copyFill` and `BlockRecord.addGenesis`, with the record's
lemmas about them. -/

variable {U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId} {sk : SkipData U.ids U.block}

/-- **The copy fill does not restore coverage either.** The generic
refutation at the record's `extends_copyFill`: a reliable set holding the
recovering replica is uncovered at every gap round, for the same reason
the fill is safe. -/
theorem not_synchronisedOn_copyFill_hz {sk : SkipData U.ids U.block} {T : Finset Replica}
    {R k : ℕ} (hv1 : sk.v1 ∈ T) (hk1 : sk.r0 < k) (hk2 : k ≤ sk.r) (hk : R ≤ k)
    {b : BlockId} (hb : b ∈ U.ids) (hbround : (U.block b).round = k + 1)
    (hbc : (U.block b).creator ∈ T) :
    ¬ Timed.SynchronisedOn (LeanDag.Hydrozoan.rule (Replica := Replica) (BlockId := BlockId))
      (BlockRecord.copyFill U sk) T R :=
  Timed.not_synchronisedOn_of_extends
    (show Extends (LeanDag.Hydrozoan.rule (Replica := Replica) (BlockId := BlockId))
        U (BlockRecord.copyFill U sk) from LeanDag.Hydrozoan.onRecord.extends_copyFill U sk) hk
    (f := sk.fresh k)
    ⟨Finset.mem_union_right _ (sk.mem_freshIds.mpr ⟨k, hk1, hk2, rfl⟩), sk.hfresh_new k⟩
    (by simp [BlockRecord.copyFill_block_fresh, SkipData.copyBlock])
    (by simpa [BlockRecord.copyFill_block_fresh, SkipData.copyBlock] using hv1)
    hb hbround hbc

/-! ## Promptness: the fill cannot conjure a commit, for Hydrozoan -/

/-- **Every candidate of a slot the recovering replica leads, at a gap
round, is a filled block.** -/
theorem candidates_fresh_hz (S : Slots Replica) {k : ℕ}
    (hlead : S.leader k = sk.v1) (hk1 : sk.r0 < S.slotRound k) (hk2 : S.slotRound k ≤ sk.r)
    {L : BlockId}
    (hL : (LeanDag.Hydrozoan.rule (Replica := Replica) (BlockId := BlockId)).IsCandidate S
      (BlockRecord.copyFill U sk) k L) : L ∉ U.ids := by
  intro hLU
  obtain ⟨-, hLr, hLc⟩ := hL
  have hLr' : (((BlockRecord.copyFill U sk).block L)).round = S.slotRound k := hLr
  have hLc' : (((BlockRecord.copyFill U sk).block L)).creator = S.leader k := hLc
  rw [BlockRecord.copyFill_block_old hLU] at hLr' hLc'
  exact sk.hgap L hLU (by rw [← hlead]; exact hLc')
    (by change sk.r0 < ((U.block L)).round; omega)
    (by change ((U.block L)).round ≤ sk.r; omega)

/-- **SS3 for Hydrozoan**, from its `SkipsUnsupported`: the slot the
recovering replica leads at a gap round is skipped at once, at the grade
`qFast ≤ |T|`. -/
theorem decided_none_fresh_hz (S : Slots Replica) {V : LeanDag.Hydrozoan.View U}
    {T : Finset Replica} {k : ℕ} (hq : LeanDag.Hydrozoan.qFast Replica ≤ T.card)
    (hlead : S.leader k = sk.v1) (hk1 : sk.r0 < S.slotRound k) (hk2 : S.slotRound k ≤ sk.r)
    (hpres : PresentAt (LeanDag.Hydrozoan.rule (Replica := Replica) (BlockId := BlockId)) V T
      (S.slotRound k + 1)) :
    (LeanDag.Hydrozoan.rule (Replica := Replica) (BlockId := BlockId)).Decided S
      (U := BlockRecord.copyFill U sk) (V.liftCopy (sk := sk)) k none :=
  decided_none_of_novel LeanDag.Hydrozoan.skipsUnsupported
    (show Extends (LeanDag.Hydrozoan.rule (Replica := Replica) (BlockId := BlockId))
        U (BlockRecord.copyFill U sk) from LeanDag.Hydrozoan.onRecord.extends_copyFill U sk) S hq
    (fun v hv => by
      obtain ⟨c, hcV, hcc, hcr⟩ := hpres v hv
      have hcU : c ∈ U.ids := V.subset_ids hcV
      refine ⟨c, hcV, ?_, ?_⟩
      · show (((BlockRecord.copyFill U sk).block c)).creator = v
        rw [BlockRecord.copyFill_block_old hcU]; exact hcc
      · show (((BlockRecord.copyFill U sk).block c)).round = S.slotRound k + 1
        rw [BlockRecord.copyFill_block_old hcU]; exact hcr)
    (fun L hL => candidates_fresh_hz S hlead hk1 hk2 hL)
    (fun c hcV _ _ => V.subset_ids hcV)

/-- **And it conflicts with no verdict.** -/
theorem decided_none_fresh_agree_hz (S : Slots Replica) {V : LeanDag.Hydrozoan.View U}
    {T : Finset Replica} {k : ℕ} (hq : LeanDag.Hydrozoan.qFast Replica ≤ T.card)
    (hlead : S.leader k = sk.v1) (hk1 : sk.r0 < S.slotRound k) (hk2 : S.slotRound k ≤ sk.r)
    (hpres : PresentAt (LeanDag.Hydrozoan.rule (Replica := Replica) (BlockId := BlockId)) V T
      (S.slotRound k + 1))
    {U'' : LeanDag.Hydrozoan.BlockUniverse Replica BlockId}
    (he' : Extends (LeanDag.Hydrozoan.rule (Replica := Replica) (BlockId := BlockId))
      (BlockRecord.copyFill U sk) U'')
    {V'' W : LeanDag.Hydrozoan.View U''} (hsub : (V.liftCopy (sk := sk)).ids ⊆ V''.ids)
    {v : Option BlockId}
    (hW : (LeanDag.Hydrozoan.rule (Replica := Replica) (BlockId := BlockId)).Decided S
      (U := U'') W k v) : v = none :=
  (decided_agree_extends LeanDag.Hydrozoan.agree (Persist.of_banded LeanDag.Hydrozoan.banded)
    he' (V := V.liftCopy (sk := sk)) (V' := V'') hsub (decided_none_fresh_hz S hq hlead hk1 hk2 hpres) hW).symm

end Integration

end LeanDag
