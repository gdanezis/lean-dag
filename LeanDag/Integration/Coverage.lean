import LeanDag.Integration.Preservation
import LeanDag.Properties.Arcs.SafeSkip
import LeanDag.Properties.Arcs.GC
import LeanDag.Timed.Extension
import LeanDag.Mysticeti.Record
/-!
# I4 — the fill does not restore coverage, and why that is correct

Every statement here is `Timed/Extension.lean`'s generic result at the
Safe Skip fill's `Extends` witness, or `Timed.synchronisedOn_of_rebased`
at its `Sustains` witness. Coverage fails at every gap round for a
reliable set counting the recovering validator
(`not_synchronisedOn_skipFill`): no old block references a fresh
identifier, which is what makes the fill safe, but coverage wants the
opposite. This is not a defect — Safe Skip restores production, not
coverage — and coverage is untouched for a set excluding the recovering
validator, returning strictly above the fill.
-/

namespace LeanDag

namespace Integration

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {U : BlockUniverse Validator BlockId Payload}

/-- The fill is an extension of the core's carrier. -/
theorem extends_skipFill (sk : SkipMsg U) :
    Properties.Extends (MysticetiProperties.mysticetiRule (Payload := Payload)) U sk.skipFill :=
  Properties.Arcs.extends_of_skipFill _ sk rfl rfl rfl rfl

/-- **I4, refuted.** The fill does not restore coverage: if the
recovering validator is counted reliable, an old reliable block at any
gap round `k+1` fails to reference the filled block at `k`. -/
theorem not_synchronisedOn_skipFill (sk : SkipMsg U) {T : Finset Validator}
    {R k : ℕ} (hv1 : sk.v1 ∈ T) (hk1 : sk.r0 < k) (hk2 : k ≤ sk.r) (hk : R ≤ k)
    {b : BlockId} (hb : b ∈ U.ids) (hbround : (U.block b).round = k + 1)
    (hbc : (U.block b).creator ∈ T) :
    ¬ SynchronisedOn sk.skipFill T R :=
  Timed.not_synchronisedOn_of_extends (extends_skipFill sk) hk
    (f := sk.fresh k)
    ⟨Finset.mem_union_right _ (sk.mem_freshIds.mpr ⟨k, hk1, hk2, rfl⟩), sk.hfresh_new k⟩
    (by change (sk.skipFill.block (sk.fresh k)).round = k; rw [sk.skipFill_block_fresh]; rfl)
    (by change (sk.skipFill.block (sk.fresh k)).creator ∈ T; rw [sk.skipFill_block_fresh]; exact hv1)
    hb hbround hbc

/-- **The refutation is narrow.** Exclude the recovering validator from
the reliable set and coverage is untouched: the fill's blocks are its
alone. -/
theorem synchronisedOn_skipFill_of_notMem (sk : SkipMsg U) {T : Finset Validator}
    {R : ℕ} (hs : SynchronisedOn U T R) (hv1 : sk.v1 ∉ T) :
    SynchronisedOn sk.skipFill T R :=
  Timed.synchronisedOn_of_extends (extends_skipFill sk) hs fun b hn => by
    rcases Finset.mem_union.mp hn.1 with ho | hf
    · exact absurd ho hn.2
    · obtain ⟨k, _, _, rfl⟩ := sk.mem_freshIds.mp hf
      change (sk.skipFill.block (sk.fresh k)).creator ∉ T
      rw [sk.skipFill_block_fresh]; exact hv1

/-- **I4, positively.** Coverage holds strictly above the fill: past the
target round every block is old and the original condition applies
unchanged. The strictness is not slack —
`not_synchronisedOn_skipFill` refutes it at `n = sk.r`. -/
theorem synchronisedOn_skipFill_above (sk : SkipMsg U) {T : Finset Validator}
    {R R' : ℕ} (hs : SynchronisedOn U T R) (hR : R ≤ R') (hR' : sk.r < R') :
    SynchronisedOn sk.skipFill T R' := by
  have h := Timed.synchronisedOn_of_rebased
    (R := MysticetiProperties.mysticetiRule) (Properties.Arcs.sustains_skipFill sk)
    (T := T) (r := R') (Nat.succ_le_of_lt hR') (Nat.zero_le _)
    (Timed.SynchronisedOn.mono (MysticetiProperties.synchronisedOn_eq.mpr hs) hR)
  exact MysticetiProperties.synchronisedOn_eq.mp (by simpa using h)

/-- **Synchrony survives the cut, from the rebase** (I2). -/
theorem synchronisedOn_chop {T : Finset Validator} {Rs R' : ℕ}
    (hs : LeanDag.SynchronisedOn U T Rs) (hGR : Rs ≤ G + R') :
    LeanDag.SynchronisedOn (chop U G) T R' := by
  have h := Timed.synchronisedOn_of_rebased (R := MysticetiProperties.mysticetiRule)
    (MysticetiProperties.sustains_chop (U := U) (G := G)) (T := T) (r := G + R') (by omega) (by omega)
    (Timed.SynchronisedOn.mono ((MysticetiProperties.synchronisedOn_eq).mpr hs) hGR)
  exact MysticetiProperties.synchronisedOn_eq.mp (by simpa using h)

end Integration

end LeanDag
