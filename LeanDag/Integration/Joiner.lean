import LeanDag.GC.ChopDecided
import LeanDag.Adaptive.Joiner
import LeanDag.Properties.Arcs.GC
import LeanDag.Mysticeti.Record
/-!
# I5 — the joiner and the adaptive schedule, at the core

`Adaptive/Joiner.lean` at the core's cut: the schedule half is
`Slots.chop` read as a `Rebases` witness, the verdict half the generic
cross-cut agreement at `truncates_chop`. Truncating an adaptive
schedule and adapting a truncated one are definitionally equal, so
`slotsChop_slotsOf_eq` closes by `rfl`.
-/

namespace LeanDag

namespace Integration

open Properties Adaptive

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {U : BlockUniverse Validator BlockId Payload}
variable [S : Slots Validator] {G d : ℕ}

/-! ## The schedule transformers commute -/

omit F in
/-- Truncation preserves one-leader-per-round. -/
theorem injective_slotRound_chop (hd : G ≤ S.slotRound d)
    (hinj : Function.Injective S.slotRound) :
    Function.Injective (S.chop G d hd).slotRound :=
  (Properties.rebases_chop hd).injective hinj

omit F in
/-- **The transformers commute**, field by field: truncating an adaptive
schedule and adapting a truncated one give the same rounds and the
same leaders, provided the assignment used in the truncation is the
original one shifted past the base slot. -/
theorem slotsChop_slotsOf (hd : G ≤ S.slotRound d)
    (hinj : Function.Injective S.slotRound) (a : ℕ → Validator)
    (hd' : G ≤ (slotsOf hinj a).slotRound d) (k : ℕ) :
    ((slotsOf hinj a).chop G d hd').slotRound k
        = (slotsOf (S := S.chop G d hd)
            (injective_slotRound_chop hd hinj) (fun m => a (d + m))).slotRound k
      ∧ ((slotsOf hinj a).chop G d hd').leader k
        = (slotsOf (S := S.chop G d hd)
            (injective_slotRound_chop hd hinj) (fun m => a (d + m))).leader k :=
  ⟨rfl, rfl⟩

omit F in
/-- **And as schedules.** Both sides are rebases of `slotsOf hinj a` by
the same offset from the same base slot, so `Rebases.unique` would
settle it; at the core the two constructions are definitionally equal. -/
theorem slotsChop_slotsOf_eq (hd : G ≤ S.slotRound d)
    (hinj : Function.Injective S.slotRound) (a : ℕ → Validator)
    (hd' : G ≤ (slotsOf hinj a).slotRound d) :
    (slotsOf hinj a).chop G d hd'
      = slotsOf (S := S.chop G d hd) (injective_slotRound_chop hd hinj)
          (fun m => a (d + m)) := rfl

/-- **I5's verdict half**, at the core: the joiner and the network agree
on every shared slot, from an arbitrary view of the truncation. -/
theorem joiner_decided_agree (hd : G ≤ S.slotRound d)
    (hinj : Function.Injective S.slotRound) (a : ℕ → Validator)
    {W : View Validator BlockId Payload (chop U G)}
    {V : View Validator BlockId Payload U} {k : ℕ} {w v : Option BlockId}
    (hW : Decided (S := slotsOf (S := S.chop G d hd)
            (injective_slotRound_chop hd hinj) (fun m => a (d + m)))
          (chop U G) W k w)
    (hV : Decided (S := slotsOf hinj a) U V (d + k) v) : w = v :=
  Adaptive.joiner_decided_agree MysticetiProperties.agree MysticetiProperties.banded
    (MysticetiProperties.truncates_chop hd) hinj a
    (MysticetiProperties.viewAgreeAbove_chop (V := V)) hW hV

/-! ## The policy half, at the core -/

section Policy

variable {P : Adaptive.Policy (MysticetiProperties.mysticetiRule
  (Validator := Validator) (BlockId := BlockId) (Payload := Payload))}
variable {pick' : (U' : BlockUniverse Validator BlockId Payload) →
      View Validator BlockId Payload U' → (ℕ → Option BlockId) → ℕ → Validator}

/-! The assignment half of I5 — under a horizon-stable rule a joiner
computes exactly the leaders the network is using — and the schedule
half are `Adaptive.joiner_assign_agree` and `Adaptive.joiner_leader_agree`
at the core's `MysticetiProperties.sustains_chop` and `truncates_chop`. -/

/-- **I5, whole.** A joiner that computed its own schedule from its own
truncated view, under a horizon-stable rule, agrees with the network's
run on every shared slot: *pruning does not split the ledger, even when
the schedule is derived from it.* -/
theorem joiner_run_decided_agree (hd : G ≤ S.slotRound d)
    (hs : HorizonStable P G d pick')
    {V : View Validator BlockId Payload U} (R : Adaptive.Run P U V)
    (V' : View Validator BlockId Payload (chop U G))
    {W : View Validator BlockId Payload (chop U G)} {k : ℕ} {w v : Option BlockId}
    (hW : Decided (S := slotsOf (S := S.chop G d hd)
            (injective_slotRound_chop hd P.inj)
            (fun m => pick' (chop U G) V' (fun j => R.vdct (d + j)) m))
          (chop U G) W k w)
    (hV : Decided (S := slotsOf P.inj R.assign) U V (d + k) v) : w = v :=
  Adaptive.joiner_run_decided_agree MysticetiProperties.agree MysticetiProperties.banded
    hs (MysticetiProperties.truncates_chop hd) R V'
    (MysticetiProperties.viewAgreeAbove_chop (V := V)) hW hV

end Policy

end Integration

end LeanDag
