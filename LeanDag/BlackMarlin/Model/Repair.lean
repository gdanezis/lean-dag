import LeanDag.BlackMarlin.Model.Descent
/-!
# Black Marlin — the descent, repaired

The execution of `black-marlin.md` §13 turns on the descent taking an
unsupported twin where the rule had committed the supported one; this
file states the condition that excludes it and a descent that meets it
(`black-marlin.md` §14), leaving `descend` and `flushRecord` unaltered.

A record is **support-preferring** when, at any round where some anchor
carries a quorum of support, what it flushes there is supported; BM1
makes that supported anchor unique, so two such records cannot part
there. `descendSupp` filters the candidates of L21–L24 to those the
rule could commit and falls back to L24 only where none is; a step
never stalls, though a chain through a different block descends through
a different cone, so the rounds a whole record flushes at may differ.

`Supported` is a fact about the universe, and a validator computes
support from its own view, which under-reports — so this states a
repair rather than supplies one; an implementation would still have to
establish that the support it needs is in view.

**Trusted core of the arc: definitions only.**
-/

namespace LeanDag

namespace BlackMarlin

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator] [Rot : Rotation Validator]
variable {BlockId : Type*} [LinearOrder BlockId] {Payload : Type*}
variable {U : BlockUniverse Validator BlockId Payload}

/-- The candidates of L21–L24 that the rule could commit. -/
def suppCandidates (U : BlockUniverse Validator BlockId Payload) (B : BlockId) :
    Finset BlockId :=
  (maxAnchor U (strongOf U B)).filter (fun A => Supported U A (U.block A).round)

/-- **The repaired choice**: a supported candidate where there is one,
and L21–L24 otherwise. -/
def descendSupp (U : BlockUniverse Validator BlockId Payload) (B : BlockId) :
    Option BlockId :=
  if (suppCandidates U B).Nonempty then pick (suppCandidates U B) else descend U B

/-- The repaired descent, with fuel, as `descentUpto` is. -/
def descentSuppUpto (U : BlockUniverse Validator BlockId Payload) :
    ℕ → BlockId → ℕ → Option BlockId
  | 0, B, ρ => if (U.block B).round = ρ then some B else none
  | (n + 1), B, ρ =>
      if (U.block B).round = ρ then some B
      else (descendSupp U B).bind (fun A => descentSuppUpto U n A ρ)

/-- The record the repaired descent leaves. -/
def flushRecordSupp (U : BlockUniverse Validator BlockId Payload) (B : BlockId) (ρ : ℕ) :
    Option BlockId :=
  descentSuppUpto U ((U.block B).round) B ρ

/-- **The side-condition.** Where a round has a supported anchor, the
record flushes a supported one. -/
def SupportPreferring (U : BlockUniverse Validator BlockId Payload) (f : Flush U) : Prop :=
  ∀ (ρ : ℕ) (L : BlockId), f.block ρ = some L →
    (∃ A, IsAnchor U ρ A ∧ Supported U A ρ) → Supported U L ρ

/-! ## The strengthened repair

`descendSupp` only helps where the supported anchor is among the
candidates L21–L24 already offers; where the step instead references a
twin, the filter is empty and the fallback takes it. `descendS` drops
the tie-break altogether and descends to the highest-round supported
anchor of the cone, which BM1 makes unique, leaving no rule for an
adversary to steer; rounds with no quorum are simply not boundaries, so
nothing is delivered later than before and nothing is lost. -/

/-- The anchors of a set that carry a quorum of support. -/
def suppAnchorsOf (U : BlockUniverse Validator BlockId Payload) (s : Finset BlockId) :
    Finset BlockId :=
  (anchorsOf U s).filter (fun A => Supported U A (U.block A).round)

/-- The highest round at which a set holds a supported anchor. -/
def maxSuppRound (U : BlockUniverse Validator BlockId Payload) (s : Finset BlockId) : ℕ :=
  (suppAnchorsOf U s).sup (fun A => (U.block A).round)

/-- **The strengthened descent**: to the highest-round supported anchor
of the cone, and nowhere else. -/
def descendS (U : BlockUniverse Validator BlockId Payload) (B : BlockId) : Option BlockId :=
  pick ((suppAnchorsOf U (strongOf U B)).filter
    (fun A => (U.block A).round = maxSuppRound U (strongOf U B)))

/-- The strengthened descent, with fuel. -/
def descentSUpto (U : BlockUniverse Validator BlockId Payload) :
    ℕ → BlockId → ℕ → Option BlockId
  | 0, B, ρ => if (U.block B).round = ρ then some B else none
  | (n + 1), B, ρ =>
      if (U.block B).round = ρ then some B
      else (descendS U B).bind (fun A => descentSUpto U n A ρ)

/-- The record it leaves. -/
def flushRecordS (U : BlockUniverse Validator BlockId Payload) (B : BlockId) (ρ : ℕ) :
    Option BlockId :=
  descentSUpto U ((U.block B).round) B ρ

end BlackMarlin

end LeanDag
