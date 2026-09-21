import LeanDag.RedSnapper.Helpers.Stance
import LeanDag.RedSnapper.Model.Votes

/-!
# Computable votes

Generated: decidable surrogates for the vote predicates of
`Model/Votes.lean`, each pinned against the audited definition by an iff
for universe members, so that witness models decide the computable side
and bridge. Nothing here is part of the audit surface.
-/

namespace LeanDag

namespace RedSnapper

variable {Validator BlockId Tx Obj : Type*} [Fintype Validator] [DecidableEq Validator]
  [DecidableEq BlockId] [DecidableEq Tx] [DecidableEq Obj] [F : Faults Validator]
  [T : Transactions Tx Obj]

section Surrogates

variable (U : Universe Validator BlockId Tx Obj)

/-- The computable form of `StanceIs U id o b (some s)`. -/
def StanceSomeDec (id : Validator) (o : Obj) (b : BlockId) (s : Stance Tx) : Prop :=
  ∃ b' ∈ latestDeclarers U id o b, (U.block b').declares o = some s ∧
    ∀ b'' ∈ latestDeclarers U id o b, b'' = b'

/-- The computable form of `AckedBefore`. -/
def AckedBeforeDec (id : Validator) (o : Obj) (b : BlockId) : Prop :=
  ∃ b' ∈ historyIn U b, (U.block b').author = id ∧
    ∃ b'' ∈ latestDeclarers U id o b', isAck ((U.block b'').declares o) = true ∧
      ∀ b''' ∈ latestDeclarers U id o b', b''' = b''

/-- The computable form of `IsFastVote`. -/
def IsFastVoteDec (b : BlockId) (tx : Tx) : Prop :=
  T.Valid tx ∧ tx ∈ txsIn U b ∧
    StanceSomeDec U (U.block b).author (T.input tx) b (Stance.ack tx)

/-- The computable form of `IsBotVote`. -/
def IsBotVoteDec (b : BlockId) (o : Obj) : Prop :=
  StanceSomeDec U (U.block b).author o b Stance.bot ∧ 1 < (candidates U b o).card

/-- The computable form of `IsSkipVote`. -/
def IsSkipVoteDec (b : BlockId) (o : Obj) : Prop :=
  IsBotVoteDec U b o ∧ ¬ AckedBeforeDec U (U.block b).author o b

/-- The computable form of `IsUnlockVote`. -/
def IsUnlockVoteDec (b : BlockId) (o : Obj) : Prop :=
  IsBotVoteDec U b o ∧ AckedBeforeDec U (U.block b).author o b

instance (id : Validator) (o : Obj) (b : BlockId) (s : Stance Tx) :
    Decidable (StanceSomeDec U id o b s) := by
  unfold StanceSomeDec; infer_instance

instance (id : Validator) (o : Obj) (b : BlockId) : Decidable (AckedBeforeDec U id o b) := by
  unfold AckedBeforeDec; infer_instance

instance (b : BlockId) (tx : Tx) : Decidable (IsFastVoteDec U b tx) := by
  unfold IsFastVoteDec; infer_instance

instance (b : BlockId) (o : Obj) : Decidable (IsBotVoteDec U b o) := by
  unfold IsBotVoteDec; infer_instance

instance (b : BlockId) (o : Obj) : Decidable (IsSkipVoteDec U b o) := by
  unfold IsSkipVoteDec; infer_instance

instance (b : BlockId) (o : Obj) : Decidable (IsUnlockVoteDec U b o) := by
  unfold IsUnlockVoteDec; infer_instance

end Surrogates

variable {U : Universe Validator BlockId Tx Obj}

omit [DecidableEq Tx] [DecidableEq Obj] T in
theorem stanceSomeDec_iff {id : Validator} {o : Obj} {b : BlockId} {s : Stance Tx}
    (hb : b ∈ U.ids) : StanceIs U id o b (some s) ↔ StanceSomeDec U id o b s :=
  stanceIs_some_iff hb

omit [DecidableEq Tx] [DecidableEq Obj] T in
theorem ackedBeforeDec_iff {id : Validator} {o : Obj} {b : BlockId} (hb : b ∈ U.ids) :
    AckedBefore U id o b ↔ AckedBeforeDec U id o b :=
  ackedBefore_iff hb

omit [DecidableEq Obj] in
theorem isFastVote_iff {b : BlockId} {tx : Tx} (hb : b ∈ U.ids) :
    IsFastVote U b tx ↔ IsFastVoteDec U b tx := by
  unfold IsFastVote IsFastVoteDec
  rw [mem_txsIn_iff hb, stanceSomeDec_iff hb]

theorem isBotVote_iff {b : BlockId} {o : Obj} (hb : b ∈ U.ids) :
    IsBotVote U b o ↔ IsBotVoteDec U b o := by
  unfold IsBotVote IsBotVoteDec
  rw [stanceSomeDec_iff hb, conflicted_iff hb]

theorem isSkipVote_iff {b : BlockId} {o : Obj} (hb : b ∈ U.ids) :
    IsSkipVote U b o ↔ IsSkipVoteDec U b o := by
  unfold IsSkipVote IsSkipVoteDec
  rw [isBotVote_iff hb, ackedBeforeDec_iff hb]

theorem isUnlockVote_iff {b : BlockId} {o : Obj} (hb : b ∈ U.ids) :
    IsUnlockVote U b o ↔ IsUnlockVoteDec U b o := by
  unfold IsUnlockVote IsUnlockVoteDec
  rw [isBotVote_iff hb, ackedBeforeDec_iff hb]

end RedSnapper

end LeanDag
