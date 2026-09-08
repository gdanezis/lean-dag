import LeanDag.FinWhale.Model.Rule
import LeanDag.Mysticeti.ViewPace
/-!
# FinWhale — the block-creation conditions

A block of round `r` is created under any of three conditions: **C1**,
the local DAG has the round-`(r−1)` leader's block with a quorum of
voters for the round-`(r−2)` leader (or an SP-skip pattern for it);
**C2**, the `2∆` timeout has expired; **C3**, the local DAG has `n − f`
round-`r` blocks. `Trigger` names which fired, and `Creation` is the
discipline, a `PaceCore` with these conditions and the parent-selection
rule as fields. `CertifiesSP` is `SPCertificate` in the universe's
vocabulary. Lemmas 18–20 and Theorem 21 follow from these fields.
-/

namespace LeanDag

namespace FinWhale

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator] [P : Params Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {U : BlockUniverse Validator BlockId Payload}
variable {T : Finset Validator} {N : ℕ}

/-- Which of the three conditions created a block. -/
inductive Trigger where
  /-- C1: the leader's block and a quorum of votes are in hand. -/
  | leaderAndQuorum
  /-- C2: the timeout expired. -/
  | timeout
  /-- C3: a quorum of blocks of this very round is in hand. -/
  | roundQuorum
  deriving DecidableEq

/-- **The block-creation rule, over the pacing trunk.** `lead` is the
leader schedule, one leader per round. -/
structure Creation (U : BlockUniverse Validator BlockId Payload)
    (T : Finset Validator) (N : ℕ) (lead : ℕ → Validator) extends PaceCore U T N where
  /-- Time advances with rounds. -/
  built_lt : ∀ v ∈ T, ∀ n < top v, built v n < built v (n + 1)
  /-- Which condition created each block. -/
  trigger : Validator → ℕ → Trigger
  /-- **The network does not deliver before it sends.** -/
  holds_built : ∀ v ∈ T, ∀ t, ∀ b ∈ holds v t, (U.block b).creator ∈ T →
    built ((U.block b).creator) ((U.block b).round) ≤ t
  /-- **No two reliable validators build one round at one instant.** -/
  builds_distinct : ∀ u ∈ T, ∀ v ∈ T, ∀ n, u ≠ v → built u n ≠ built v n
  /-- **C1's L1**: the round-`r` leader's block is in hand. -/
  c1_leader : ∀ v ∈ T, ∀ n, n + 1 ≤ N → trigger v (n + 1) = Trigger.leaderAndQuorum →
    ∀ L ∈ U.ids, (U.block L).round = n → (U.block L).creator = lead n →
      L ∈ holds v (built v (n + 1))
  /-- **C1's L2**: either a quorum of held voters for the round-`r`
  leader, or a quorum of held blocks declining to vote for it. -/
  c1_votes : ∀ v ∈ T, ∀ n, n + 2 ≤ N → trigger v (n + 2) = Trigger.leaderAndQuorum →
    ∀ L ∈ U.ids, (U.block L).round = n → (U.block L).creator = lead n →
    (∃ S : Finset Validator, spQuorum Validator ≤ S.card ∧ ∀ u ∈ S, ∃ b ∈ U.ids,
        b ∈ holds v (built v (n + 2)) ∧ (U.block b).creator = u ∧
        (U.block b).round = n + 1 ∧ L ∈ (U.block b).refs) ∨
    (∃ S : Finset Validator, spQuorum Validator ≤ S.card ∧ ∀ u ∈ S, ∃ b ∈ U.ids,
        b ∈ holds v (built v (n + 2)) ∧ (U.block b).creator = u ∧
        (U.block b).round = n + 1 ∧ L ∉ (U.block b).refs)
  /-- **C2**: the full timeout was waited out. -/
  c2_wait : ∀ v ∈ T, ∀ n, trigger v (n + 1) = Trigger.timeout →
    built v n + timeout n ≤ built v (n + 1)
  /-- **C3**: `n − f` blocks of the round being built are in hand. -/
  c3_quorum : ∀ v ∈ T, ∀ n, n + 1 ≤ N → trigger v (n + 1) = Trigger.roundQuorum →
    ∃ S : Finset Validator, quorumCard Validator ≤ S.card ∧ ∀ u ∈ S, ∃ b ∈ U.ids,
      b ∈ holds v (built v (n + 1)) ∧ (U.block b).creator = u ∧
      (U.block b).round = n + 1
  /-- **Parent selection takes the leader's block** when it is held and
  the leader is reliable. The reliability guard is not decoration: an
  equivocating leader would force a validator holding two of its blocks
  to reference both, which `distinct_creators` forbids. -/
  selects_leader : ∀ v ∈ T, ∀ n, lead n ∈ T → ∀ c ∈ U.ids, (U.block c).creator = v →
    (U.block c).round = n + 1 → ∀ L ∈ U.ids, (U.block L).round = n →
    (U.block L).creator = lead n → L ∈ holds v (built v (n + 1)) →
      L ∈ (U.block c).refs
  /-- **And it takes the votes** it holds: where the builder holds a
  round-`(n+1)` block voting for the reliable leader's block, its own
  block has a parent by that same validator, voting for it too. Stated
  as "has a parent by that author," not "the held block is a parent,"
  since a Byzantine validator's two voting blocks would force two
  references otherwise — what the certificate counts is authors. -/
  selects_votes : ∀ v ∈ T, ∀ n, lead n ∈ T → ∀ c ∈ U.ids, (U.block c).creator = v →
    (U.block c).round = n + 2 → ∀ L ∈ U.ids, (U.block L).round = n →
    (U.block L).creator = lead n → ∀ b ∈ U.ids, (U.block b).round = n + 1 →
    b ∈ holds v (built v (n + 2)) → L ∈ (U.block b).refs →
      ∃ q ∈ (U.block c).refs, (U.block q).creator = (U.block b).creator ∧
        L ∈ (U.block q).refs

/-- A block whose parents voting for `L` are a slow-path quorum —
`SPCertificate`, in the universe's vocabulary. -/
def CertifiesSP (U : BlockUniverse Validator BlockId Payload) (c L : BlockId) : Prop :=
  spQuorum Validator ≤
    (creatorsOf U.block (((U.block c).refs).filter (fun q => L ∈ (U.block q).refs))).card

end FinWhale

end LeanDag
