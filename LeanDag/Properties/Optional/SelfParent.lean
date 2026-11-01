import LeanDag.Properties.Carrier
/-!
# Self-reference, and one block per reliable author per round

Two optional properties whose conjunction gives a reliable author's
block reach to every earlier block of the same author above a round.
`SelfParent` is the core's P3′ at the carrier, asked of the reliable
authors' blocks above a round `R₀` only, since that is all the chain walk
reads; `NoEquiv` is the non-equivocation clause at a fault model. Neither is derivable from the band, and both exist
for inclusion (`Arcs/Quality.lean`), with no synchrony in the argument.
Nemo drops self-parent and Hydrozoan never had one, so those rules get
the coverage half of chain quality only.
-/

namespace LeanDag

namespace Properties

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {R : DagRule Validator BlockId Payload}

/-- **Every reliable author's block above round `R₀` references a block by
its author.** -/
def SelfParent (R : DagRule Validator BlockId Payload) (rel : Reliability Validator) (R₀ : ℕ) :
    Prop :=
  ∀ (U : R.Universe) (b : BlockId), b ∈ R.ids U → (R.block U b).creator ∈ rel.correct →
    R₀ < (R.block U b).round →
    ∃ p ∈ (R.block U b).refs, (R.block U p).creator = (R.block U b).creator

/-- **A reliable author has one block per round.** -/
def NoEquiv (R : DagRule Validator BlockId Payload) (rel : Reliability Validator) : Prop :=
  ∀ (U : R.Universe) (b c : BlockId), b ∈ R.ids U → c ∈ R.ids U →
    (R.block U b).creator ∈ rel.correct →
    (R.block U b).creator = (R.block U c).creator →
    (R.block U b).round = (R.block U c).round → b = c

/-- **A reliable author's block reaches every earlier block of that
author** at or above `R₀`: walk the self-parent chain down to the earlier
block's round, where non-equivocation says the chain has arrived. -/
theorem SelfParent.reaches_of_creator {rel : Reliability Validator} {R₀ : ℕ}
    (hsp : SelfParent R rel R₀) (hne : NoEquiv R rel) {U : R.Universe} {b c : BlockId}
    (hb : b ∈ R.ids U) (hc : c ∈ R.ids U) (hbc : (R.block U b).creator ∈ rel.correct)
    (hcc : (R.block U c).creator = (R.block U b).creator)
    (hle : (R.block U b).round ≤ (R.block U c).round) (h₀ : R₀ ≤ (R.block U b).round) :
    ReachesFrom (R.block U) c b := by
  obtain ⟨d, hd⟩ : ∃ d, (R.block U c).round = (R.block U b).round + d :=
    ⟨_, (Nat.add_sub_cancel' hle).symm⟩
  induction d generalizing c with
  | zero =>
    have : b = c := hne U b c hb hc hbc hcc.symm (by omega)
    subst this
    exact Relation.ReflTransGen.refl
  | succ d ih =>
    obtain ⟨p, hp, hpc⟩ := hsp U c hc (by rw [hcc]; exact hbc) (by omega)
    have hpU : p ∈ R.ids U := (R.causal U).complete c hc p hp
    have hpr := (R.causal U).refs_round c hc p hp
    exact Relation.ReflTransGen.head hp (ih hpU (hpc.trans hcc) (by omega) (by omega))

end Properties

end LeanDag
