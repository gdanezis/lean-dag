import LeanDag.Node.Converge.Statement
import LeanDag.Node.Vote
/-!
# Bootstrap — statement

`docs/validator.md` §3.6, V9. A restarted node asks its peers for their
bases; once some round above its top has blocks offered by `f + 1`
distinct peers, it raises its horizon there, keeps those blocks, starts
its own chain again at that round, and takes the offered blocks above it.
Over a trace of honest nodes `H` and an adversary, assume:

* **timely authentication** (`Converge.TimelyAuthentic`): a block
  delivered or offered to an honest node with an honest author's
  identity and its hash was made by that author earlier;
* **timely jumps** (`TimelyJumps`): a jump message given to an honest node
  in an honest node's name was sent by that node earlier;
* **timely offers** (`TimelyOffers`): a base offer given to an honest node
  in an honest peer's name was served by that peer earlier;
* **the hash** (`Converge.HashInjective`).

Then, at the bounded vote, with an admissible row and at most `f` nodes
outside `H`, **two honest nodes that decide a slot decide it alike**
(`Agrees`), whatever horizons they raise, whenever they jump and however
they bootstrap. A node that bootstraps skips the slots below its new
horizon, so its decisions need not be a prefix of another's.

Statements only; the proofs are `Proof.lean`.
-/

namespace LeanDag

namespace Node

namespace Boot

variable {Validator BlockId Payload : Type} [Fintype Validator] [DecidableEq Validator]
variable [LinearOrder BlockId]

/-- **Timely jumps**: a jump message given to an honest node in an honest
node's name was sent by that node earlier. -/
def TimelyJumps (cfg : Config Validator BlockId Payload) (H : Finset Validator)
    (tr : Trace Validator BlockId Payload) : Prop :=
  ∀ j v v1 B1 v2 B2, tr[j]? = some (v, .jump v1 B1 v2 B2) → v ∈ H → v1 ∈ H →
    ∃ i < j, (tr[i]?.map Prod.fst) = some v1 ∧ Output.jump v1 B1 v2 B2 ∈ outputsAt cfg tr i

/-- **Timely offers**: a base offer given to an honest node in an honest
peer's name was served by that peer earlier. -/
def TimelyOffers (cfg : Config Validator BlockId Payload) (H : Finset Validator)
    (tr : Trace Validator BlockId Payload) : Prop :=
  ∀ j v p G bs, tr[j]? = some (v, .baseOffer p G bs) → v ∈ H → p ∈ H →
    ∃ i < j, (tr[i]?.map Prod.fst) = some p ∧ Output.serveBase v G bs ∈ outputsAt cfg tr i

/-- **Two honest nodes that decide a slot decide it alike.** -/
def Agrees : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [LinearOrder BlockId] (cfg : Config Validator BlockId Payload) (H : Finset Validator)
    (tr : Trace Validator BlockId Payload),
    cfg.σ = boundedSel → cfg.Admissible → Hᶜ.card ≤ cfg.f →
    Converge.TimelyAuthentic cfg H tr → TimelyJumps cfg H tr → TimelyOffers cfg H tr →
    Converge.HashInjective cfg H tr →
    ∀ v ∈ H, ∀ w ∈ H, ∀ k d d', (k, d) ∈ decisionsOf cfg tr v → (k, d') ∈ decisionsOf cfg tr w →
      d = d'

/-- Bootstrap. -/
def Statement : Prop := Agrees

end Boot

end Node

end LeanDag
