import LeanDag.Node.Converge.Statement
import LeanDag.Node.Vote
/-!
# Bootstrap — statement

`docs/validator.md` §3.6 and §3.8, V9 and V12. A restarted node asks its
peers for their bases and certificates; once some round above its top
has blocks offered by `f + 1` distinct peers and an offered certificate
reaches it, it raises its horizon there, keeps those blocks, moves its
top to that round with no block of its own there, takes the offered
blocks above it, and outputs the certified decisions it lacks. Over a
trace of honest nodes `H` and an adversary, assume:

* **timely authentication** (`Converge.TimelyAuthentic`): a block
  delivered or offered to an honest node with an honest author's
  identity and its hash was broadcast by that author earlier;
* **timely offers** (`TimelyOffers`): a base offer given to an honest node
  in an honest peer's name was served by that peer earlier;
* **signed checkpoints** (`TimelyCerts`): every honest signer that a
  certificate given to an honest node lists proposed its decisions at its
  height earlier;
* **the hash** (`Converge.HashInjective`).

Then, at the bounded vote, with an admissible row and at most `f` nodes
outside `H`:

* **every certificate an honest node is given, with `q` distinct signers,
  certifies a prefix of an honest node's decisions** (`Certified`, V12);
* **any two honest nodes' decisions are prefix-comparable** (`Agrees`,
  V9), whatever horizons they raise, whenever they restart and however
  they bootstrap.

Statements only; the proofs are `Proof.lean`.
-/

namespace LeanDag

namespace Node

namespace Boot

variable {Validator BlockId Payload : Type} [Fintype Validator] [DecidableEq Validator]
variable [LinearOrder BlockId]

/-- **Timely offers**: a base offer given to an honest node in an honest
peer's name was served by that peer earlier. -/
def TimelyOffers (cfg : Config Validator BlockId Payload) (H : Finset Validator)
    (tr : Trace Validator BlockId Payload) : Prop :=
  ∀ j v p G bs, tr[j]? = some (v, .baseOffer p G bs) → v ∈ H → p ∈ H →
    ∃ i < j, (tr[i]?.map Prod.fst) = some p ∧ Output.serveBase v G bs ∈ outputsAt cfg tr i

/-- **Signed checkpoints**: every honest signer that a certificate given
to an honest node lists proposed its decisions at its height earlier. -/
def TimelyCerts (cfg : Config Validator BlockId Payload) (H : Finset Validator)
    (tr : Trace Validator BlockId Payload) : Prop :=
  ∀ (j : ℕ) v p (c : Cert Validator BlockId), tr[j]? = some (v, Input.certOffer p c) → v ∈ H →
    ∀ u ∈ c.signers, u ∈ H →
    ∃ i < j, (tr[i]?.map Prod.fst) = some u ∧
      Output.propose c.height c.decisions ∈ outputsAt cfg tr i

/-- **A certificate certifies an honest node's decisions**: one given to
an honest node with `q` distinct signers lists a prefix of an honest
node's decisions. -/
def Certified : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [LinearOrder BlockId] (cfg : Config Validator BlockId Payload) (H : Finset Validator)
    (tr : Trace Validator BlockId Payload),
    cfg.Admissible → Hᶜ.card ≤ cfg.f → TimelyCerts cfg H tr →
    ∀ (j : ℕ) v p (c : Cert Validator BlockId), tr[j]? = some (v, Input.certOffer p c) → v ∈ H →
      cfg.q ≤ c.signers.length →
        c.signers.Nodup → ∃ u ∈ H, c.decisions <+: decisionsOf cfg tr u

/-- **Two honest nodes' decisions are prefix-comparable**, bootstraps
included. -/
def Agrees : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [LinearOrder BlockId] (cfg : Config Validator BlockId Payload) (H : Finset Validator)
    (tr : Trace Validator BlockId Payload),
    cfg.σ = boundedSel → cfg.Admissible → Hᶜ.card ≤ cfg.f →
    Converge.TimelyAuthentic cfg H tr → TimelyOffers cfg H tr → TimelyCerts cfg H tr →
    Converge.HashInjective cfg H tr →
    ∀ v ∈ H, ∀ w ∈ H, decisionsOf cfg tr v <+: decisionsOf cfg tr w ∨
      decisionsOf cfg tr w <+: decisionsOf cfg tr v

/-- Bootstrap and checkpoints. -/
def Statement : Prop := Certified ∧ Agrees

end Boot

end Node

end LeanDag
