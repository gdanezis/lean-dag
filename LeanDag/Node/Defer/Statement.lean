import LeanDag.Node.Boot.Statement
/-!
# Rate limiting does not make a node decide wrongly — statement

`docs/validator.md` §3.9, V7. Over a trace of honest nodes `H` and an
adversary, under the assumptions of `Boot.Agrees`, at every
configuration, rate limiting or not, there is a block record at quorum
`q` whose honest set is `H` and whose identifiers are ones the honest
nodes knew blocks under, such that:

* **every honest store is a cut of it** at the end of the trace: each
  stored block is a block of the record, read alike at the store's
  horizon;
* **every honest decision is the record's verdict on a view of it and
  on every larger view** (`Decides`): a node that held fewer blocks,
  having deferred or dropped some, decides only what a node holding more
  of the record decides.

Statements only; the proofs are `Proof.lean`.
-/

namespace LeanDag

namespace Node

namespace Defer

/-- **Every honest decision is the run's record's verdict on a view of it
and on every larger view**, and every honest store a cut of that record. -/
def Decides : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [LinearOrder BlockId] (cfg : Config Validator BlockId Payload) (H : Finset Validator)
    (tr : Trace Validator BlockId Payload),
    cfg.σ = boundedSel → cfg.Admissible → Hᶜ.card ≤ cfg.f →
    Converge.TimelyAuthentic cfg H tr → Boot.TimelyOffers cfg H tr → Boot.TimelyCerts cfg H tr →
    Converge.HashInjective cfg H tr → Boot.ChainInjective cfg H tr →
    ∃ U : BlockRecord Validator BlockId Payload (ValidAt cfg.q Clause.none) H,
      (∀ j ∈ U.ids, ∃ v ∈ H, ∃ x ∈ knownOf cfg tr v, x.1 = j) ∧
      (∀ v ∈ H, let st := (stateBefore cfg tr tr.length v).store
        ∀ j ∈ st.ids, j ∈ U.ids ∧ atBase st.base (U.block j) = st.blk j) ∧
      ∀ v ∈ H, ∀ e ∈ decisionsOf cfg tr v, ∃ V : U.View, ∀ V' : U.View, V.ids ⊆ V'.ids →
        letI := cfg.slots
        (Scheme.schemeAnchored cfg.p boundedSel).Decided U V' e.1 e.2

/-- Rate limiting and decisions. -/
def Statement : Prop := Decides

end Defer

end Node

end LeanDag
