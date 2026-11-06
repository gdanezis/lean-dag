import LeanDag.KPartialDag.Model.Order
import LeanDag.KPartialDag.Model.Reactive
/-!
# K-partial DAG — closing the channel

`docs/kpartial.md` §12. Blocks declare the channel closed through their
payload (`closes`); a ledger is closed once it holds such blocks of a quorum
of distinct authors (`ClosedIn`), and the last commit is the slot at which it
first is (`ClosesAfter`). A node's decisions up to a slot (`DecidesBelow`).
-/

namespace LeanDag

namespace KPartialDag

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator] [F : Faults Validator]
variable {BlockId : Type*} [LinearOrder BlockId] {Payload : Type*}

/-- **A node's ledger is closed** after slots `0, …, n-1`: it holds blocks
whose payloads declare the channel closed, by a quorum of distinct authors. -/
def ClosedIn (U : KRecord Validator BlockId Payload) (K : ℕ) (H : Finset BlockId) (D : ℕ)
    (closes : Payload → Prop) (g : ℕ → Option BlockId) (n : ℕ) : Prop :=
  ∃ X : Finset BlockId, ↑X ⊆ LedgerIn U K H D g n ∧ (∀ x ∈ X, closes (U.block x).payload) ∧
    quorumCard Validator ≤ (creatorsOf U.block X).card

/-- **The channel closes after `n` slots** on a node's ledger: the ledger is
closed after slots `0, …, n-1` and after no fewer, so slot `n − 1` is the
last commit. -/
def ClosesAfter (U : KRecord Validator BlockId Payload) (K : ℕ) (H : Finset BlockId) (D : ℕ)
    (closes : Payload → Prop) (g : ℕ → Option BlockId) (n : ℕ) : Prop :=
  ClosedIn U K H D closes g n ∧ ∀ m, m < n → ¬ ClosedIn U K H D closes g m

/-- **Validators of `T` declare the channel closed from round `r₀` on**: each
of their blocks from that round on does. -/
def DeclaresFrom (U : KRecord Validator BlockId Payload) (T : Finset Validator)
    (closes : Payload → Prop) (r₀ : ℕ) : Prop :=
  ∀ x ∈ U.ids, (U.block x).creator ∈ T → r₀ ≤ (U.block x).round → closes (U.block x).payload

variable [S : Slots Validator]

/-- **A node has decided every slot below `n`** on `H`, and fetched each
leader it commits down to `D` rounds below it. -/
def DecidesBelow (U : KRecord Validator BlockId Payload) (K : ℕ) (H : Finset BlockId) (D : ℕ)
    (g : ℕ → Option BlockId) (n : ℕ) : Prop :=
  ∀ i, i < n → NodeDecided U K H i (g i) ∧
    ∀ L, g i = some L → FetchedIn U K H L ((U.block L).round - D)

end KPartialDag

end LeanDag
