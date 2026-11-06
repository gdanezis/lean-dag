import LeanDag.KPartialDag.Model.Live
import Mathlib.Data.Prod.Lex
/-!
# K-partial DAG — what a committed leader outputs

`docs/kpartial.md` §7. A committed leader's output (`Out`, `OutIn`), a
node's ledger and entry slots (`LedgerIn`, `EntersIn`), and the ledger order
(`PrecedesIn`).
-/

namespace LeanDag

namespace KPartialDag

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator] [F : Faults Validator]
variable {BlockId : Type*} [LinearOrder BlockId] {Payload : Type*}

/-- **What a committed leader `L` outputs**: the blocks of its available
sub-DAG at most `D` rounds below it. -/
def Out (U : KRecord Validator BlockId Payload) (K D : ℕ) (L : BlockId) : Set BlockId :=
  {b | b ∈ Avail U K L ∧ (U.block L).round ≤ (U.block b).round + D}

/-- What `L` outputs, read on `H`. -/
def OutIn (U : KRecord Validator BlockId Payload) (K : ℕ) (H : Finset BlockId) (D : ℕ)
    (L : BlockId) : Set BlockId :=
  {b | b ∈ AvailIn U K H L ∧ (U.block L).round ≤ (U.block b).round + D}

/-- **A node's ledger** after slots `0, …, n-1`, for its verdicts `g`: what the
leaders it committed there output, read on `H`. -/
def LedgerIn (U : KRecord Validator BlockId Payload) (K : ℕ) (H : Finset BlockId) (D : ℕ)
    (g : ℕ → Option BlockId) (n : ℕ) : Set BlockId :=
  {b | ∃ k, k < n ∧ ∃ L, g k = some L ∧ b ∈ OutIn U K H D L}

/-- `b` enters a node's ledger at slot `k`: the first committed slot whose
leader outputs it. -/
def EntersIn (U : KRecord Validator BlockId Payload) (K : ℕ) (H : Finset BlockId) (D : ℕ)
    (g : ℕ → Option BlockId) (b : BlockId) (k : ℕ) : Prop :=
  (∃ L, g k = some L ∧ b ∈ OutIn U K H D L) ∧
    ∀ j, j < k → ∀ L, g j = some L → b ∉ OutIn U K H D L

/-- **The position of a block within one slot's output**: its round, then
its author, then its id, in lexicographic order. -/
def slotKey [LinearOrder Validator] (U : KRecord Validator BlockId Payload)
    (b : BlockId) : Lex (ℕ × Lex (Validator × BlockId)) :=
  toLex ((U.block b).round, toLex ((U.block b).creator, b))

/-- `b` comes before `b'` within one slot's output. -/
def KeyLt [LinearOrder Validator] (U : KRecord Validator BlockId Payload)
    (b b' : BlockId) : Prop :=
  slotKey U b < slotKey U b'

/-- **`b` precedes `b'` in a node's ledger** after slots `0, …, n-1`: it
enters at an earlier slot, or at the same slot and before `b'` within the
slot. -/
def PrecedesIn [LinearOrder Validator]
    (U : KRecord Validator BlockId Payload) (K : ℕ) (H : Finset BlockId) (D : ℕ)
    (g : ℕ → Option BlockId) (n : ℕ) (b b' : BlockId) : Prop :=
  ∃ k k', k < n ∧ k' < n ∧ EntersIn U K H D g b k ∧ EntersIn U K H D g b' k' ∧
    (k < k' ∨ k = k' ∧ KeyLt U b b')

end KPartialDag

end LeanDag
