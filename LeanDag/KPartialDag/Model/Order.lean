import LeanDag.KPartialDag.Model.Live
/-!
# K-partial DAG — what a committed leader outputs

`docs/kpartial.md` §7. A committed leader `L` outputs the blocks of its
available sub-DAG at most `D` rounds below it (`Out`); a node reads them on
what it holds (`OutIn`). A node's ledger after slots `0, …, n-1` is what the
leaders it committed there output (`LedgerIn`), and a block enters it at the
first committed slot whose leader outputs it (`EntersIn`).

Definitions only.
-/

namespace LeanDag

namespace KPartialDag

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator] [F : Faults Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}

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

end KPartialDag

end LeanDag
