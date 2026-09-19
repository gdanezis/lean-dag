import LeanDag.Hydrozoan.PrefixAgreement.Statement
import LeanDag.Common.Dedup
/-!
# Delivery — statement

What a validator delivers, as the paper's `LinearizeSubDags` computes
it: the procedure keeps a persistent set `H` of delivered keys, walks
each committed leader's blocks in a fixed order, and outputs a block iff
its key is not yet in `H`. `PrefixAgreement`'s `ledger` is that walk
without the filter — every committed leader flattened by a per-leader
function `lin` — so the delivered sequence is `ledger` deduplicated by
first occurrence of the key.

The claims hold **for every key and every per-leader listing**. Two
instances matter: `authorRound U.block`, the paper's
`(b.author, b.round)`, under which the first claim is the Integrity
property of Byzantine atomic broadcast as the paper states it ("at most
once, regardless of `m`"); and `id`, a block's own identifier, which is
what an implementation deduplicating on block references computes.

Three claims: no key is delivered twice (Integrity); at different
horizons and from different views, the shorter delivered sequence is a
prefix of the longer (Total Order — with Integrity, a prefix leaves no
two blocks in opposite orders); and the filter only removes repeated
keys, so the claims are not about an empty list.
-/

namespace LeanDag

namespace Hydrozoan

namespace Delivery

open LeanDag.Hydrozoan.PrefixAgreement (ledger DecidesBelow)

section Sequences

variable {Replica BlockId Payload κ : Type*} [DecidableEq κ]

/-- The paper's key: a block's author and round. -/
def authorRound (blk : BlockId → LeanDag.Block Replica BlockId Payload) (b : BlockId) :
    Replica × ℕ :=
  ((blk b).creator, (blk b).round)

/-- **The delivered sequence**: the ledger with the first block of each
key kept and every later one dropped — `LinearizeSubDags` with its set
`H`, run over the committed leaders of slots `0, …, n-1`. -/
def delivered (key : BlockId → κ) (lin : BlockId → List BlockId)
    (g : ℕ → Option BlockId) (n : ℕ) : List BlockId :=
  dedupBy key (ledger lin g n)

end Sequences

section Claims

variable {Replica BlockId : Type*} [Fintype Replica] [DecidableEq Replica]
  [DecidableEq BlockId] [LinearOrder BlockId] [F : LeanDag.Hydrozoan.Faults Replica]
  [S : Slots Replica]

/-- **Integrity**: no key is delivered twice — for any key, any listing,
any verdict assignment and any horizon. In particular no block is. -/
def Integrity (BlockId : Type*) : Prop :=
  ∀ (κ : Type) [DecidableEq κ] (key : BlockId → κ) (lin : BlockId → List BlockId)
    (g : ℕ → Option BlockId) (n : ℕ),
    ((delivered key lin g n).map key).Nodup

/-- **Delivered prefix consistency**: two replicas, from any two views
and at any two horizons, deliver sequences of which the shorter is a
prefix of the longer. -/
def DeliveredPrefixConsistency (U : BlockUniverse Replica BlockId) : Prop :=
  ∀ (κ : Type) [DecidableEq κ] (key : BlockId → κ) (lin : BlockId → List BlockId)
    (V₁ V₂ : View U) (g₁ g₂ : ℕ → Option BlockId) (n₁ n₂ : ℕ),
    n₁ ≤ n₂ → DecidesBelow U V₁ g₁ n₁ → DecidesBelow U V₂ g₂ n₂ →
    delivered key lin g₁ n₁ <+: delivered key lin g₂ n₂

/-- **The filter is faithful**: what is delivered is a subsequence of the
ledger, and every key of the ledger is delivered — by that block or by
an earlier one of the same key. -/
def Faithful (BlockId : Type*) : Prop :=
  ∀ (κ : Type) [DecidableEq κ] (key : BlockId → κ) (lin : BlockId → List BlockId)
    (g : ℕ → Option BlockId) (n : ℕ),
    (delivered key lin g n).Sublist (ledger lin g n) ∧
      ∀ b ∈ ledger lin g n, ∃ c ∈ delivered key lin g n, key c = key b

/-- Delivery safety over every fault configuration, schedule, tie-break
order, and block universe the model admits. -/
def Statement : Prop :=
  ∀ (Replica BlockId : Type) [Fintype Replica] [DecidableEq Replica]
    [DecidableEq BlockId] [LinearOrder BlockId] [LeanDag.Hydrozoan.Faults Replica]
    [Slots Replica] (U : BlockUniverse Replica BlockId),
    Integrity BlockId ∧ DeliveredPrefixConsistency U ∧ Faithful BlockId

end Claims

end Delivery

end Hydrozoan

end LeanDag
