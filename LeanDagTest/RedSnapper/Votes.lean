import LeanDag.RedSnapper.Helpers.Votes
import LeanDagTest.RedSnapper.Stance

/-!
# Witness: votes

The three vote shapes of `Model/Votes.lean`, decided on the Phase 3
universes `U` and `UKeep` through the surrogates of `Helpers/Votes.lean`.

* **Fast votes.** Id 6 (correct `1`, carries `tx 0`, declares `ack 0`)
  is a fast vote for `tx 0`, as is Byzantine `0`'s twin 4. Refused: at
  id 4 for `tx 1` (the stance is `ack 0`); at id 9 for `tx 0` (the
  stance is `⊥`); at id 12 for `tx 0` (Byzantine `0` declares `ack 0`
  without `tx 0` in its history — a declaration is not an inclusion).
* **Bot votes.** Id 9 (correct `1`, `⊥` with the conflict on `o0`
  visible, having ACKed `tx 0` at id 6) is an unlock vote and not a skip
  vote. In `UKeep`, validator `2` declares `⊥` on `o0` at ids 5 and 9
  with a single candidate in view: no conflict, so no vote of either
  kind — `⊥` alone is not a skip vote.

Skip votes and the invalid-transaction refusal are witnessed on the
certificate universes of `RedSnapperTest.Certificates`.
-/

namespace LeanDagTest

namespace RedSnapper

open LeanDag LeanDag.RedSnapper

set_option maxRecDepth 16384
set_option synthInstance.maxSize 4096

-- Fast votes.
example : IsFastVote U 6 0 := (isFastVote_iff (by decide)).mpr (by decide)
example : IsFastVote U 4 0 := (isFastVote_iff (by decide)).mpr (by decide)
example : ¬ IsFastVote U 4 1 := fun h => absurd ((isFastVote_iff (by decide)).mp h) (by decide)
example : ¬ IsFastVote U 9 0 := fun h => absurd ((isFastVote_iff (by decide)).mp h) (by decide)
example : ¬ IsFastVote U 12 0 := fun h => absurd ((isFastVote_iff (by decide)).mp h) (by decide)

-- Id 12 declares `ack 0` but does not include `tx 0`: the gate that
-- refuses it.
example : StanceIs U 0 0 12 (some (.ack 0)) ∧ ¬ Includes U 12 0 :=
  ⟨(stanceIs_some_iff (by decide)).mpr (by decide),
    fun h => (by decide : (0 : Fin 4) ∉ txsIn U 12)
      ((mem_txsIn_iff (U := U) (b := 12) (tx := 0) (by decide)).mpr h)⟩

-- Bot votes: id 9 retracts after ACKing — an unlock vote, not a skip.
example : IsBotVote U 9 0 := (isBotVote_iff (by decide)).mpr (by decide)
example : IsUnlockVote U 9 0 := (isUnlockVote_iff (by decide)).mpr (by decide)
example : ¬ IsSkipVote U 9 0 := fun h => absurd ((isSkipVote_iff (by decide)).mp h) (by decide)

-- `⊥` with no conflict in view is no vote: `UKeep`'s validator 2 at ids
-- 5 and 9 stands at `⊥` with one candidate.
example : StanceIs UKeep 2 0 9 (some .bot) := (stanceIs_some_iff (by decide)).mpr (by decide)
example : ¬ Conflicted UKeep 9 0 := fun h => absurd ((conflicted_iff (by decide)).mp h) (by decide)
example : ¬ IsBotVote UKeep 9 0 := fun h => absurd ((isBotVote_iff (by decide)).mp h) (by decide)
example : ¬ IsSkipVote UKeep 9 0 := fun h => absurd ((isSkipVote_iff (by decide)).mp h) (by decide)

-- And a correct validator keeping its ACK is a fast vote at every block
-- of its chain.
example : IsFastVote UKeep 4 0 ∧ IsFastVote UKeep 8 0 :=
  ⟨(isFastVote_iff (by decide)).mpr (by decide), (isFastVote_iff (by decide)).mpr (by decide)⟩

end RedSnapper

end LeanDagTest
