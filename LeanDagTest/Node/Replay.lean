import LeanDag.Node.Model.Run
import LeanDag.Node.Vote
import LeanDagTest.MahiMahi.Model
import LeanDagTest.Mysticeti.Model
/-!
# The program on the scheme's hand-built records

`docs/validator.md` §6, item 1. A record's blocks go through the
program's store path (`flush`, which accepts each block once its
references are accepted and it is valid at the row) into an empty store,
and the program's decider (`decideStep`) runs once on the result. Its
commits are those the scheme's tests record for `tryDecide` on the same
record (`LeanDagTest/Scheme/TryDecide.lean`): slots `0`, `1` and `2` of
Mahi-Mahi's `full4` at the Mahi-Mahi row of wave four, and slots `0`
(indirectly) and `1` of Mysticeti's `U7` at the Mysticeti row.
-/

namespace LeanDagTest

namespace Node

namespace Replay

open LeanDag LeanDag.Node

/-- A record's hash: the identifier the record gives the block. -/
def idIn (blk : Fin 24 → Block (Fin 4) (Fin 24) Unit) (b : Block (Fin 4) (Fin 24) Unit) :
    Fin 24 :=
  ((List.finRange 24).find? fun i => decide ((blk i).round = b.round ∧
    (blk i).creator = b.creator ∧ (blk i).refs = b.refs)).getD 0

/-- A configuration at row `p`, `n = 4`, `f = 1`, `q = 3`, with one
leader every `per` rounds, the record's hash, and no garbage collection
within the record's rounds. -/
def cfg (p : Scheme.Params) (per : ℕ) (hper : 0 < per) (elect : ℕ → Fin 4)
    (blk : Fin 24 → Block (Fin 4) (Fin 24) Unit) : Config (Fin 4) (Fin 24) Unit where
  p := p
  f := 1
  c := 0
  q := 3
  me := 0
  per := per
  m := 1
  per_pos := hper
  m_pos := Nat.one_pos
  elect := elect
  elect_block := Slots.one_hblock _
  timeout := fun _ => 10
  σ := boundedSel
  idOf := idIn blk
  lag := 100
  limit := none
  payload := fun _ => ()

/-- The record's blocks through the store path into an empty store: the
number of blocks the store accepted, the number left pending, and the commits of one
decision step. -/
def replay (c : Config (Fin 4) (Fin 24) Unit) (blk : Fin 24 → Block (Fin 4) (Fin 24) Unit) :
    ℕ × ℕ × List (ℕ × Option (Fin 24)) :=
  let fl := flush c 24 (Store.empty c.genesis) ((List.finRange 24).map fun i => (i, blk i))
  let s := { State.init c with store := fl.1 }
  (fl.1.ids.card, fl.2.length, commitsOf (decideStep c s).2)

/-! ## Mahi-Mahi's `full4` at the Mahi-Mahi row of wave four -/

/-- info: (24, 0, [(0, some 0), (1, some 5), (2, some 10)]) -/
#guard_msgs in
#eval replay (cfg (Scheme.Params.mahiMahi 4 4 1) 1 Nat.one_pos (fun k => ⟨k % 4, by omega⟩)
  mmFullBlk) mmFullBlk

/-! ## Mysticeti's `U7` at the Mysticeti row -/

/-- info: (24, 0, [(0, some 0), (1, some 12)]) -/
#guard_msgs in
#eval replay (cfg (Scheme.Params.mysticeti 4 1) 3 (by omega) (fun _ => 0) lk7) lk7

end Replay

end Node

end LeanDagTest
