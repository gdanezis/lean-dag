import LeanDag.Properties.Arcs.Record
import LeanDag.Common.BypassView
/-!
# Safety under bypass below the decided horizon, at any carrier on the record

`docs/sync-auth.md` §8. A node that runs the rule (`BypassRun`) accepts a
block once it has followed its references up to bypassed blocks, decides
slot `n` on the blocks it holds at or above `slotRound n - 1`
(`DecOnCut`), and orders each commit from the blocks it holds.

* **It can decide on what it holds** (`exists_cutView`): those blocks form
  a view of the record cut at that round, since no reference there is
  bypassed.
* **Safety** (`bypassRun_agree`): under `Agree`, two such nodes agree on
  every verdict and order the same blocks, the ledger of those verdicts.
* **And with a full history** (`bypassRun_agree_full`): under `Banded`,
  their verdicts are those of any node holding a view of the whole record,
  by `decided_agree_chop` of garbage collection.
-/

namespace LeanDag

namespace Properties

namespace DagRule.OnRecord

open BlockRecord

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {R : DagRule Validator BlockId Payload}
variable {P : Validity Validator BlockId Payload} {honest : Finset Validator}
variable {I : BlockRecord Validator BlockId Payload P honest → Prop}
variable (c : R.OnRecord P honest I) [P.Mechanised] [Invariant.Chops I]
variable {S : Slots Validator} {U : R.Universe} {G d q H : ℕ}

/-- A bypass view, as a view of the carrier cut at `G`. -/
def bypassView {C : Finset BlockId} (W : BypassView (c.toRec U) q H C) (G : ℕ)
    (hG : H ≤ G + 1) : R.View (c.chop U G) :=
  c.ofView (W.chop G hG)

theorem viewIds_bypassView {C : Finset BlockId} (W : BypassView (c.toRec U) q H C) (G : ℕ)
    (hG : H ≤ G + 1) :
    R.viewIds (c.bypassView W G hG) = W.ids.filter fun i => G ≤ (R.block U i).round := by
  have h := c.viewIds_of (h := Invariant.Chops.chop G (c.inv U)) (W.chop G hG)
  rw [BypassView.chop_ids, c.block_to] at h
  exact h

/-- The decision of slot `n` on the blocks `held`: the rule's verdict on a
view of the cut at `slotRound n - 1` that holds exactly the blocks of
`held` at or above that round. -/
def DecOnCut (U : R.Universe) (S : Slots Validator) (held : Finset BlockId) (n : ℕ)
    (v : Option BlockId) : Prop :=
  ∃ V : R.View (c.chop U (S.slotRound n - 1)),
    R.viewIds V = held.filter (fun i => S.slotRound n - 1 ≤ (R.block U i).round) ∧
    R.Decided (S.chop (S.slotRound n - 1) n (Nat.sub_le _ _)) V 0 v

/-- **A node can decide on what it holds**: in every state of a run, the
blocks held at or above `slotRound n - 1` form a view of the cut there. -/
theorem exists_cutView {Dec : Finset BlockId → ℕ → Option BlockId → Prop}
    {g : ℕ → Option BlockId} {held led : Finset BlockId} {n : ℕ}
    (h : BypassRun (S := S) (c.toRec U) q Dec g held n led) :
    ∃ V : R.View (c.chop U (S.slotRound n - 1)),
      R.viewIds V = held.filter (fun i => S.slotRound n - 1 ≤ (R.block U i).round) := by
  obtain ⟨-, W, rfl⟩ := h.inv
  exact ⟨c.bypassView W _ (by omega), c.viewIds_bypassView W _ _⟩

/-- **Safety under bypass**: two nodes that run the rule, each deciding the
slots on the blocks it holds, agree on every verdict below `N` and order the
same blocks, the ledger of those verdicts. -/
theorem bypassRun_agree (ha : Agree R) {N : ℕ} {g₁ g₂ : ℕ → Option BlockId}
    {held₁ held₂ led₁ led₂ : Finset BlockId}
    (h₁ : BypassRun (S := S) (c.toRec U) q (c.DecOnCut U S) g₁ held₁ N led₁)
    (h₂ : BypassRun (S := S) (c.toRec U) q (c.DecOnCut U S) g₂ held₂ N led₂) :
    (∀ n, n < N → g₁ n = g₂ n) ∧ led₁ = led₂ ∧ led₁ = bypassLedger (c.toRec U) q g₁ N := by
  have hg : ∀ n, n < N → g₁ n = g₂ n := fun n hn => by
    obtain ⟨_, V₁, -, hV₁⟩ := h₁.decided n hn
    obtain ⟨_, V₂, -, hV₂⟩ := h₂.decided n hn
    exact ha _ _ _ 0 _ _ hV₁ hV₂
  refine ⟨hg, ?_, h₁.inv.1⟩
  rw [h₁.inv.1, h₂.inv.1]
  exact bypassLedger_agree_of hg

/-- **And with a full history**: under `Banded`, the verdicts of a node that
runs the rule are those of any node holding a view of the whole record. -/
theorem bypassRun_agree_full (ha : Agree R) (hb : Banded R) {N : ℕ}
    {g : ℕ → Option BlockId} {held led : Finset BlockId}
    (h : BypassRun (S := S) (c.toRec U) q (c.DecOnCut U S) g held N led)
    {n : ℕ} (hn : n < N) {V : R.View U} {v : Option BlockId} (hV : R.Decided S V n v) :
    g n = v := by
  obtain ⟨_, W, -, hW⟩ := h.decided n hn
  exact c.decided_agree_chop ha hb _ hW hV

end DagRule.OnRecord

end Properties

end LeanDag
