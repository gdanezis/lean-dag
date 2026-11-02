import LeanDag.Properties.Arcs.Record
import LeanDag.Common.BypassView
/-!
# Safety under bypass below the decided horizon, at any carrier on the record

`docs/sync-auth.md` §8. A validator that applies the rule of §8 holds a
bypass view: its ordered blocks, and every reference of a held block,
unless the reference is bypassed below the horizon. It decides slot `n`
on the part of its bypass view at or above `slotRound n - 1`, which is a
view of the record cut there (`BypassView.chop`).

* **Agreement of two bypass views** (`decided_agree_bypass`): any two such
  validators agree on the slot, by `Agree` on the cut.
* **And with a full history** (`decided_agree_bypass_full`): a rule with
  `Banded` gives the verdict of every validator holding a view of the
  whole record, as for garbage collection.
* **Safety** (`bypassLedger_agree_bypass`): two validators that decide
  every slot below `N` so, each on a bypass view of its own ledger, order
  the same blocks; `flushOn_eq` says each computes its commits from the
  blocks it holds.
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

/-- **Agreement of two bypass views**: two validators deciding a slot on
their bypass views, cut at one round, agree. -/
theorem decided_agree_bypass (ha : Agree R) (hd : G ≤ S.slotRound d)
    {H₁ H₂ : ℕ} {C₁ C₂ : Finset BlockId}
    {W₁ : BypassView (c.toRec U) q H₁ C₁} {W₂ : BypassView (c.toRec U) q H₂ C₂}
    (h₁ : H₁ ≤ G + 1) (h₂ : H₂ ≤ G + 1) {k : ℕ} {w₁ w₂ : Option BlockId}
    (hW₁ : R.Decided (S.chop G d hd) (c.bypassView W₁ G h₁) k w₁)
    (hW₂ : R.Decided (S.chop G d hd) (c.bypassView W₂ G h₂) k w₂) : w₁ = w₂ :=
  ha _ _ _ k w₁ w₂ hW₁ hW₂

/-- **And with a full history**: under `Banded`, a validator deciding on its
bypass view agrees with any validator holding a view of the whole record. -/
theorem decided_agree_bypass_full (ha : Agree R) (hb : Banded R) (hd : G ≤ S.slotRound d)
    {C : Finset BlockId} {W : BypassView (c.toRec U) q H C} (hG : H ≤ G + 1)
    {V : R.View U} {k : ℕ} {w v : Option BlockId}
    (hW : R.Decided (S.chop G d hd) (c.bypassView W G hG) k w)
    (hV : R.Decided S V (d + k) v) : w = v :=
  c.decided_agree_chop ha hb hd hW hV

/-- `g` is decided, slot by slot below `N`, on bypass views: slot `n` on a
bypass view of the ledger after `n` slots at the horizon `slotRound n`,
cut one round below it. -/
def DecidedOnBypass (U : R.Universe) (S : Slots Validator) (q N : ℕ)
    (g : ℕ → Option BlockId) : Prop :=
  ∀ n, n < N → ∃ W : BypassView (c.toRec U) q (S.slotRound n) (bypassLedger (c.toRec U) q g n),
    R.Decided (S.chop (S.slotRound n - 1) n (Nat.sub_le _ _))
      (c.bypassView W (S.slotRound n - 1) (by omega)) 0 (g n)

/-- **Safety under bypass**: two validators that decide every slot below `N`
on bypass views of their own ledgers agree on every verdict, and order the
same blocks. -/
theorem bypassLedger_agree_bypass (ha : Agree R) {N : ℕ} {g₁ g₂ : ℕ → Option BlockId}
    (h₁ : c.DecidedOnBypass U S q N g₁) (h₂ : c.DecidedOnBypass U S q N g₂) :
    (∀ n, n < N → g₁ n = g₂ n) ∧
      bypassLedger (c.toRec U) q g₁ N = bypassLedger (c.toRec U) q g₂ N := by
  have hg : ∀ n, n < N → g₁ n = g₂ n := fun n hn => by
    obtain ⟨W₁, hW₁⟩ := h₁ n hn
    obtain ⟨W₂, hW₂⟩ := h₂ n hn
    exact c.decided_agree_bypass ha _ _ _ hW₁ hW₂
  exact ⟨hg, bypassLedger_agree_of hg⟩

/-- **And with a full history**: under `Banded`, a validator that decides
every slot below `N` on bypass views orders the blocks that the verdicts of
a validator holding views of the whole record give. -/
theorem bypassLedger_agree_bypass_full (ha : Agree R) (hb : Banded R) {N : ℕ}
    {g g' : ℕ → Option BlockId} (h : c.DecidedOnBypass U S q N g)
    (h' : ∀ n, n < N → ∃ V : R.View U, R.Decided S V n (g' n)) :
    (∀ n, n < N → g n = g' n) ∧
      bypassLedger (c.toRec U) q g N = bypassLedger (c.toRec U) q g' N := by
  have hg : ∀ n, n < N → g n = g' n := fun n hn => by
    obtain ⟨W, hW⟩ := h n hn
    obtain ⟨V, hV⟩ := h' n hn
    exact c.decided_agree_bypass_full ha hb _ _ hW hV
  exact ⟨hg, bypassLedger_agree_of hg⟩

end DagRule.OnRecord

end Properties

end LeanDag
