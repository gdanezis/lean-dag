import LeanDag.Properties.Band
/-!
# What a view-level mechanism owes

`docs/target-properties.md` §11.5. Rate limiting and the joiner
transform a **view** rather than the DAG `Sustains` covers. Safety needs
nothing: a verdict reached on a smaller view is reached on a larger one.
Liveness needs `DeliversOn`, since nothing else says a rate limiter
eventually delivers enough for a slot to decide. The protocol side is
derived, not owed: `exists_coversUpto_decides` says every verdict has a
round it is settled by, from the band alone, so the obligation falls
entirely on the mechanism. `Delivers` asks coverage of everything up to
a round, which a limiter that drops Byzantine spam need not give; a
weaker obligation over the correct blocks alone would serve such a
mechanism but has no witness or consumer here yet.
-/

namespace LeanDag

namespace Properties

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {R : DagRule Validator BlockId Payload}

/-- **A view is caught up to round `N`**: it holds every block the
universe has at or below that round. -/
def CoversUpto (R : DagRule Validator BlockId Payload) {U : R.Universe}
    (V : R.View U) (N : ℕ) : Prop :=
  ∀ b, b ∈ R.ids U → (R.block U b).round ≤ N → b ∈ R.viewIds V

/-- Covering a round covers every earlier one. -/
theorem CoversUpto.mono {U : R.Universe} {V : R.View U} {M N : ℕ}
    (h : CoversUpto R V N) (hMN : M ≤ N) : CoversUpto R V M :=
  fun b hb hr => h b hb (le_trans hr hMN)

/-- **A verdict is reached by every view caught up far enough**: the
band's ceiling is a round the verdict reads nothing above. -/
theorem exists_coversUpto_decides (h : Banded R) {S : Slots Validator}
    {U : R.Universe} {W : R.View U} {k : ℕ} {v : Option BlockId}
    (hW : R.Decided S W k v) :
    ∃ N, ∀ V : R.View U, CoversUpto R V N → R.Decided S V k v := by
  obtain ⟨top, htop⟩ := h S U W k v hW
  refine ⟨top, fun V hcov => ?_⟩
  exact htop 0 0 0 0 S U V k (by omega) (fun m m' hm _ => by
      have : m = m' := by omega
      subst this; rfl)
    (fun m m' hm _ => by have : m = m' := by omega
                         subst this; rfl)
    AgreeBand.refl (fun b hb _ h2 => hcov b (R.viewSound W hb) h2)

/-- **A view holds the reliable set's blocks over a window.** Weaker
than `CoversUpto` in the way a rate limiter needs: it says nothing about
what an equivocator or a withholder produced, because a verdict is
reached from a quorum of correct evidence and not from every block. -/
def CoversOn (R : DagRule Validator BlockId Payload) {U : R.Universe}
    (V : R.View U) (T : Finset Validator) (lo hi : ℕ) : Prop :=
  ∀ b, b ∈ R.ids U → (R.block U b).creator ∈ T →
    lo ≤ (R.block U b).round → (R.block U b).round ≤ hi → b ∈ R.viewIds V

/-- Full coverage over a window is coverage of any set over it. -/
theorem CoversUpto.coversOn {U : R.Universe} {V : R.View U} {N : ℕ}
    (h : CoversUpto R V N) (T : Finset Validator) (lo : ℕ) :
    CoversOn R V T lo N :=
  fun b hb _ _ hhi => h b hb hhi

/-- **A view-level mechanism delivers the reliable set.** For every
round, one of the views it produces holds every `T`-block from `lo` up to
it. What a rate limiter can promise, and what `DoS/Delivers.lean`
proves of the novelty budget. -/
def DeliversOn (R : DagRule Validator BlockId Payload) {U : R.Universe}
    (view : ℕ → R.View U) (T : Finset Validator) (lo : ℕ) : Prop :=
  ∀ hi, ∃ t, CoversOn R (view t) T lo hi

end Properties

end LeanDag
