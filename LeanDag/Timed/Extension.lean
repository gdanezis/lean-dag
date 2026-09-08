import LeanDag.Timed.Coverage
import LeanDag.Properties.Extends
/-!
# Coverage under an extension

What a fill does to coverage, stated once for every rule: a reliable set
holding a novel block's author loses coverage at that block's round, and
one holding no such author keeps it, since an extension leaves old
blocks and their references unchanged (`Properties.Extends`).
-/

namespace LeanDag

namespace Timed

open Properties

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {R : DagRule Validator BlockId Payload}

/-- **An extension does not restore coverage** for a set that counts a
novel block's author reliable. An old reliable block at the round
above the novel one references only old identifiers, and coverage
would have it reference the novel one. -/
theorem not_synchronisedOn_of_extends {U U' : R.Universe} (he : Extends R U U')
    {T : Finset Validator} {R₀ k : ℕ} (hk : R₀ ≤ k)
    {f : BlockId} (hf : Novel R U U' f) (hfr : (R.block U' f).round = k)
    (hfc : (R.block U' f).creator ∈ T)
    {b : BlockId} (hb : b ∈ R.ids U) (hbr : (R.block U b).round = k + 1)
    (hbc : (R.block U b).creator ∈ T) :
    ¬ SynchronisedOn R U' T R₀ := by
  intro hs
  have hmem := hs k hk b (he.subset b hb) (by rw [he.block b hb]; exact hbr)
    (by rw [he.block b hb]; exact hbc) f hf.1 hfr hfc
  exact he.not_novel_of_mem_refs hb hmem hf

/-- **An extension preserves coverage** for a set holding no author of
a novel block: every block the clause reaches is old, and old blocks
are unchanged. -/
theorem synchronisedOn_of_extends {U U' : R.Universe} (he : Extends R U U')
    {T : Finset Validator} {R₀ : ℕ} (hs : SynchronisedOn R U T R₀)
    (hnew : ∀ b, Novel R U U' b → (R.block U' b).creator ∉ T) :
    SynchronisedOn R U' T R₀ := by
  intro n hn b hb hbr hbc a ha har hac
  have hbU : b ∈ R.ids U := by
    by_contra h; exact hnew b ⟨hb, h⟩ hbc
  have haU : a ∈ R.ids U := by
    by_contra h; exact hnew a ⟨ha, h⟩ hac
  rw [he.block b hbU] at hbr hbc ⊢
  rw [he.block a haU] at har hac
  exact hs n hn b hbU hbr hbc a haU har hac

end Timed

end LeanDag
