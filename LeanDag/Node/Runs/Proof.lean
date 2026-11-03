import LeanDag.Node.Runs.Statement
import LeanDag.Node.Cut.Proof
import LeanDag.Node.Local.Proof
/-!
# Many honest nodes — proof

An honest node's decisions are the slots `0, 1, …` in order
(`Local.decisions`), and two honest nodes decide each slot alike
(`Cut.agrees`), so the shorter list of decisions is a prefix of the longer
(`prefix_of_agree`).
-/

namespace LeanDag

namespace Node

namespace Runs

/-- **Two lists of decisions of the slots `0, 1, …` in order that agree on
each common slot are prefix-comparable.** -/
theorem prefix_of_agree {BlockId : Type} {L₁ L₂ : List (ℕ × Option BlockId)}
    (h₁ : L₁.map Prod.fst = List.range L₁.length) (h₂ : L₂.map Prod.fst = List.range L₂.length)
    (hag : ∀ e ∈ L₁, ∀ e' ∈ L₂, e.1 = e'.1 → e.2 = e'.2) : L₁ <+: L₂ ∨ L₂ <+: L₁ := by
  have hfst : ∀ (L : List (ℕ × Option BlockId)), L.map Prod.fst = List.range L.length →
      ∀ k (hk : k < L.length), L[k].1 = k := fun L h k hk => by
    have := congrArg (·[k]?) h
    simp only [List.getElem?_map, List.getElem?_range hk, List.getElem?_eq_getElem hk,
      Option.map_some, Option.some.injEq] at this
    exact this
  -- the shorter list is the longer one taken to its length
  have htake : ∀ (A B : List (ℕ × Option BlockId)), A.map Prod.fst = List.range A.length →
      B.map Prod.fst = List.range B.length → (∀ e ∈ A, ∀ e' ∈ B, e.1 = e'.1 → e.2 = e'.2) →
      A.length ≤ B.length → A <+: B := fun A B hA hB hAB hle => by
    have heq : A = B.take A.length := by
      refine List.ext_getElem (by simp [hle]) fun k hkA hkT => ?_
      have hkB : k < B.length := lt_of_lt_of_le hkA hle
      rw [List.getElem_take]
      have h1 := hfst A hA k hkA
      have h2 := hfst B hB k hkB
      exact Prod.ext (h1.trans h2.symm)
        (hAB _ (List.getElem_mem hkA) _ (List.getElem_mem hkB) (h1.trans h2.symm))
    rw [heq]
    exact List.take_prefix _ _
  rcases le_total L₁.length L₂.length with hle | hle
  · exact Or.inl (htake L₁ L₂ h₁ h₂ hag hle)
  · exact Or.inr (htake L₂ L₁ h₂ h₁ (fun e he e' he' hk => (hag e' he' e he hk.symm).symm) hle)

theorem safety : Safety := by
  intro Validator BlockId Payload _ _ _ cfg H tr hσ hadm hf htime hinj hid v hv w hw
  have hlen : ∀ u, (commitsOf (runOf cfg tr u).2).map Prod.fst =
      List.range (commitsOf (runOf cfg tr u).2).length := fun u => by
    obtain ⟨-, h⟩ := Local.decisions Validator BlockId Payload (cfg.at u)
      (inputsBefore tr tr.length u)
    change (commitsOf (runOf cfg tr u).2).map Prod.fst = List.range (runOf cfg tr u).1.lo at h
    rw [h, ← List.length_map (f := Prod.fst), h, List.length_range]
  exact prefix_of_agree (hlen v) (hlen w)
    (Cut.agrees Validator BlockId Payload cfg H tr hσ hadm hf htime hinj hid v hv w hw
      tr.length tr.length)

theorem holds : Statement := safety

end Runs

end Node

end LeanDag
