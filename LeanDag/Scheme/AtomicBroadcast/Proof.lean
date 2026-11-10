import LeanDag.Scheme.AtomicBroadcast.Statement
import LeanDag.Scheme.Helpers.Deliver
import LeanDag.Scheme.Loop.Proof
/-!
# Byzantine atomic broadcast — proof

The safety properties are the loop's prefix comparability and resumption
(`Loop.prefixComparable`, `Loop.resume`) carried through `deliverOf`,
which preserves prefixes and keeps one block per round and author
(`Helpers/Deliver.lean`). Agreement is eventual delivery among the
reliable validators: the view of one is eventually inside the view of
another, whose delivered sequence then extends the first one's.
-/

namespace LeanDag

namespace Scheme

namespace AtomicBroadcast

theorem grows : Grows := by
  intro Validator BlockId Payload _ _ _ P _ q _ honest f p σ S U V₁ V₂ N₁ N₂ ht hV hN
  exact deliverOf_prefix ⟨_, Loop.resume Validator BlockId Payload P q honest f p σ U V₁ V₂ 0 N₁ N₂
    ht hV hN⟩

theorem runGrows : RunGrows := by
  intro Validator BlockId Payload _ _ _ P _ q _ honest f p σ S U T N qp ap M ht v hv t t' htt
  exact grows Validator BlockId Payload P q honest f p σ U _ _ M M ht
    (ap.holds_mono v t t' htt) le_rfl

theorem integrity : Integrity := by
  intro Validator BlockId Payload _ _ _ P honest p σ S U V N r P_k
  refine length_filter_le_one (roundAuthor U) (deliverOf_nodup_roundAuthor _) _ ?_
  intro a c ha hc
  simp only [decide_eq_true_eq] at ha hc
  simp [roundAuthor, ha.1, ha.2, hc.1, hc.2]

theorem integritySD : IntegritySD := by
  intro Validator BlockId Payload _ _ _ P honest p σ S U V N
  exact ⟨deliverOf_nodup _, fun b hb => (mem_deliverOf hb).1⟩

/-- Two delivered sequences are prefix-comparable at the rows the
inequalities cover. -/
theorem deliverSeq_comparable {Validator BlockId Payload : Type} [Fintype Validator]
    [DecidableEq Validator] [LinearOrder BlockId] {P : Validity Validator BlockId Payload}
    [P.Mechanised] {q : ℕ} [P.Quorate q] {honest : Finset Validator} {f : ℕ} {p : Params}
    (σ : VoteSel Validator BlockId Payload P honest) [S : Slots Validator]
    (U : BlockRecord Validator BlockId Payload P honest) (V₁ V₂ : U.View) (N₁ N₂ : ℕ)
    (ht : p.Tolerates honest f q) :
    deliverSeq p σ U V₁ N₁ <+: deliverSeq p σ U V₂ N₂ ∨
      deliverSeq p σ U V₂ N₂ <+: deliverSeq p σ U V₁ N₁ :=
  (Loop.prefixComparable Validator BlockId Payload P q honest f p σ U V₁ V₂ 0 N₁ N₂ ht
    (Nat.zero_le _) (Nat.zero_le _)).imp deliverOf_prefix deliverOf_prefix

theorem totalOrder : TotalOrder := by
  intro Validator BlockId Payload _ _ _ P _ q _ honest f p σ S U V_i V_j N_i N_j x y ht h
  exact h.not_swap (deliverSeq_comparable σ U V_i V_j N_i N_j ht) (deliverOf_nodup _)
    (deliverOf_nodup _)

theorem totalOrderSD : TotalOrderSD := by
  intro Validator BlockId Payload _ _ _ P _ q _ honest f p σ S U V_i V_j N_i N_j x y ht h hy
  exact h.of_comparable (deliverSeq_comparable σ U V_i V_j N_i N_j ht) (deliverOf_nodup _) hy

theorem agreement : Agreement := by
  intro Validator BlockId Payload _ _ _ P _ q _ honest f p σ S U T N qp ap M ht P_i hi t b hb
    P_j hj
  obtain ⟨d, hd⟩ := ap.converges P_j hj P_i hi t
  refine ⟨t + d, fun t'' ht'' => ?_⟩
  have hsub : (ap.viewAt hi t).ids ⊆ (ap.viewAt hj t'').ids :=
    hd.trans (ap.holds_mono P_j _ _ ht'')
  exact (grows Validator BlockId Payload P q honest f p σ U _ _ M M ht hsub le_rfl).subset hb

theorem holds : Statement :=
  ⟨grows, runGrows, integrity, integritySD, totalOrder, totalOrderSD, agreement⟩

end AtomicBroadcast

end Scheme

end LeanDag
