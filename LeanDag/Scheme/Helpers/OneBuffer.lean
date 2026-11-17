import LeanDag.Scheme.Helpers.AsyncCoin
/-!
# The asynchronous rows: one buffer round, from the double count

With an honest population of the buffer round at least `q` strong, the
double count of `card_safeAt_count` gives
`q·(q − f) ≤ G·(2q − n) + |honest|·(n − q)`, `G` the safe set's size
(`card_safeAt_oneBuffer`). At `n ≥ 5f + 3c + 1` and `q = n − f − c` this
is `n ≤ 3G` (`card_safeAt_third`), so a uniform coin names a safe leader
with probability at least `1/3` (`third_le_coin`).
-/

namespace LeanDag

namespace Scheme

open scoped ENNReal

theorem one_buffer_arith {t G H n q f : ℕ}
    (hc : t * (q - f) + G * (n - q) ≤ G * t + H * (n - q)) (hqt : q ≤ t) (hqn : q ≤ n)
    (h2q : n ≤ 2 * q) (hH : q ≤ H + f) :
    q * (q - f) ≤ G * (2 * q - n) + H * (n - q) := by
  rcases le_or_gt q f with hqf | hfq
  · simp [Nat.sub_eq_zero_of_le hqf]
  obtain ⟨a, rfl⟩ : ∃ a, n = q + a := ⟨n - q, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b, q = f + b := ⟨q - f, by omega⟩
  have e1 : f + b + a - (f + b) = a := by omega
  have e2 : f + b - f = b := by omega
  have e3 : 2 * (f + b) - (f + b + a) = f + b - a := by omega
  rw [e1, e2] at hc
  rw [e1, e2, e3]
  obtain ⟨e, he⟩ : ∃ e, f + b = a + e := ⟨f + b - a, by omega⟩
  rw [he, show a + e - a = e by omega]
  rcases le_or_gt b G with hbG | hGb
  · nlinarith
  · nlinarith [Nat.mul_le_mul (show a + e ≤ t by omega) (show b - G ≤ b - G from le_rfl)]

theorem third_arith {G n q f c : ℕ} (h : q * (q - f) ≤ G * (2 * q - n) + n * (n - q))
    (hn : 5 * f + 3 * c + 1 ≤ n) (hq : q + f + c = n) : n ≤ 3 * G := by
  obtain ⟨d, rfl⟩ : ∃ d, n = 5 * f + 3 * c + 1 + d := ⟨n - (5 * f + 3 * c + 1), by omega⟩
  have hq' : q = 4 * f + 2 * c + 1 + d := by omega
  subst hq'
  have e1 : 4 * f + 2 * c + 1 + d - f = 3 * f + 2 * c + 1 + d := by omega
  have e2 : 2 * (4 * f + 2 * c + 1 + d) - (5 * f + 3 * c + 1 + d) = 3 * f + c + 1 + d := by omega
  have e3 : 5 * f + 3 * c + 1 + d - (4 * f + 2 * c + 1 + d) = f + c := by omega
  rw [e1, e2, e3] at h
  by_contra hlt
  push Not at hlt
  nlinarith

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [LinearOrder BlockId] {Payload : Type}
variable {P : Validity Validator BlockId Payload} {honest : Finset Validator}
variable [P.Mechanised] {q : ℕ} [P.Quorate q] {p : Params}
variable {U : BlockRecord Validator BlockId Payload P honest}

/-- **One buffer round, against a population at least `q` strong.** -/
theorem card_safeAt_oneBuffer {f r : ℕ} {T : Finset Validator} (hf : honestᶜ.card ≤ f)
    (hvo : 2 ≤ p.voteOffset) (hTh : T ⊆ honest) (hpop1 : PopulatedOn U T (r + 1))
    (hqT : q ≤ T.card) (h2q : Fintype.card Validator ≤ 2 * q) :
    q * (q - f) ≤ (safeAt p U r).card * (2 * q - Fintype.card Validator) +
      honest.card * (Fintype.card Validator - q) := by
  have hTn : T.card ≤ Fintype.card Validator := Finset.card_le_univ T
  have hH : honest.card + honestᶜ.card = Fintype.card Validator := Finset.card_add_card_compl _
  exact one_buffer_arith (card_safeAt_count hf hvo hTh hpop1 (by omega)) hqT (by omega) h2q
    (by omega)

/-- **One buffer round at `n ≥ 5f + 3c + 1`, `q = n − f − c`: a third of the
validators is safe.** -/
theorem card_safeAt_third {f c r : ℕ} {T : Finset Validator} (hf : honestᶜ.card ≤ f)
    (hvo : 2 ≤ p.voteOffset) (hTh : T ⊆ honest) (hpop1 : PopulatedOn U T (r + 1))
    (hqT : q ≤ T.card) (hn : 5 * f + 3 * c + 1 ≤ Fintype.card Validator)
    (hq : q + f + c = Fintype.card Validator) :
    Fintype.card Validator ≤ 3 * (safeAt p U r).card := by
  have h := card_safeAt_oneBuffer hf hvo hTh hpop1 hqT (by omega)
  have hH : honest.card * (Fintype.card Validator - q) ≤
      Fintype.card Validator * (Fintype.card Validator - q) :=
    Nat.mul_le_mul_right _ (Finset.card_le_univ _)
  exact third_arith (le_trans h (Nat.add_le_add_left hH _)) hn hq

/-- **A uniform coin lands in a set holding a third of the validators with
probability at least `1/3`.** -/
theorem third_le_coin [Nonempty Validator] {G : Finset Validator}
    (h : Fintype.card Validator ≤ 3 * G.card) :
    (1 : ℝ≥0∞) / 3 ≤ (PMF.uniformOfFintype Validator).toOuterMeasure ↑G := by
  rw [Steelhead.uniform_prob_mem]
  have hn : (Fintype.card Validator : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos (α := Validator)).ne'
  rw [ENNReal.le_div_iff_mul_le (Or.inl hn) (Or.inl (ENNReal.natCast_ne_top _)), one_div,
    mul_comm, ← div_eq_mul_inv, ENNReal.div_le_iff (by norm_num) (by norm_num), mul_comm]
  exact_mod_cast h

end Scheme

end LeanDag
