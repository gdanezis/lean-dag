import LeanDag.Node.Order.Statement
import LeanDag.Node.Helpers.Run
import LeanDag.Node.Local.Proof
/-!
# The blocks a node orders — proof

An honest node keeps one decision for each slot below its next undecided
one (`Local.decisions`), so its verdict for a slot is that decision
(`verdictIn_of_mem`). Its decisions are one run of the scheme's loop on a
view of the run's record that its disk holds (`commitInv_before`), so each
committed leader lies in that view (`Scheme.tryDecide_mem_ids`), and the
ledger read from its disk is the record's (`ledgerOn_eq`). Each decision is
a verdict on the record (`cut_before`), and verdicts agree
(`AnchoredRule.decided_agree`), so two honest nodes' ledgers agree
(`bypassLedger_agree_of`).
-/

namespace LeanDag

namespace Node

namespace Order

variable {Validator BlockId Payload : Type} [Fintype Validator] [DecidableEq Validator]
variable [LinearOrder BlockId]

omit [Fintype Validator] [DecidableEq Validator] [LinearOrder BlockId] in
/-- **The verdict of a kept decision**, when the decisions name each slot once. -/
theorem verdictIn_of_mem :
    ∀ {ds : List (ℕ × Option BlockId)}, (ds.map Prod.fst).Nodup →
      ∀ {e : ℕ × Option BlockId}, e ∈ ds → verdictIn ds e.1 = e.2
  | [], _, _, he => absurd he List.not_mem_nil
  | d :: ds, hnd, e, he => by
    rw [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp he with rfl | he
    · simp [verdictIn]
    · have hne : d.1 ≠ e.1 := fun h => hnd.1 (by rw [h]; exact List.mem_map_of_mem he)
      have hb : (d.1 == e.1) = false := by simp [hne]
      have ih := verdictIn_of_mem hnd.2 he
      unfold verdictIn at ih ⊢
      simp only [List.find?_cons, hb]
      exact ih

variable {cfg : Config Validator BlockId Payload} {H : Finset Validator}
variable {tr : Trace Validator BlockId Payload}

/-- **What an honest node ordered is the record's ledger of its verdicts**,
held on its disk, and each of its verdicts is a verdict on the record. -/
theorem ordered_eq (hσ : cfg.σ = boundedSel) (hadm : cfg.Admissible) (hf : Hᶜ.card ≤ cfg.f)
    (htime : Converge.TimelyAuthentic cfg H tr) (hinj : Converge.HashInjective cfg H tr)
    (hdr : cfg.drops = false) {v : Validator} (hv : v ∈ H) (i n : ℕ)
    (hn : n ≤ (stateBefore cfg tr i v).lo) :
    let U := globalRecord (hashInjective_of_trace hinj) (authentic_of_timely htime)
    let s := stateBefore cfg tr i v
    s.ordered (S := cfg.slots) cfg.q n =
        bypassLedger (S := cfg.slots) U cfg.q (verdictIn s.decided) n ∧
      bypassLedger (S := cfg.slots) U cfg.q (verdictIn s.decided) n ⊆ s.disk.ids ∧
      ∀ k < n, Verdict (cfg.at v) U (k, verdictIn s.decided k) := by
  intro U s
  obtain ⟨hd, hmap⟩ := Local.decisions Validator BlockId Payload (cfg.at v) (inputsBefore tr i v)
  change s.decided.reverse = _ at hd
  change _ = List.range s.lo at hmap
  have hnd : (s.decided.map Prod.fst).Nodup := by
    have h := List.nodup_range (n := s.lo)
    rw [← hmap, ← hd, List.map_reverse] at h
    exact List.nodup_reverse.mp h
  have hmemk : ∀ k < s.lo, ∃ e ∈ commitsOf (run (cfg.at v) (State.init (cfg.at v))
      (inputsBefore tr i v)).2, e.1 = k ∧ verdictIn s.decided k = e.2 := by
    intro k hk
    have hk' : k ∈ (commitsOf (run (cfg.at v) (State.init (cfg.at v))
        (inputsBefore tr i v)).2).map Prod.fst := by
      rw [hmap]; exact List.mem_range.mpr hk
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hk'
    refine ⟨e, he, rfl, verdictIn_of_mem hnd ?_⟩
    rw [← List.mem_reverse, hd]
    exact he
  have hcut := cut_before hσ hadm hf htime hinj hdr i v hv
  have hn' : n ≤ s.lo := hn
  rcases commitInv_before hσ hadm hf htime hinj hdr hv i with h0 | ⟨V, N, hV, heq⟩
  · have hlo : s.lo = 0 := by
      have h := congrArg List.length hmap
      rw [h0] at h
      simpa using h.symm
    obtain rfl : n = 0 := by omega
    exact ⟨rfl, Finset.empty_subset _, fun k hk => absurd hk (Nat.not_lt_zero _)⟩
  · have hblk : ∀ x ∈ V.ids, s.disk.full x = U.block x := fun x hx => (hcut.1 x (hV hx)).2.symm
    have hlead : ∀ k < n, ∀ L, verdictIn s.decided k = some L → L ∈ V.ids := by
      intro k hk L hL
      obtain ⟨e, he, hek, hev⟩ := hmemk k (by omega)
      rw [heq] at he
      have he' : (k, some L) ∈ Scheme.tryDecide (S := cfg.slots) cfg.p boundedSel U V 0 N := by
        rw [← hek, ← hL, hev]
        exact he
      exact Scheme.tryDecide_mem_ids (S := cfg.slots) he'
    obtain ⟨h1, h2⟩ := ledgerOn_eq (S := cfg.slots) (q := cfg.q) V hblk n hlead
    refine ⟨h1, h2.trans hV, fun k hk => ?_⟩
    obtain ⟨e, he, hek, hev⟩ := hmemk k (by omega)
    rw [hev, ← hek]
    exact hcut.2 e he

theorem agrees : Agrees := by
  intro Validator BlockId Payload _ _ _ cfg H tr v w i j n hσ hadm hf htime hinj hdr hv hw hnv
    hnw
  obtain ⟨h1, -, hv'⟩ := ordered_eq hσ hadm hf htime hinj hdr hv i n hnv
  obtain ⟨h2, -, hw'⟩ := ordered_eq hσ hadm hf htime hinj hdr hw j n hnw
  rw [h1, h2]
  haveI : Validity.Quorate (ValidAt (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload) cfg.q Clause.none) cfg.q :=
    Validity.Quorate.of_validAt hadm.2.2.2.1 fun _ _ => Iff.rfl
  have ht : cfg.p.Tolerates H cfg.f cfg.q := ⟨hf, hadm.2.2.2.2, hadm.1⟩
  letI := cfg.slots
  obtain ⟨-, -, -, hlaws⟩ := Scheme.coveredLaws (boundedSel
    (P := ValidAt cfg.q Clause.none) (honest := H) (Validator := Validator) (BlockId := BlockId)
    (Payload := Payload)) ht
  refine bypassLedger_agree_of fun k hk => ?_
  obtain ⟨V₁, d₁⟩ := hv' k hk
  obtain ⟨V₂, d₂⟩ := hw' k hk
  exact AnchoredRule.decided_agree hlaws trivial d₁ d₂

theorem held : Held := by
  intro Validator BlockId Payload _ _ _ cfg H tr v i n hσ hadm hf htime hinj hdr hv hn
  obtain ⟨h1, h2, -⟩ := ordered_eq hσ hadm hf htime hinj hdr hv i n hn
  rw [h1]
  exact h2

/-- What a node orders. -/
theorem statement : Statement := ⟨agrees, held⟩

end Order

end Node

end LeanDag
