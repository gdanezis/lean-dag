import LeanDag.Node.Helpers.Hold
/-!
# A reliable node's certificate catches up

`docs/validator.md` §13.8. A reliable node given a good certificate above
its own, at a height it decided, confirms it (`confirms_of`); at a height
it did not decide, it asks the sender, which serves its certificate with
the decisions above the asked slot (`serveFrom_eq`), and adopts them if
they agree with its own (`adoptable_of`).
-/

namespace LeanDag

namespace Node

variable {Validator BlockId Payload : Type} [Fintype Validator] [DecidableEq Validator]
variable [LinearOrder BlockId]
variable {cfg : Config Validator BlockId Payload}

omit [Fintype Validator] in
/-- The chain extended by the decisions since the height last proposed and
more is the head of the decisions with them. -/
theorem chain_extend {s : State Validator BlockId Payload} (hL : Ledger cfg s)
    (ds : List (ℕ × Option BlockId)) :
    ((s.decided.take (s.lo - s.lastProposed)).reverse ++ ds).foldl cfg.extend s.chain =
      cfg.headOf (s.decided.reverse ++ ds) := by
  have hlen : s.decided.reverse.length = s.lo := by rw [List.length_reverse]; exact hL.length
  have hcs := chain_step (cfg := cfg) (D := s.decided.reverse) hL.2.1 (le_of_eq hlen.symm)
  have hX : ((s.decided.take (s.lo - s.lastProposed)).reverse).take (s.lo - s.lastProposed) =
      (s.decided.take (s.lo - s.lastProposed)).reverse :=
    List.take_of_length_le (by simp)
  rw [List.reverse_reverse, hlen, hX, ← hL.2.2, List.take_of_length_le (le_of_eq hlen)] at hcs
  rw [List.foldl_append, hcs, Config.headOf, Config.headOf, List.foldl_append]

omit [Fintype Validator] in
/-- **A node confirms a good certificate** above its own at a height it
decided, with the head of its decisions there. -/
theorem confirms_of {P : List (Validator × ℕ × BlockId)} {s : State Validator BlockId Payload}
    (hK : Kept cfg P s) (hcov : Covered cfg s) {c : Cert Validator BlockId}
    (hq : cfg.q ≤ c.signers.length) (hnd : c.signers.Nodup) (hm : cfg.m ∣ c.height)
    (hlt : s.certHeight < c.height) (hle : c.height ≤ s.lo)
    (hh : c.head = cfg.headOf (s.decided.reverse.take c.height)) : confirms cfg s c = true := by
  have hlp : c.height ≤ s.lastProposed := by
    by_contra h
    have := nextHeight_le (cfg := cfg) (s := s) hm (max_lt (not_le.mp h) hlt)
    unfold Covered at hcov
    omega
  have hown := hK.own_mem c.height (by omega) hm hlp hlt
  rw [← hh] at hown
  unfold confirms
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨⟨hq, hnd⟩, hlt⟩, hle⟩, hown⟩

omit [Fintype Validator] in
/-- **A node adopts decisions** served with a certificate of `q` distinct
signers at a multiple of `m` above its next undecided slot, the slots from
there to its height, whose chain from its own has the certificate's head. -/
theorem adoptable_of {s : State Validator BlockId Payload} (hL : Ledger cfg s)
    {c : Cert Validator BlockId} {ds : List (ℕ × Option BlockId)}
    (hq : cfg.q ≤ c.signers.length) (hnd : c.signers.Nodup) (hm : cfg.m ∣ c.height)
    (hlt : s.lo < c.height) (hds : ds.map Prod.fst = List.range' s.lo (c.height - s.lo))
    (hh : cfg.headOf (s.decided.reverse ++ ds) = c.head) : adoptable cfg s c ds = true := by
  unfold adoptable
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨⟨hq, hnd⟩, hlt, hm⟩, hds⟩, by rw [chain_extend hL]; exact hh⟩

omit [Fintype Validator] in
/-- **What a node serves** asked from slot `lo` below its certificate's
height: the certificate, with its decisions from `lo` to the height. -/
theorem serveFrom_eq {s : State Validator BlockId Payload} (hL : Ledger cfg s) {peer : Validator}
    {lo : ℕ} {c : Cert Validator BlockId} (hc : s.cert = some c) (hlo : lo < c.height)
    (hle : c.height ≤ s.lo) :
    serveFrom s peer lo = [.serveCert peer c ((s.decided.reverse.take c.height).drop lo)] := by
  have hlen : s.decided.length = s.lo := hL.length
  unfold serveFrom
  rw [hc]
  dsimp only
  rw [if_pos ⟨hlo, hle⟩, List.take_reverse, List.drop_reverse, hlen]
  congr 3
  rw [List.length_drop, hlen]
  congr 1
  omega

/-! ## Along a trace -/

variable {tr : Trace Validator BlockId Payload} {H : Finset Validator}

/-- **Two honest nodes' decisions are prefix-comparable**, before any
events, under the assumptions of agreement. -/
theorem decided_comparable (hσ : cfg.σ = boundedSel) (hadm : cfg.Admissible)
    (hf : Hᶜ.card ≤ cfg.f) (htime : Converge.TimelyAuthentic cfg H tr)
    (hoff : Boot.TimelyOffers cfg H tr) (hcert : Boot.TimelyCerts cfg H tr)
    (hinj : Converge.HashInjective cfg H tr) (hchain : Boot.ChainInjective cfg H tr)
    {u v : Validator} (hu : u ∈ H) (hv : v ∈ H) (i j : ℕ) :
    (stateBefore cfg tr i u).decided.reverse <+: (stateBefore cfg tr j v).decided.reverse ∨
      (stateBefore cfg tr j v).decided.reverse <+: (stateBefore cfg tr i u).decided.reverse := by
  haveI : Validity.Quorate (ValidAt (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload) cfg.q Clause.none) cfg.q :=
    Validity.Quorate.of_validAt hadm.2.2.2.1 fun _ _ => Iff.rfl
  have ht : cfg.p.Tolerates H cfg.f cfg.q := ⟨hf, hadm.2.2.2.2.1, hadm.1⟩
  have key := cut_before hσ hadm hf htime hoff hcert hinj hchain
  have hD : ∀ w t, (stateBefore cfg tr t w).decided.reverse =
      commitsOf (run (cfg.at w) (State.init (cfg.at w)) (inputsBefore tr t w)).2 :=
    fun w t => (Local.decisions _ _ _ (cfg.at w) (inputsBefore tr t w)).1
  have hL : ∀ w t, (commitsOf (run (cfg.at w) (State.init (cfg.at w))
      (inputsBefore tr t w)).2).map Prod.fst = List.range (commitsOf (run (cfg.at w)
        (State.init (cfg.at w)) (inputsBefore tr t w)).2).length := by
    intro w t
    obtain ⟨-, hfst, -⟩ := Local.decisions _ _ _ (cfg.at w) (inputsBefore tr t w)
    have hlen := congrArg List.length hfst
    simp only [List.length_map, List.length_range] at hlen
    rw [hfst, hlen]
  rw [hD, hD]
  refine prefix_of_slots (hL u i) (hL v j) fun k d d' hd hd' => ?_
  obtain ⟨V₁, h₁⟩ := (key i u hu).2 _ hd
  obtain ⟨V₂, h₂⟩ := (key j v hv).2 _ hd'
  letI := cfg.slots
  obtain ⟨-, -, -, hlaws⟩ := Scheme.coveredLaws (boundedSel (P := ValidAt cfg.q Clause.none)
    (honest := H) (Validator := Validator) (BlockId := BlockId) (Payload := Payload)) ht
  exact AnchoredRule.decided_agree hlaws trivial h₁ h₂

omit [Fintype Validator] [DecidableEq Validator] [LinearOrder BlockId] in
/-- Of two prefix-comparable lists, the first `k` agree, for `k` at most
both lengths. -/
theorem take_eq_of_comparable {α : Type} {l₁ l₂ : List α} (h : l₁ <+: l₂ ∨ l₂ <+: l₁) {k : ℕ}
    (h₁ : k ≤ l₁.length) (h₂ : k ≤ l₂.length) : l₁.take k = l₂.take k := by
  rcases h with ⟨t, rfl⟩ | ⟨t, rfl⟩
  · rw [List.take_append_of_le_length h₁]
  · rw [List.take_append_of_le_length h₂]

end Node

end LeanDag
