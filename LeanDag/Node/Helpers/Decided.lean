import LeanDag.Node.Helpers.Commits
/-!
# The decisions a node keeps

A node keeps the decisions it outputs (`State.decided`): along a run they
grow by exactly the decisions output, and every proposal it sends is a
prefix of them (`Appends`). They are the slots `0 … lo − 1`, in order
(`Ledger`): a decision step decides a run of slots from `lo`, and a
bootstrap takes a certificate's decisions from `lo` up to its height.
-/

namespace LeanDag

namespace Node

variable {Validator BlockId Payload : Type} [Fintype Validator] [DecidableEq Validator]
variable [LinearOrder BlockId]
variable {cfg : Config Validator BlockId Payload}

/-- **The kept decisions are the slots below the next undecided one**, in
order. -/
def Ledger (s : State Validator BlockId Payload) : Prop :=
  s.decided.map Prod.fst = List.range s.lo

/-- **A transition appends its decisions**: from `s` to `s'` with outputs
`out`, the kept decisions grow by the decisions output, and every
proposal output is a prefix of them. -/
def Appends (s : State Validator BlockId Payload) (out : List (Output Validator BlockId Payload))
    (s' : State Validator BlockId Payload) : Prop :=
  s'.decided = s.decided ++ commitsOf out ∧ ∀ k ds, Output.propose k ds ∈ out → ds <+: s'.decided

omit [Fintype Validator] in
theorem Appends.trans {s s₁ s₂ : State Validator BlockId Payload}
    {o₁ o₂ : List (Output Validator BlockId Payload)} (h₁ : Appends s o₁ s₁)
    (h₂ : Appends s₁ o₂ s₂) : Appends s (o₁ ++ o₂) s₂ := by
  refine ⟨by rw [h₂.1, h₁.1, commitsOf_append, List.append_assoc], fun k ds h => ?_⟩
  rcases List.mem_append.mp h with h | h
  · rw [h₂.1]; exact (h₁.2 k ds h).trans (List.prefix_append _ _)
  · exact h₂.2 k ds h

omit [Fintype Validator] in
/-- A transition that keeps the decisions and outputs neither a decision
nor a proposal. -/
theorem Appends.quiet {s s' : State Validator BlockId Payload}
    {out : List (Output Validator BlockId Payload)} (hd : s'.decided = s.decided)
    (hc : commitsOf out = []) (hp : ∀ k ds, Output.propose k ds ∉ out) : Appends s out s' :=
  ⟨by rw [hd, hc, List.append_nil], fun k ds h => absurd h (hp k ds)⟩

omit [Fintype Validator] in
theorem Appends.refl (s : State Validator BlockId Payload) : Appends s [] s :=
  Appends.quiet rfl rfl fun _ _ h => absurd h List.not_mem_nil

omit [Fintype Validator] in
theorem Appends.built {s s' : State Validator BlockId Payload}
    (bs : List (BlockId × Block Validator BlockId Payload)) (hd : s'.decided = s.decided) :
    Appends s (built cfg bs) s' :=
  Appends.quiet hd (commitsOf_built bs) fun k ds h => by
    obtain ⟨e, -, he⟩ := List.mem_flatMap.mp h
    simp at he

omit [Fintype Validator] in
theorem tryBuild_appends {s s' : State Validator BlockId Payload}
    {out : List (Output Validator BlockId Payload)} (h : tryBuild cfg s = some (s', out)) :
    Appends s out s' ∧ s'.lo = s.lo := by
  unfold tryBuild at h
  split at h
  · dsimp only at h
    split at h
    · split at h
      · rw [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨Appends.quiet rfl rfl (by simp), rfl⟩
      · exact absurd h (by simp)
    · exact absurd h (by simp)
  · exact absurd h (by simp)

omit [Fintype Validator] in
theorem progress_appends : ∀ (fuel : ℕ) (s : State Validator BlockId Payload),
    Appends s (progress cfg fuel s).2 (progress cfg fuel s).1 ∧
      (progress cfg fuel s).1.lo = s.lo
  | 0, s => ⟨Appends.refl s, rfl⟩
  | fuel + 1, s => by
    unfold Node.progress
    split
    · rename_i s₁ out h
      obtain ⟨h₁, hl₁⟩ := tryBuild_appends h
      obtain ⟨h₂, hl₂⟩ := progress_appends fuel s₁
      exact ⟨h₁.trans h₂, hl₂.trans hl₁⟩
    · exact ⟨Appends.refl s, rfl⟩

omit [DecidableEq Validator] [Fintype Validator] [LinearOrder BlockId] in
/-- The slots of a decided run from `lo` are `lo, lo + 1, …`. -/
theorem fst_takeWhile_range' {β : Type} (d : ℕ → β) (q : ℕ × β → Bool) :
    ∀ n lo, (((List.range' lo n).map fun k => (k, d k)).takeWhile q).map Prod.fst =
      List.range' lo (((List.range' lo n).map fun k => (k, d k)).takeWhile q).length
  | 0, lo => by simp
  | n + 1, lo => by
    rw [List.range'_succ, List.map_cons, List.takeWhile_cons]
    split
    · rw [List.map_cons, List.length_cons, List.range'_succ, fst_takeWhile_range' d q n (lo + 1)]
    · simp

omit [Fintype Validator] in
/-- **The slots `tryDecide` decides from `lo` are `lo, lo + 1, …`.** -/
theorem tryDecide_fst {P : Validity Validator BlockId Payload} {H : Finset Validator}
    {p : Scheme.Params} {σ : Scheme.VoteSel Validator BlockId Payload P H} [S : Slots Validator]
    {U : BlockRecord Validator BlockId Payload P H} {V : U.View} {lo N : ℕ} (hlo : lo ≤ N + 1) :
    (Scheme.tryDecide p σ U V lo N).map Prod.fst =
      List.range' lo (Scheme.tryDecide p σ U V lo N).length := by
  rw [Scheme.tryDecide_eq hlo, List.map_map, List.length_map]
  exact fst_takeWhile_range' _ _ _ _

omit [Fintype Validator] in
/-- Appending the run of slots from `lo` keeps the ledger. -/
theorem Ledger.append {lo : ℕ} {d ds : List (ℕ × Option BlockId)}
    (hd : d.map Prod.fst = List.range lo)
    (hds : ds.map Prod.fst = List.range' lo ds.length) :
    (d ++ ds).map Prod.fst = List.range (lo + ds.length) := by
  rw [List.map_append, hd, hds, List.range_add, List.range'_eq_map_range]

omit [Fintype Validator] in
theorem decideStep_appends {s : State Validator BlockId Payload} (hL : Ledger s) :
    Appends s (decideStep cfg s).2 (decideStep cfg s).1 ∧ Ledger (decideStep cfg s).1 := by
  unfold Node.decideStep
  dsimp only
  split
  · rename_i hlt
    generalize hds : Scheme.tryDecide (S := cfg.slots) cfg.p cfg.σ s.store.toRecord
      s.store.view s.lo (decidable cfg s.store.topRound - 1) = ds
    have hfst : ds.map Prod.fst = List.range' s.lo ds.length := by
      rw [← hds]; exact tryDecide_fst (S := cfg.slots) (by omega)
    set s₁ : State Validator BlockId Payload :=
      { s with lo := s.lo + ds.length, decided := s.decided ++ ds } with hs₁
    obtain ⟨-, -, -, -, -, hlo, -, -, -, hdec, -⟩ := proposeAt_keeps (cfg := cfg) s₁
    refine ⟨⟨?_, fun k d h => ?_⟩, ?_⟩
    · rw [hdec, commitsOf_append, commitsOf_map, proposeAt_commits, List.append_nil]
    · rcases List.mem_append.mp h with h | h
      · obtain ⟨e, -, he⟩ := List.mem_map.mp h; cases he
      · rw [hdec]
        unfold proposeAt at h
        dsimp only at h
        split at h
        · rw [List.mem_singleton, Output.propose.injEq] at h
          obtain ⟨-, rfl⟩ := h
          exact List.take_prefix _ _
        · exact absurd h List.not_mem_nil
    · unfold Ledger
      rw [hdec, hlo]
      exact Ledger.append hL hfst
  · exact ⟨Appends.refl s, hL⟩

omit [Fintype Validator] in
theorem collect_appends (s : State Validator BlockId Payload) :
    Appends s (collect cfg s).2 (collect cfg s).1 ∧ (collect cfg s).1.lo = s.lo := by
  unfold Node.collect
  split
  · dsimp only
    split
    · exact ⟨Appends.quiet rfl rfl (by simp), rfl⟩
    · exact ⟨Appends.refl s, rfl⟩
  · exact ⟨Appends.refl s, rfl⟩

omit [Fintype Validator] in
theorem advance_appends {s : State Validator BlockId Payload} (hL : Ledger s) :
    Appends s (advance cfg s).2 (advance cfg s).1 ∧ Ledger (advance cfg s).1 := by
  obtain ⟨h₁, hl₁⟩ := progress_appends (cfg := cfg) (s.store.topRound + 2) s
  have hL₁ : Ledger (progress cfg (s.store.topRound + 2) s).1 := by
    unfold Ledger
    have hd : (progress cfg (s.store.topRound + 2) s).1.decided = s.decided := by
      rw [h₁.1, (progress_built (cfg := cfg) _ s).choose_spec, commitsOf_built,
        List.append_nil]
    rw [hd, hl₁]; exact hL
  obtain ⟨h₂, hL₂⟩ := decideStep_appends (cfg := cfg) hL₁
  obtain ⟨h₃, hl₃⟩ := collect_appends (cfg := cfg) (decideStep cfg (progress cfg
    (s.store.topRound + 2) s).1).1
  simp only [Node.advance]
  refine ⟨(h₁.trans h₂).trans h₃, ?_⟩
  unfold Ledger
  change (collect cfg _).1.decided.map Prod.fst = List.range (collect cfg _).1.lo
  rw [hl₃, h₃.1, commitsOf_collect, List.append_nil]
  exact hL₂

omit [Fintype Validator] in
theorem settle_appends {s : State Validator BlockId Payload} (hL : Ledger s) :
    Appends s (settle cfg s).2 (settle cfg s).1 ∧ Ledger (settle cfg s).1 := by
  rcases settle_cases (cfg := cfg) s with h | ⟨s₁, hr, h⟩ <;> rw [h]
  · exact advance_appends hL
  · obtain ⟨-, -, -, -, -, -, -, -, -, -, hlo, -⟩ := tryResume_some hr
    have hd : s₁.decided = s.decided := by
      unfold tryResume at hr
      split at hr
      · dsimp only at hr
        split at hr
        · split at hr
          · rw [Option.some.injEq] at hr; subst hr; rfl
          · cases hr
        · cases hr
      · cases hr
    have hL₁ : Ledger s₁ := by unfold Ledger; rw [hd, hlo]; exact hL
    obtain ⟨h₂, hL₂⟩ := advance_appends (cfg := cfg) hL₁
    exact ⟨(Appends.quiet hd rfl fun _ _ h => absurd h List.not_mem_nil).trans h₂, hL₂⟩

omit [Fintype Validator] in
theorem bootFrom_appends {s : State Validator BlockId Payload} (hL : Ledger s) :
    Appends s (bootFrom cfg s).2 (bootFrom cfg s).1 ∧ Ledger (bootFrom cfg s).1 := by
  rcases bootFrom_cases (cfg := cfg) s with he | ⟨s₂, ads, hb, he⟩ <;> rw [he]
  · exact ⟨Appends.refl s, hL⟩
  · obtain ⟨t, G, c, hbG, -, -, -, hc, -, -, -, -, hlo, -, -, -, -, hads, hdec, -⟩ :=
      tryBoot_some hb
    obtain ⟨-, -, hcd, -⟩ := (validCert_iff (cfg := cfg)).mp (certFor_valid hc).2
    have hlen : s.decided.length = s.lo := by
      have := congrArg List.length hL; simpa using this
    have hL₂ : Ledger s₂ := by
      unfold Ledger
      rw [hdec, hlo, hads, List.map_append, hL, List.map_drop, hcd, hlen]
      rcases le_total s.lo c.height with h | h
      · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le h
        rw [max_eq_right h, List.range_eq_range' (n := c.height), List.drop_range', hk,
          Nat.add_sub_cancel_left, ← List.range_eq_range', List.range_add,
          List.range'_eq_map_range]
        simp
      · rw [max_eq_left h, List.drop_eq_nil_of_le (by simpa using h), List.append_nil]
    obtain ⟨h₃, hL₃⟩ := advance_appends (cfg := cfg) hL₂
    have h₁ : Appends s
        (ads.map fun e => (Output.commit e.1 e.2 : Output Validator BlockId Payload)) s₂ :=
      ⟨by rw [hdec, commitsOf_map], fun k ds h => by
        obtain ⟨e, -, he⟩ := List.mem_map.mp h; cases he⟩
    exact ⟨h₁.trans h₃, hL₃⟩

/-- **A step appends its decisions**, and keeps the ledger. -/
theorem step_appends {s : State Validator BlockId Payload} (hL : Ledger s)
    (i : Input Validator BlockId Payload) :
    Appends s (Node.step cfg s i).2 (Node.step cfg s i).1 ∧ Ledger (Node.step cfg s i).1 := by
  have hset : ∀ (s₀ : State Validator BlockId Payload)
      (pre : List (Output Validator BlockId Payload)),
      s₀.decided = s.decided → s₀.lo = s.lo → commitsOf pre = [] →
      (∀ k ds, Output.propose k ds ∉ pre) →
      Appends s (pre ++ (settle cfg s₀).2) (settle cfg s₀).1 ∧ Ledger (settle cfg s₀).1 := by
    intro s₀ pre hd hl hc hp
    have hL₀ : Ledger s₀ := by unfold Ledger; rw [hd, hl]; exact hL
    obtain ⟨h₁, h₂⟩ := settle_appends (cfg := cfg) hL₀
    exact ⟨(Appends.quiet hd hc hp).trans h₁, h₂⟩
  cases i with
  | start =>
    simp only [Node.step]
    split
    · split
      · exact hset _ _ rfl rfl rfl (by simp)
      · exact ⟨Appends.refl s, hL⟩
    · exact ⟨Appends.refl s, hL⟩
  | deliver id b =>
    simp only [Node.step]
    split
    · refine hset _ _ rfl rfl ?_ ?_
      · simp only [commitsOf, List.filterMap_append]
        split_ifs <;> rfl
      · intro k ds h
        simp only [List.mem_append] at h
        split_ifs at h <;> simp_all
    · exact ⟨Appends.refl s, hL⟩
  | timer r => exact hset _ [] rfl rfl rfl (by simp)
  | restart => exact hset _ [.requestBase] rfl rfl rfl (by simp)
  | fetchRequest peer ids =>
    refine ⟨Appends.quiet rfl ?_ fun k ds h => ?_, hL⟩
    · change commitsOf (answer s peer ids) = []
      unfold answer commitsOf
      rw [List.filterMap_map]
      exact List.filterMap_eq_nil_iff.mpr fun _ _ => rfl
    · change Output.propose k ds ∈ answer s peer ids at h
      unfold answer at h
      obtain ⟨j, -, hj⟩ := List.mem_map.mp h
      cases hj
  | baseRequest peer =>
    refine ⟨Appends.quiet rfl ?_ fun k ds h => ?_, hL⟩
    · change commitsOf (Output.serveBase peer s.store.base s.store.window ::
        s.cert.toList.map (Output.serveCert peer)) = []
      cases s.cert <;> rfl
    · change Output.propose k ds ∈ Output.serveBase peer s.store.base s.store.window ::
        s.cert.toList.map (Output.serveCert peer) at h
      cases hc : s.cert <;> simp [hc] at h
  | proposal p k ds =>
    rw [step_proposal]
    split
    · exact ⟨Appends.quiet rfl rfl (by simp), hL⟩
    · exact ⟨Appends.refl s, hL⟩
  | baseOffer p G bs =>
    rw [step_offer]
    split
    · exact bootFrom_appends (s := withOffer s p G bs) hL
    · exact ⟨Appends.refl s, hL⟩
  | certOffer p c =>
    rw [step_certOffer]
    split
    · exact bootFrom_appends (s := withCert s c) hL
    · exact ⟨Appends.refl s, hL⟩

/-- **A run appends its decisions**, and keeps the ledger. -/
theorem run_appends : ∀ (is : List (Input Validator BlockId Payload))
    {s : State Validator BlockId Payload}, Ledger s →
    Appends s (Node.run cfg s is).2 (Node.run cfg s is).1 ∧ Ledger (Node.run cfg s is).1
  | [], s, hL => ⟨Appends.refl s, hL⟩
  | i :: is, s, hL => by
    obtain ⟨h₁, hL₁⟩ := step_appends (cfg := cfg) hL i
    obtain ⟨h₂, hL₂⟩ := run_appends is hL₁
    exact ⟨h₁.trans h₂, hL₂⟩

omit [Fintype Validator] in
theorem Ledger.init : Ledger (State.init cfg) := rfl

end Node

end LeanDag
