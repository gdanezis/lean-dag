import LeanDag.Node.Helpers.Steps
import LeanDag.Scheme.Helpers.Restart
/-!
# The decisions a node keeps

A node keeps the decisions it outputs (`State.decided`), the latest
first: along a run, read oldest first, they grow by exactly the decisions
output (`Appends`). They are the slots `0 … lo − 1` (`Ledger`): a
decision step decides a run of slots from `lo`.
-/

namespace LeanDag

namespace Node

variable {Validator BlockId Payload : Type} [Fintype Validator] [DecidableEq Validator]
variable [LinearOrder BlockId]
variable {cfg : Config Validator BlockId Payload}

omit [Fintype Validator] in
theorem commitsOf_built (bs : List (BlockId × Block Validator BlockId Payload)) :
    commitsOf (built cfg bs) = [] := by
  induction bs with
  | nil => rfl
  | cons e bs ih =>
    simp only [built, List.flatMap_cons] at ih ⊢
    rw [commitsOf_append, ih]
    rfl

omit [Fintype Validator] in
theorem commitsOf_map (ds : List (ℕ × Option BlockId)) :
    commitsOf (ds.map fun e => (Output.commit e.1 e.2 : Output Validator BlockId Payload)) =
      ds := by
  induction ds with
  | nil => rfl
  | cons e ds ih => simp only [List.map_cons, commitsOf, List.filterMap_cons] at ih ⊢; rw [ih]

/-- **The kept decisions are the slots below the next undecided one**,
the latest first. -/
def Ledger (s : State Validator BlockId Payload) : Prop :=
  s.decided.reverse.map Prod.fst = List.range s.lo

/-- **A transition appends its decisions**: from `s` to `s'` with outputs
`out`, the kept decisions, read oldest first, grow by the decisions
output. -/
def Appends (s : State Validator BlockId Payload) (out : List (Output Validator BlockId Payload))
    (s' : State Validator BlockId Payload) : Prop :=
  s'.decided.reverse = s.decided.reverse ++ commitsOf out

omit [Fintype Validator] in
/-- A ledger with the same decisions and slot. -/
theorem Ledger.of_eq {s s' : State Validator BlockId Payload} (h : Ledger s)
    (hd : s'.decided = s.decided) (hl : s'.lo = s.lo) : Ledger s' := by
  unfold Ledger; rw [hd, hl]; exact h

omit [Fintype Validator] in
/-- The kept decisions number `lo`. -/
theorem Ledger.length {s : State Validator BlockId Payload} (h : Ledger s) :
    s.decided.length = s.lo := by
  have := congrArg List.length h; simpa using this

omit [Fintype Validator] in
theorem Appends.trans {s s₁ s₂ : State Validator BlockId Payload}
    {o₁ o₂ : List (Output Validator BlockId Payload)} (h₁ : Appends s o₁ s₁)
    (h₂ : Appends s₁ o₂ s₂) : Appends s (o₁ ++ o₂) s₂ := by
  unfold Appends at *
  rw [h₂, h₁, commitsOf_append, List.append_assoc]

omit [Fintype Validator] in
/-- A transition that keeps the decisions and outputs none. -/
theorem Appends.quiet {s s' : State Validator BlockId Payload}
    {out : List (Output Validator BlockId Payload)} (hd : s'.decided = s.decided)
    (hc : commitsOf out = []) : Appends s out s' := by
  unfold Appends; rw [hd, hc, List.append_nil]

omit [Fintype Validator] in
theorem Appends.refl (s : State Validator BlockId Payload) : Appends s [] s :=
  Appends.quiet rfl rfl

omit [Fintype Validator] in
theorem tryBuild_appends {s s' : State Validator BlockId Payload}
    {out : List (Output Validator BlockId Payload)} (h : tryBuild cfg s = some (s', out)) :
    Appends s out s' ∧ s'.decided = s.decided ∧ s'.lo = s.lo := by
  obtain ⟨_, _, _, -, h, -⟩ := tryBuild_cases h
  unfold buildAbove at h
  dsimp only at h
  split at h
  · split at h
    · rw [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨Appends.quiet (release_decided _) rfl, release_decided _, release_lo _⟩
    · exact absurd h (by simp)
  · exact absurd h (by simp)

omit [Fintype Validator] in
theorem progress_appends : ∀ (fuel : ℕ) (s : State Validator BlockId Payload),
    Appends s (progress cfg fuel s).2 (progress cfg fuel s).1 ∧
      (progress cfg fuel s).1.decided = s.decided ∧ (progress cfg fuel s).1.lo = s.lo
  | 0, s => ⟨Appends.refl s, rfl, rfl⟩
  | fuel + 1, s => by
    unfold Node.progress
    split
    · rename_i s₁ out h
      obtain ⟨h₁, hd₁, hl₁⟩ := tryBuild_appends h
      obtain ⟨h₂, hd₂, hl₂⟩ := progress_appends fuel s₁
      exact ⟨h₁.trans h₂, hd₂.trans hd₁, hl₂.trans hl₁⟩
    · exact ⟨Appends.refl s, rfl, rfl⟩

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
    generalize hds : Scheme.tryDecide (S := cfg.slots) cfg.p cfg.σ
      (s.memory.window (cfg.slots.slotRound s.lo)) (s.memory.windowView (cfg.slots.slotRound s.lo))
      s.lo (decidable cfg s.disk.topRound - 1) = ds
    have hfst : ds.map Prod.fst = List.range' s.lo ds.length := by
      rw [← hds]; exact tryDecide_fst (S := cfg.slots) (by omega)
    have hD₁ : (ds.reverse ++ s.decided).reverse = s.decided.reverse ++ ds := by
      simp [List.reverse_append]
    unfold Appends Ledger
    simp only [release_decided, release_lo]
    refine ⟨?_, ?_⟩
    · change (ds.reverse ++ s.decided).reverse = s.decided.reverse ++ commitsOf (ds.map _)
      rw [hD₁, commitsOf_map]
    · change (ds.reverse ++ s.decided).reverse.map Prod.fst = List.range (s.lo + ds.length)
      rw [hD₁]; exact Ledger.append hL hfst
  · exact ⟨Appends.refl s, hL⟩

omit [Fintype Validator] in
theorem advance_appends {s : State Validator BlockId Payload} (hL : Ledger s) :
    Appends s (advance cfg s).2 (advance cfg s).1 ∧ Ledger (advance cfg s).1 := by
  obtain ⟨h₁, hd₁, hl₁⟩ := progress_appends (cfg := cfg) (s.disk.topRound + 2) s
  obtain ⟨h₂, hL₂⟩ := decideStep_appends (cfg := cfg) (hL.of_eq hd₁ hl₁)
  have h₃ := h₁.trans h₂
  unfold Appends Ledger at *
  simp only [Node.advance, Node.pass, release_decided, release_lo, arm_decided, arm_lo,
    flushSyncs_decided, flushSyncs_lo, commitsOf_append, commitsOf_arm, List.append_nil] at h₃ ⊢
  exact ⟨h₃, hL₂⟩

omit [Fintype Validator] in
theorem quiesce_appends (n : ℕ) {s : State Validator BlockId Payload} (hL : Ledger s) :
    Appends s (quiesce cfg n s).2 (quiesce cfg n s).1 ∧ Ledger (quiesce cfg n s).1 :=
  quiesce_rel (P := Ledger) (R := Appends) Appends.refl
    (fun _ _ _ _ _ h₁ h₂ => h₁.trans h₂) (fun _ h => advance_appends h) n s hL

omit [Fintype Validator] in
theorem settle_appends {s : State Validator BlockId Payload} (hL : Ledger s) :
    Appends s (settle cfg s).2 (settle cfg s).1 ∧ Ledger (settle cfg s).1 :=
  quiesce_appends _ hL

/-- **A step appends its decisions**, and keeps the ledger. -/
theorem step_appends {s : State Validator BlockId Payload} (hL : Ledger s)
    (i : Input Validator BlockId Payload) :
    Appends s (Node.step cfg s i).2 (Node.step cfg s i).1 ∧ Ledger (Node.step cfg s i).1 := by
  have hset : ∀ (s₀ : State Validator BlockId Payload)
      (pre : List (Output Validator BlockId Payload)),
      s₀.decided = s.decided → s₀.lo = s.lo → commitsOf pre = [] →
      Appends s (pre ++ (settle cfg s₀).2) (settle cfg s₀).1 ∧ Ledger (settle cfg s₀).1 := by
    intro s₀ pre hd hl hc
    obtain ⟨h₁, h₂⟩ := settle_appends (cfg := cfg) (hL.of_eq hd hl)
    exact ⟨(Appends.quiet hd hc).trans h₁, h₂⟩
  cases i with
  | start =>
    simp only [Node.step]
    split
    · split
      · exact hset _ _ rfl rfl rfl
      · exact ⟨Appends.refl s, hL⟩
    · exact ⟨Appends.refl s, hL⟩
  | deliver u id b =>
    rcases step_receipt (cfg := cfg) (s := s) (Or.inl ⟨u, id, b, rfl⟩) with
      h | ⟨s₁, pre, hr, hpre, h⟩
    · rw [h]; exact ⟨Appends.refl s, hL⟩
    · rw [h]
      refine hset _ _ hr.decided hr.lo (List.filterMap_eq_nil_iff.mpr fun o ho => ?_)
      obtain ⟨_, _, _, _, rfl⟩ := hpre o ho; rfl
  | stream u L =>
    rcases step_receipt (cfg := cfg) (s := s) (Or.inr ⟨u, L, rfl⟩) with h | ⟨s₁, pre, hr, hpre, h⟩
    · rw [h]; exact ⟨Appends.refl s, hL⟩
    · rw [h]
      refine hset _ _ hr.decided hr.lo (List.filterMap_eq_nil_iff.mpr fun o ho => ?_)
      obtain ⟨_, _, _, _, rfl⟩ := hpre o ho; rfl
  | timer r =>
    obtain ⟨h₁, h₂⟩ := hset { s with fired := fire s r, recovering := false } [] rfl rfl rfl
    rw [List.nil_append] at h₁
    simp only [Node.step]
    split
    · exact ⟨h₁.trans (Appends.quiet rfl (commitsOf_resend _)), h₂⟩
    · exact ⟨h₁, h₂⟩
  | syncRequest peer t fr ids =>
    refine ⟨Appends.quiet rfl ?_, hL⟩
    simp only [Node.step]
    split <;> rfl
  | ask peer r =>
    refine ⟨Appends.quiet rfl ?_, hL⟩
    simp only [Node.step]
    split
    · rfl
    · split <;> rfl
  | restart =>
    exact hset { s with recovering := true } (Node.resend cfg s ++ Node.rearm cfg s) rfl rfl
      (by rw [commitsOf_append, commitsOf_resend, commitsOf_rearm, List.append_nil])

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
