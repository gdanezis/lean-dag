import LeanDag.Node.Helpers.Commits
/-!
# The decisions a node keeps

A node keeps the decisions it outputs (`State.decided`), the latest
first: along a run, read oldest first, they grow by exactly the decisions
output, and every proposal it sends at a height `k` is the head of the
chain of the first `k` of them (`Appends`). They are the slots
`0 … lo − 1` (`Ledger`): a decision step decides a run of slots from
`lo`, and a bootstrap takes a certificate's decisions from `lo` up to its
height. The head the node keeps is the chain's head at the height it last
proposed, at or below `lo`, so a proposal extends it by the decisions
since (`chain_step`).
-/

namespace LeanDag

namespace Node

variable {Validator BlockId Payload : Type} [Fintype Validator] [DecidableEq Validator]
variable [LinearOrder BlockId]
variable {cfg : Config Validator BlockId Payload}

variable (cfg) in
/-- **The kept decisions are the slots below the next undecided one**,
the latest first; the height last proposed lies at or below `lo`, and
the head kept is the chain's head there. -/
def Ledger (s : State Validator BlockId Payload) : Prop :=
  s.decided.reverse.map Prod.fst = List.range s.lo ∧ s.lastProposed ≤ s.lo ∧
    s.chain = cfg.headOf (s.decided.reverse.take s.lastProposed)

variable (cfg) in
/-- **A transition appends its decisions**: from `s` to `s'` with outputs
`out`, the kept decisions, read oldest first, grow by the decisions
output, and every proposal output at a height `k` is the head of the
chain of the first `k` of them. -/
def Appends (s : State Validator BlockId Payload) (out : List (Output Validator BlockId Payload))
    (s' : State Validator BlockId Payload) : Prop :=
  s'.decided.reverse = s.decided.reverse ++ commitsOf out ∧
    ∀ k h, Output.propose k h ∈ out → k ≤ s'.decided.length ∧
      h = cfg.headOf (s'.decided.reverse.take k)

omit [Fintype Validator] in
/-- A ledger with the same decisions, slot, height and head. -/
theorem Ledger.of_eq {s s' : State Validator BlockId Payload} (h : Ledger cfg s)
    (hd : s'.decided = s.decided) (hl : s'.lo = s.lo) (hp : s'.lastProposed = s.lastProposed)
    (hc : s'.chain = s.chain) : Ledger cfg s' := by
  unfold Ledger; rw [hd, hl, hp, hc]; exact h

omit [Fintype Validator] in
/-- The kept decisions number `lo`. -/
theorem Ledger.length {s : State Validator BlockId Payload} (h : Ledger cfg s) :
    s.decided.length = s.lo := by
  have := congrArg List.length h.1; simpa using this

omit [Fintype Validator] in
theorem Appends.trans {s s₁ s₂ : State Validator BlockId Payload}
    {o₁ o₂ : List (Output Validator BlockId Payload)} (h₁ : Appends cfg s o₁ s₁)
    (h₂ : Appends cfg s₁ o₂ s₂) : Appends cfg s (o₁ ++ o₂) s₂ := by
  refine ⟨by rw [h₂.1, h₁.1, commitsOf_append, List.append_assoc], fun k kh h => ?_⟩
  rcases List.mem_append.mp h with h | h
  · obtain ⟨hk, hkh⟩ := h₁.2 k kh h
    have hk' : k ≤ s₁.decided.reverse.length := by rw [List.length_reverse]; exact hk
    refine ⟨?_, ?_⟩
    · rw [← List.length_reverse, h₂.1, List.length_append]
      exact hk'.trans (Nat.le_add_right _ _)
    · rw [h₂.1, List.take_append_of_le_length hk']; exact hkh
  · exact h₂.2 k kh h

omit [Fintype Validator] in
/-- A transition that keeps the decisions and outputs neither a decision
nor a proposal. -/
theorem Appends.quiet {s s' : State Validator BlockId Payload}
    {out : List (Output Validator BlockId Payload)} (hd : s'.decided = s.decided)
    (hc : commitsOf out = []) (hp : ∀ k h, Output.propose k h ∉ out) : Appends cfg s out s' :=
  ⟨by rw [hd, hc, List.append_nil], fun k h hk => absurd hk (hp k h)⟩

omit [Fintype Validator] in
theorem Appends.refl (s : State Validator BlockId Payload) : Appends cfg s [] s :=
  Appends.quiet rfl rfl fun _ _ h => absurd h List.not_mem_nil

omit [Fintype Validator] in
theorem Appends.built {s s' : State Validator BlockId Payload}
    (bs : List (BlockId × Block Validator BlockId Payload)) (hd : s'.decided = s.decided) :
    Appends cfg s (built cfg bs) s' :=
  Appends.quiet hd (commitsOf_built bs) fun k h hk => by
    obtain ⟨e, -, he⟩ := List.mem_flatMap.mp hk
    simp at he

omit [Fintype Validator] in
/-- **Extending the head at `lp`** by the decisions `lp … k − 1`, the
latest `lo − lp` read off the decisions kept latest first, gives the head
at `k`. -/
theorem chain_step {D : List (ℕ × Option BlockId)} {lp k : ℕ} (hlp : lp ≤ k)
    (hk : k ≤ D.length) :
    ((D.reverse.take (D.length - lp)).reverse.take (k - lp)).foldl cfg.extend
      (cfg.headOf (D.take lp)) = cfg.headOf (D.take k) := by
  rw [List.take_reverse (xs := D), List.reverse_reverse,
    show D.length - (D.length - lp) = lp by omega, Config.headOf, Config.headOf,
    ← List.foldl_append, ← List.take_add, Nat.add_sub_cancel' hlp]

omit [Fintype Validator] in
/-- The next height lies above the height last proposed. -/
theorem lastProposed_lt_nextHeight (s : State Validator BlockId Payload) :
    s.lastProposed < nextHeight cfg s := by
  unfold nextHeight
  have := Nat.lt_mul_div_succ (max s.lastProposed s.certHeight) cfg.m_pos
  exact lt_of_le_of_lt (le_max_left _ _) this

omit [Fintype Validator] in
/-- **Proposing once keeps the ledger** and the decisions, and its
proposal at a height `k` is the head of the chain of the first `k`
decisions. -/
theorem proposeNext_ledger {s s₁ : State Validator BlockId Payload}
    {o : Output Validator BlockId Payload} (hL : Ledger cfg s)
    (hn : proposeNext cfg s = some (s₁, o)) :
    Ledger cfg s₁ ∧ s₁.decided = s.decided ∧ ∀ k h, o = Output.propose k h →
      k ≤ s.decided.length ∧ h = cfg.headOf (s.decided.reverse.take k) := by
  have hlen := hL.length
  obtain ⟨hk, rfl, rfl⟩ := proposeNext_some hn
  have hlt := lastProposed_lt_nextHeight (cfg := cfg) s
  have hD : s.decided.reverse.length = s.lo := by rw [List.length_reverse, hlen]
  have hh : ((s.decided.take (s.lo - s.lastProposed)).reverse.take
      (nextHeight cfg s - s.lastProposed)).foldl cfg.extend s.chain =
      cfg.headOf (s.decided.reverse.take (nextHeight cfg s)) := by
    have := chain_step (cfg := cfg) (D := s.decided.reverse) hlt.le (by rw [hD]; exact hk)
    rw [List.reverse_reverse, hD] at this
    rw [hL.2.2]; exact this
  refine ⟨⟨hL.1, hk, hh⟩, rfl, fun k h hp => ?_⟩
  rw [Output.propose.injEq] at hp
  obtain ⟨rfl, rfl⟩ := hp
  exact ⟨hlen ▸ hk, hh⟩

omit [Fintype Validator] in
theorem proposeFrom_ledger : ∀ (fuel : ℕ) {s : State Validator BlockId Payload},
    Ledger cfg s → Ledger cfg (proposeFrom cfg fuel s).1 ∧
      (proposeFrom cfg fuel s).1.decided = s.decided ∧
      ∀ k h, Output.propose k h ∈ (proposeFrom cfg fuel s).2 → k ≤ s.decided.length ∧
        h = cfg.headOf (s.decided.reverse.take k)
  | 0, s, hL => ⟨hL, rfl, fun k h hp => by simp [proposeFrom] at hp⟩
  | fuel + 1, s, hL => by
    rw [proposeFrom_succ]
    split
    · rename_i s₁ o hn
      obtain ⟨hL₁, hd₁, ho⟩ := proposeNext_ledger hL hn
      obtain ⟨hL₂, hd₂, hp₂⟩ := proposeFrom_ledger fuel hL₁
      refine ⟨hL₂, hd₂.trans hd₁, fun k h hp => ?_⟩
      rcases List.mem_cons.mp hp with hp | hp
      · exact ho k h hp.symm
      · rw [← hd₁]; exact hp₂ k h hp
    · exact ⟨hL, rfl, fun k h hp => by simp at hp⟩

omit [Fintype Validator] in
/-- **Proposing keeps the ledger** and the decisions, and a proposal at a
height `k` is the head of the chain of the first `k` decisions. -/
theorem proposeAt_ledger {s : State Validator BlockId Payload} (hL : Ledger cfg s) :
    Ledger cfg (proposeAt cfg s).1 ∧ (proposeAt cfg s).1.decided = s.decided ∧
      ∀ k h, Output.propose k h ∈ (proposeAt cfg s).2 → k ≤ s.decided.length ∧
        h = cfg.headOf (s.decided.reverse.take k) :=
  proposeFrom_ledger _ hL

omit [Fintype Validator] in
theorem tryBuild_appends {s s' : State Validator BlockId Payload}
    {out : List (Output Validator BlockId Payload)} (h : tryBuild cfg s = some (s', out)) :
    Appends cfg s out s' ∧ s'.lo = s.lo ∧ s'.lastProposed = s.lastProposed ∧
      s'.chain = s.chain := by
  unfold tryBuild at h
  split at h
  · dsimp only at h
    split at h
    · split at h
      · rw [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨Appends.quiet rfl rfl (by simp), rfl, rfl, rfl⟩
      · exact absurd h (by simp)
    · exact absurd h (by simp)
  · exact absurd h (by simp)

omit [Fintype Validator] in
theorem progress_appends : ∀ (fuel : ℕ) (s : State Validator BlockId Payload),
    Appends cfg s (progress cfg fuel s).2 (progress cfg fuel s).1 ∧
      (progress cfg fuel s).1.lo = s.lo ∧
      (progress cfg fuel s).1.lastProposed = s.lastProposed ∧
      (progress cfg fuel s).1.chain = s.chain
  | 0, s => ⟨Appends.refl s, rfl, rfl, rfl⟩
  | fuel + 1, s => by
    unfold Node.progress
    split
    · rename_i s₁ out h
      obtain ⟨h₁, hl₁, hp₁, hc₁⟩ := tryBuild_appends h
      obtain ⟨h₂, hl₂, hp₂, hc₂⟩ := progress_appends fuel s₁
      exact ⟨h₁.trans h₂, hl₂.trans hl₁, hp₂.trans hp₁, hc₂.trans hc₁⟩
    · exact ⟨Appends.refl s, rfl, rfl, rfl⟩

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
theorem decideStep_appends {s : State Validator BlockId Payload} (hL : Ledger cfg s) :
    Appends cfg s (decideStep cfg s).2 (decideStep cfg s).1 ∧ Ledger cfg (decideStep cfg s).1 := by
  unfold Node.decideStep
  dsimp only
  split
  · rename_i hlt
    generalize hds : Scheme.tryDecide (S := cfg.slots) cfg.p cfg.σ s.store.toRecord
      s.store.view s.lo (decidable cfg s.store.topRound - 1) = ds
    have hfst : ds.map Prod.fst = List.range' s.lo ds.length := by
      rw [← hds]; exact tryDecide_fst (S := cfg.slots) (by omega)
    set s₁ : State Validator BlockId Payload :=
      { s with lo := s.lo + ds.length, decided := ds.reverse ++ s.decided } with hs₁
    have hD₁ : s₁.decided.reverse = s.decided.reverse ++ ds := by
      simp [hs₁, List.reverse_append]
    have hL₁ : Ledger cfg s₁ := by
      have hlp : s.lastProposed ≤ s.decided.reverse.length := by
        rw [List.length_reverse, hL.length]; exact hL.2.1
      refine ⟨by rw [hD₁]; exact Ledger.append hL.1 hfst, hL.2.1.trans (Nat.le_add_right _ _), ?_⟩
      change s.chain = cfg.headOf (s₁.decided.reverse.take s.lastProposed)
      rw [hD₁, List.take_append_of_le_length hlp]; exact hL.2.2
    obtain ⟨hL₂, hdec, hprop⟩ := proposeAt_ledger (cfg := cfg) hL₁
    refine ⟨⟨?_, fun k h hp => ?_⟩, hL₂⟩
    · rw [hdec, hD₁, commitsOf_append, commitsOf_map, proposeAt_commits, List.append_nil]
    · rcases List.mem_append.mp hp with hp | hp
      · obtain ⟨e, -, he⟩ := List.mem_map.mp hp; cases he
      · rw [hdec]; exact hprop k h hp
  · obtain ⟨hL₂, hdec, hprop⟩ := proposeAt_ledger (cfg := cfg) hL
    refine ⟨⟨by rw [hdec, proposeAt_commits, List.append_nil], fun k h hp => ?_⟩, hL₂⟩
    rw [hdec]; exact hprop k h hp

omit [Fintype Validator] in
theorem collect_appends (s : State Validator BlockId Payload) :
    Appends cfg s (collect cfg s).2 (collect cfg s).1 ∧ (collect cfg s).1.lo = s.lo ∧
      (collect cfg s).1.decided = s.decided ∧ (collect cfg s).1.lastProposed = s.lastProposed ∧
      (collect cfg s).1.chain = s.chain := by
  have hf : (collect cfg s).1.lo = s.lo ∧ (collect cfg s).1.decided = s.decided ∧
      (collect cfg s).1.lastProposed = s.lastProposed ∧ (collect cfg s).1.chain = s.chain := by
    unfold Node.collect
    split
    · dsimp only
      split <;> exact ⟨rfl, rfl, rfl, rfl⟩
    · exact ⟨rfl, rfl, rfl, rfl⟩
  refine ⟨Appends.quiet hf.2.1 (commitsOf_collect s) fun k h hk => ?_, hf⟩
  rcases collect_out s _ hk with ⟨_, he⟩ | ⟨_, he⟩ <;> cases he

omit [Fintype Validator] in
theorem advance_appends {s : State Validator BlockId Payload} (hL : Ledger cfg s) :
    Appends cfg s (advance cfg s).2 (advance cfg s).1 ∧ Ledger cfg (advance cfg s).1 := by
  obtain ⟨h₁, hl₁, hp₁, hc₁⟩ := progress_appends (cfg := cfg) (s.store.topRound + 2) s
  have hL₁ : Ledger cfg (progress cfg (s.store.topRound + 2) s).1 := by
    have hd : (progress cfg (s.store.topRound + 2) s).1.decided = s.decided := by
      have := h₁.1
      rw [(progress_built (cfg := cfg) _ s).choose_spec, commitsOf_built, List.append_nil,
        List.reverse_inj] at this
      exact this
    exact hL.of_eq hd hl₁ hp₁ hc₁
  obtain ⟨h₂, hL₂⟩ := decideStep_appends (cfg := cfg) hL₁
  obtain ⟨h₃, hl₃, hd₃, hp₃, hc₃⟩ := collect_appends (cfg := cfg) (decideStep cfg (progress cfg
    (s.store.topRound + 2) s).1).1
  simp only [Node.advance]
  exact ⟨(h₁.trans h₂).trans h₃, hL₂.of_eq hd₃ hl₃ hp₃ hc₃⟩

omit [Fintype Validator] in
theorem settle_appends {s : State Validator BlockId Payload} (hL : Ledger cfg s) :
    Appends cfg s (settle cfg s).2 (settle cfg s).1 ∧ Ledger cfg (settle cfg s).1 := by
  rcases settle_cases (cfg := cfg) s with h | ⟨s₁, hr, h⟩ <;> rw [h]
  · exact advance_appends hL
  · obtain ⟨-, -, -, -, -, -, -, -, -, -, hlo, -⟩ := tryResume_some hr
    have hd : s₁.decided = s.decided ∧ s₁.lastProposed = s.lastProposed ∧
        s₁.chain = s.chain := by
      unfold tryResume at hr
      split at hr
      · dsimp only at hr
        split at hr
        · split at hr
          · rw [Option.some.injEq] at hr; subst hr; exact ⟨rfl, rfl, rfl⟩
          · cases hr
        · cases hr
      · cases hr
    obtain ⟨h₂, hL₂⟩ := advance_appends (cfg := cfg) (hL.of_eq hd.1 hlo hd.2.1 hd.2.2)
    exact ⟨(Appends.quiet hd.1 rfl fun _ _ h => absurd h List.not_mem_nil).trans h₂, hL₂⟩

omit [Fintype Validator] in
theorem bootFrom_appends {s : State Validator BlockId Payload} (hL : Ledger cfg s) :
    Appends cfg s (bootFrom cfg s).2 (bootFrom cfg s).1 ∧ Ledger cfg (bootFrom cfg s).1 := by
  rcases bootFrom_cases (cfg := cfg) s with he | ⟨s₂, ads, hb, he⟩ <;> rw [he]
  · exact ⟨Appends.refl s, hL⟩
  · obtain ⟨t, G, c, ds, hbG, -, -, -, hc, -, -, -, -, hlo, -, -, -, -, hads, hdec, -, -, hlp,
      hch, -⟩ := tryBoot_some hb
    obtain ⟨-, -, hcd, -⟩ := (validCert_iff (cfg := cfg)).mp (certFor_valid hc).2
    have hlen : s.decided.length = s.lo := hL.length
    have hD₂ : s₂.decided.reverse = s.decided.reverse ++ ads := by
      rw [hdec, List.reverse_append, List.reverse_reverse]
    have hL₂ : Ledger cfg s₂ := by
      have hlp' : s.lastProposed ≤ s.decided.reverse.length := by
        rw [List.length_reverse, hlen]; exact hL.2.1
      refine ⟨?_, ?_, ?_⟩
      · rw [hD₂, hlo, hads, List.map_append, hL.1, List.map_drop, hcd, hlen]
        rcases le_total s.lo c.height with h | h
        · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le h
          rw [max_eq_right h, List.range_eq_range' (n := c.height), List.drop_range', hk,
            Nat.add_sub_cancel_left, ← List.range_eq_range', List.range_add,
            List.range'_eq_map_range]
          simp
        · rw [max_eq_left h, List.drop_eq_nil_of_le (by simpa using h), List.append_nil]
      · rw [hlp, hlo]; exact hL.2.1.trans (le_max_left _ _)
      · rw [hlp, hch, hD₂, List.take_append_of_le_length hlp']; exact hL.2.2
    obtain ⟨h₃, hL₃⟩ := advance_appends (cfg := cfg) hL₂
    have h₁ : Appends cfg s
        (ads.map fun e => (Output.commit e.1 e.2 : Output Validator BlockId Payload)) s₂ :=
      ⟨by rw [hD₂, commitsOf_map], fun k h hp => by
        obtain ⟨e, -, he⟩ := List.mem_map.mp hp; cases he⟩
    exact ⟨h₁.trans h₃, hL₃⟩

omit [Fintype Validator] in
/-- **Adoptable decisions extend the node's chain to the certificate's
head.** -/
theorem adoptable_head {s : State Validator BlockId Payload} (hL : Ledger cfg s)
    {c : Cert Validator BlockId} {ds : List (ℕ × Option BlockId)}
    (ha : adoptable cfg s c ds = true) : cfg.headOf (s.decided.reverse ++ ds) = c.head := by
  unfold adoptable at ha
  simp only [Bool.and_eq_true, decide_eq_true_eq] at ha
  have hlen : s.decided.reverse.length = s.lo := by rw [List.length_reverse]; exact hL.length
  have hcs := chain_step (cfg := cfg) (D := s.decided.reverse) hL.2.1 (le_of_eq hlen.symm)
  have hX : ((s.decided.take (s.lo - s.lastProposed)).reverse).take (s.lo - s.lastProposed) =
      (s.decided.take (s.lo - s.lastProposed)).reverse :=
    List.take_of_length_le (by simp)
  rw [List.reverse_reverse, hlen, hX, ← hL.2.2, List.take_of_length_le (le_of_eq hlen)] at hcs
  rw [← ha.2, List.foldl_append, hcs, Config.headOf, Config.headOf, List.foldl_append]

omit [Fintype Validator] in
/-- **Adopted decisions keep the ledger**: the decisions, read oldest
first, grow by those served, up to the certificate's height. -/
theorem adopted_ledger {s : State Validator BlockId Payload} (hL : Ledger cfg s)
    {c : Cert Validator BlockId} {ds : List (ℕ × Option BlockId)}
    (ha : adoptable cfg s c ds = true) :
    Ledger cfg (adopted s c ds) ∧ (adopted s c ds).decided.reverse = s.decided.reverse ++ ds := by
  have hlt := adoptable_lo ha
  unfold adoptable at ha
  simp only [Bool.and_eq_true, decide_eq_true_eq] at ha
  have hds := ha.1.2
  have hlen : s.decided.length = s.lo := hL.length
  have hD : (adopted s c ds).decided.reverse = s.decided.reverse ++ ds := by
    simp [adopted, List.reverse_append]
  have hlp' : s.lastProposed ≤ s.decided.reverse.length := by
    rw [List.length_reverse, hlen]; exact hL.2.1
  refine ⟨⟨?_, ?_, ?_⟩, hD⟩
  · rw [hD, List.map_append, hL.1, hds]
    change List.range s.lo ++ List.range' s.lo (c.height - s.lo) = List.range c.height
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hlt.le
    rw [hk, Nat.add_sub_cancel_left, List.range_add, List.range'_eq_map_range]
  · exact hL.2.1.trans hlt.le
  · change s.chain = cfg.headOf ((adopted s c ds).decided.reverse.take s.lastProposed)
    rw [hD, List.take_append_of_le_length hlp']; exact hL.2.2

omit [Fintype Validator] in
theorem adopt_appends {s : State Validator BlockId Payload} (hL : Ledger cfg s)
    {c : Cert Validator BlockId} {ds : List (ℕ × Option BlockId)}
    (ha : adoptable cfg s c ds = true) :
    Appends cfg s (adopt cfg s c ds).2 (adopt cfg s c ds).1 ∧ Ledger cfg (adopt cfg s c ds).1 := by
  obtain ⟨hL₁, hD⟩ := adopted_ledger hL ha
  rw [adopt_eq]
  obtain ⟨h₂, hL₂⟩ := settle_appends (cfg := cfg) hL₁
  have h₁ : Appends cfg s
      (ds.map fun e => (Output.commit e.1 e.2 : Output Validator BlockId Payload))
      (adopted s c ds) :=
    ⟨by rw [hD, commitsOf_map], fun k h hp => by
      obtain ⟨e, -, he⟩ := List.mem_map.mp hp; cases he⟩
  exact ⟨h₁.trans h₂, hL₂⟩

/-- **A step appends its decisions**, and keeps the ledger. -/
theorem step_appends {s : State Validator BlockId Payload} (hL : Ledger cfg s)
    (i : Input Validator BlockId Payload) :
    Appends cfg s (Node.step cfg s i).2 (Node.step cfg s i).1 ∧
      Ledger cfg (Node.step cfg s i).1 := by
  have hset : ∀ (s₀ : State Validator BlockId Payload)
      (pre : List (Output Validator BlockId Payload)),
      s₀.decided = s.decided → s₀.lo = s.lo → s₀.lastProposed = s.lastProposed →
      s₀.chain = s.chain → commitsOf pre = [] → (∀ k h, Output.propose k h ∉ pre) →
      Appends cfg s (pre ++ (settle cfg s₀).2) (settle cfg s₀).1 ∧
        Ledger cfg (settle cfg s₀).1 := by
    intro s₀ pre hd hl hp' hc' hc hp
    obtain ⟨h₁, h₂⟩ := settle_appends (cfg := cfg) (hL.of_eq hd hl hp' hc')
    exact ⟨(Appends.quiet hd hc hp).trans h₁, h₂⟩
  cases i with
  | start =>
    simp only [Node.step]
    split
    · split
      · exact hset _ _ rfl rfl rfl rfl rfl (by simp)
      · exact ⟨Appends.refl s, hL⟩
    · exact ⟨Appends.refl s, hL⟩
  | deliver id b =>
    simp only [Node.step]
    split
    · refine hset _ _ rfl rfl rfl rfl ?_ ?_
      · simp only [commitsOf, List.filterMap_append]
        split_ifs <;> rfl
      · intro k h hk
        simp only [List.mem_append] at hk
        split_ifs at hk <;> simp_all
    · exact ⟨Appends.refl s, hL⟩
  | timer r => exact hset _ [] rfl rfl rfl rfl rfl (by simp)
  | restart => exact hset _ [.requestBase] rfl rfl rfl rfl rfl (by simp)
  | fetchRequest peer G ids =>
    refine ⟨Appends.quiet rfl ?_ fun k h hk => ?_, hL⟩
    · change commitsOf (answer s peer G ids) = []
      unfold answer commitsOf
      rw [List.filterMap_map]
      exact List.filterMap_eq_nil_iff.mpr fun _ _ => rfl
    · change Output.propose k h ∈ answer s peer G ids at hk
      unfold answer at hk
      obtain ⟨j, -, hj⟩ := List.mem_map.mp hk
      cases hj
  | baseRequest peer =>
    refine ⟨Appends.quiet rfl ?_ fun k h hk => ?_, hL⟩
    · change commitsOf (Output.serveBase peer s.store.base s.store.window ::
        s.cert.toList.map (fun c => Output.serveCert peer c
          (s.decided.drop (s.lo - c.height)).reverse)) = []
      cases s.cert <;> rfl
    · change Output.propose k h ∈ Output.serveBase peer s.store.base s.store.window ::
        s.cert.toList.map (fun c => Output.serveCert peer c
          (s.decided.drop (s.lo - c.height)).reverse) at hk
      cases hc : s.cert <;> simp [hc] at hk
  | proposal p k kh =>
    rw [step_proposal]
    split
    · obtain ⟨n, hn⟩ := seek_eq (cfg := cfg) (record cfg s p k kh) k kh
      rw [hn]
      refine ⟨Appends.quiet rfl
        (commitsOf_requests fun o ho => Or.inl (seek_out (cfg := cfg) _ k kh o ho))
        fun k' h' hk => ?_, hL.of_eq rfl rfl rfl rfl⟩
      obtain ⟨_, _, he⟩ := seek_out (cfg := cfg) _ k kh _ hk
      cases he
    · exact ⟨Appends.refl s, hL⟩
  | decisionRequest p lo =>
    rw [step_decisionRequest]
    have hout : ∀ o ∈ (if p ≠ cfg.me then serveFrom s p lo else []), ∃ c ds,
        o = Output.serveCert p c ds := fun o ho => by
      split at ho
      · exact serveFrom_out s p lo o ho
      · simp at ho
    refine ⟨Appends.quiet rfl
      (commitsOf_requests fun o ho => Or.inr ⟨p, hout o ho⟩) fun k h hk => ?_, hL⟩
    obtain ⟨_, _, he⟩ := hout _ hk
    cases he
  | baseOffer p G bs =>
    rw [step_offer]
    split
    · exact bootFrom_appends (s := withOffer s p G bs) hL
    · exact ⟨Appends.refl s, hL⟩
  | certOffer p c ds =>
    rcases certOffer_cases (cfg := cfg) s p c ds with ⟨-, -, he⟩ | ⟨-, ds', -, -, ha, he⟩ |
      ⟨-, -, -, he⟩ | ⟨-, he⟩ <;> rw [he]
    · exact bootFrom_appends (s := withCert s c ds) hL
    · exact adopt_appends hL ha
    · have h₀ : Ledger cfg { s with cert := some c, props := above (some c) s.props } := hL
      obtain ⟨ha, hL'⟩ := settle_appends h₀
      exact ⟨⟨ha.1, ha.2⟩, hL'⟩
    · exact ⟨Appends.refl s, hL⟩
  | announced p c =>
    rcases announced_cases (cfg := cfg) s p c with ⟨-, -, he⟩ | he | he <;> rw [he]
    · have h₀ : Ledger cfg { s with cert := some c, props := above (some c) s.props } := hL
      obtain ⟨ha, hL'⟩ := settle_appends h₀
      exact ⟨⟨ha.1, ha.2⟩, hL'⟩
    · refine ⟨Appends.quiet rfl rfl fun k h hk => ?_, hL⟩
      simp at hk
    · exact ⟨Appends.refl s, hL⟩

/-- **A run appends its decisions**, and keeps the ledger. -/
theorem run_appends : ∀ (is : List (Input Validator BlockId Payload))
    {s : State Validator BlockId Payload}, Ledger cfg s →
    Appends cfg s (Node.run cfg s is).2 (Node.run cfg s is).1 ∧
      Ledger cfg (Node.run cfg s is).1
  | [], s, hL => ⟨Appends.refl s, hL⟩
  | i :: is, s, hL => by
    obtain ⟨h₁, hL₁⟩ := step_appends (cfg := cfg) hL i
    obtain ⟨h₂, hL₂⟩ := run_appends is hL₁
    exact ⟨h₁.trans h₂, hL₂⟩

omit [Fintype Validator] in
theorem Ledger.init : Ledger cfg (State.init cfg) := ⟨rfl, le_rfl, rfl⟩

end Node

end LeanDag
