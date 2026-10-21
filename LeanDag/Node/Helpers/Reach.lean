import LeanDag.Node.Helpers.Wave
/-!
# What a node's store reaches

`docs/validator.md` §13.12. A node not recovering decides past its
certificate only slots at rounds its store holds, and proposes only
heights it decided past its certificate, so the height it last proposed,
and its next undecided slot unless its certificate covers it, lie within
the slots at its store's rounds (`Reached`). Each proposal it outputs is
at such a height, and its certificate rises past them only by a
certificate it adopted (`step_reached`).
-/

namespace LeanDag

namespace Node

variable {Validator BlockId Payload : Type} [Fintype Validator] [DecidableEq Validator]
variable [LinearOrder BlockId]
variable {cfg : Config Validator BlockId Payload}

variable (cfg) in
/-- **The store reaches what the node proposed and decided past its
certificate**: the height last proposed, and the next undecided slot
unless the certificate's height covers it, lie within the slots at the
store's rounds. -/
def Reached (s : State Validator BlockId Payload) : Prop :=
  s.lastProposed ≤ decidable cfg s.store.topRound ∧
    s.lo ≤ max s.certHeight (decidable cfg s.store.topRound)

omit [Fintype Validator] in
theorem Reached.mono {s s' : State Validator BlockId Payload} (h : Reached cfg s)
    (hlp : s'.lastProposed = s.lastProposed) (hlo : s'.lo = s.lo)
    (hc : s.certHeight ≤ s'.certHeight) (ht : s.store.topRound ≤ s'.store.topRound) :
    Reached cfg s' := by
  have hd := decidable_mono (cfg := cfg) ht
  refine ⟨by rw [hlp]; exact h.1.trans hd, by rw [hlo]; exact h.2.trans (max_le_max hc hd)⟩

omit [Fintype Validator] in
theorem Reached.init : Reached cfg (State.init cfg) := ⟨Nat.zero_le _, Nat.zero_le _⟩

omit [Fintype Validator] [DecidableEq Validator] in
/-- A stored block's round lies at or below the store's top round. -/
theorem le_topRound {st : Store Validator BlockId Payload} {j : BlockId} (hj : j ∈ st.ids) :
    (st.blk j).round ≤ st.topRound :=
  Finset.le_sup (f := fun i => (st.blk i).round) hj

omit [Fintype Validator] in
/-- The next height lies above the certificate's. -/
theorem certHeight_lt_nextHeight (s : State Validator BlockId Payload) :
    s.certHeight < nextHeight cfg s := by
  unfold nextHeight
  have := Nat.lt_mul_div_succ (max s.lastProposed s.certHeight) cfg.m_pos
  exact lt_of_le_of_lt (le_max_right _ _) this

/-! ## Through a pass -/

variable (cfg) in
/-- **What a pass keeps of the store's reach**, from `a` to `b` with outputs
`out`: the store's top round no lower, every proposal at a height within
the slots at its rounds, and the certificate's height raised at most to
them. -/
def Reaches (a : State Validator BlockId Payload) (out : List (Output Validator BlockId Payload))
    (b : State Validator BlockId Payload) : Prop :=
  a.store.topRound ≤ b.store.topRound ∧
    (∀ k h, Output.propose k h ∈ out → k ≤ decidable cfg b.store.topRound) ∧
    b.certHeight ≤ max a.certHeight (decidable cfg b.store.topRound)

omit [Fintype Validator] in
theorem Reaches.refl (s : State Validator BlockId Payload) : Reaches cfg s [] s :=
  ⟨le_rfl, fun _ _ h => absurd h List.not_mem_nil, le_max_left _ _⟩

omit [Fintype Validator] in
theorem Reaches.trans {a b c : State Validator BlockId Payload}
    {o₁ o₂ : List (Output Validator BlockId Payload)} (h₁ : Reaches cfg a o₁ b)
    (h₂ : Reaches cfg b o₂ c) : Reaches cfg a (o₁ ++ o₂) c := by
  have hd := decidable_mono (cfg := cfg) h₂.1
  refine ⟨h₁.1.trans h₂.1, fun k h hk => ?_, ?_⟩
  · rcases List.mem_append.mp hk with hk | hk
    · exact (h₁.2.1 k h hk).trans hd
    · exact h₂.2.1 k h hk
  · exact h₂.2.2.trans (max_le (h₁.2.2.trans (max_le_max le_rfl hd)) (le_max_right _ _))

omit [Fintype Validator] in
/-- Proposing keeps the store's reach, each proposal at a height within
it, the certificate raised at most to the height last proposed. -/
theorem proposeFrom_reached : ∀ (fuel : ℕ) {s : State Validator BlockId Payload},
    Reached cfg s → Reached cfg (proposeFrom cfg fuel s).1 ∧
      (proposeFrom cfg fuel s).1.store = s.store ∧
      (∀ k h, Output.propose k h ∈ (proposeFrom cfg fuel s).2 →
        k ≤ decidable cfg s.store.topRound) ∧
      (proposeFrom cfg fuel s).1.certHeight ≤ max s.certHeight (decidable cfg s.store.topRound)
  | 0, s, h => ⟨h, rfl, fun _ _ hk => by simp [proposeFrom] at hk, le_max_left _ _⟩
  | fuel + 1, s, h => by
    rw [proposeFrom_succ]
    split
    · rename_i s₁ o hn
      obtain ⟨hk, rfl, rfl⟩ := proposeNext_some hn
      set hd := ((s.decided.take (s.lo - s.lastProposed)).reverse.take
          (nextHeight cfg s - s.lastProposed)).foldl cfg.extend s.chain
      set x := certifyAt cfg { s with lastProposed := nextHeight cfg s, chain := hd }
        (nextHeight cfg s) hd
      have hlt := certHeight_lt_nextHeight (cfg := cfg) s
      have hkD : nextHeight cfg s ≤ decidable cfg s.store.topRound := by
        have := h.2; rw [max_def] at this; split at this <;> omega
      have hxc := certifyAt_cert_le (cfg := cfg)
        { s with lastProposed := nextHeight cfg s, chain := hd } (nextHeight cfg s) hd
      have hxc' := certifyAt_certHeight (cfg := cfg)
        { s with lastProposed := nextHeight cfg s, chain := hd } (nextHeight cfg s) hd
      have hx : Reached cfg x := by
        refine ⟨hkD, ?_⟩
        change s.lo ≤ max x.certHeight (decidable cfg s.store.topRound)
        exact h.2.trans (max_le_max hxc' le_rfl)
      have hxD : x.certHeight ≤ max s.certHeight (decidable cfg s.store.topRound) := by
        rcases hxc with hxc | hxc
        · exact (le_of_eq hxc).trans (le_max_left _ _)
        · exact hxc.trans (hkD.trans (le_max_right _ _))
      obtain ⟨h₁, h₂, h₃, h₄⟩ := proposeFrom_reached fuel hx
      refine ⟨h₁, h₂, fun k' h' hk' => ?_, ?_⟩
      · rcases List.mem_cons.mp hk' with he | hk'
        · rw [Output.propose.injEq] at he; rw [he.1]; exact hkD
        · exact h₃ k' h' hk'
      · exact h₄.trans (max_le hxD (le_max_right _ _))
    · exact ⟨h, rfl, fun _ _ hk => by simp at hk, le_max_left _ _⟩

omit [Fintype Validator] in
/-- **Deciding keeps the store's reach**: it decides only slots at rounds
the store holds, and proposes and certifies within them. -/
theorem decideStep_reached {s : State Validator BlockId Payload} (h : Reached cfg s) :
    Reached cfg (decideStep cfg s).1 ∧ Reaches cfg s (decideStep cfg s).2 (decideStep cfg s).1 := by
  have hst := decideStep_store (cfg := cfg) s
  unfold Node.decideStep at hst ⊢
  dsimp only at hst ⊢
  split
  · rename_i hlt
    generalize hds : Scheme.tryDecide (S := cfg.slots) cfg.p cfg.σ s.store.toRecord
      s.store.view s.lo (decidable cfg s.store.topRound - 1) = ds
    have hlen : ds.length ≤ decidable cfg s.store.topRound - 1 + 1 - s.lo := by
      rw [← hds]; exact tryDecide_length_le (S := cfg.slots) (by omega)
    set x : State Validator BlockId Payload :=
      { s with
        lo := s.lo + ds.length
        decided := ds.reverse ++ s.decided }
    have hx : Reached cfg x := by
      refine ⟨h.1, ?_⟩
      change s.lo + ds.length ≤ max s.certHeight (decidable cfg s.store.topRound)
      have := le_max_right s.certHeight (decidable cfg s.store.topRound)
      omega
    obtain ⟨h₁, h₂, h₃, h₄⟩ := proposeFrom_reached (cfg := cfg) (s.lo + ds.length + 1) hx
    refine ⟨h₁, ?_, fun k hh hk => ?_, ?_⟩
    · change s.store.topRound ≤ (proposeAt cfg x).1.store.topRound
      unfold proposeAt; rw [h₂]
    · rcases List.mem_append.mp hk with hk | hk
      · obtain ⟨_, -, he⟩ := List.mem_map.mp hk; cases he
      · change k ≤ decidable cfg (proposeAt cfg x).1.store.topRound
        unfold proposeAt; rw [h₂]; exact h₃ k hh hk
    · change (proposeAt cfg x).1.certHeight ≤
        max s.certHeight (decidable cfg (proposeAt cfg x).1.store.topRound)
      unfold proposeAt; rw [h₂]; exact h₄
  · obtain ⟨h₁, h₂, h₃, h₄⟩ := proposeFrom_reached (cfg := cfg) (s.lo + 1) h
    refine ⟨h₁, ?_, fun k hh hk => ?_, ?_⟩
    · unfold proposeAt; rw [h₂]
    · unfold proposeAt; rw [h₂]; exact h₃ k hh hk
    · unfold proposeAt; rw [h₂]; exact h₄

omit [Fintype Validator] in
/-- **Building keeps the store's reach**, the store grown by the new block. -/
theorem tryBuild_reached {s s' : State Validator BlockId Payload}
    {out : List (Output Validator BlockId Payload)} (h : tryBuild cfg s = some (s', out))
    (hR : Reached cfg s) : Reached cfg s' ∧ Reaches cfg s out s' := by
  obtain ⟨r, id, b, hnew, hab, hrefs, hpred, -, -, -, -, -, hst, -, -, -, hout⟩ := tryBuild_some h
  obtain ⟨-, hc, hlo, hlp, -, -⟩ := tryBuild_frame h
  have hc' : s'.certHeight = s.certHeight := by simp [State.certHeight, hc]
  have ht : s.store.topRound ≤ s'.store.topRound := by
    rw [hst]; exact (Grows.insert s.store).topRound rfl
  refine ⟨hR.mono hlp hlo hc'.ge ht, ht, fun k hh hk => ?_, by rw [hc']; exact le_max_left _ _⟩
  rw [hout] at hk
  simp [built] at hk

omit [Fintype Validator] in
theorem progress_reached : ∀ (fuel : ℕ) {s : State Validator BlockId Payload}, Reached cfg s →
    Reached cfg (progress cfg fuel s).1 ∧
      Reaches cfg s (progress cfg fuel s).2 (progress cfg fuel s).1
  | 0, s, h => ⟨h, Reaches.refl s⟩
  | fuel + 1, s, h => by
    unfold Node.progress
    split
    · rename_i s₁ out hb
      obtain ⟨h₁, h₂⟩ := tryBuild_reached hb h
      obtain ⟨h₃, h₄⟩ := progress_reached fuel h₁
      exact ⟨h₃, h₂.trans h₄⟩
    · exact ⟨h, Reaches.refl s⟩

omit [Fintype Validator] in
/-- **Raising the horizon keeps the store's reach**, below a top the store
holds. -/
theorem collect_reached {s : State Validator BlockId Payload} (hR : Reached cfg s)
    (ht : ∀ t, s.top = some t → t ≤ s.store.topRound) :
    Reached cfg (collect cfg s).1 ∧ Reaches cfg s (collect cfg s).2 (collect cfg s).1 := by
  have key : (collect cfg s).1.lastProposed = s.lastProposed ∧
      (collect cfg s).1.certHeight = s.certHeight ∧ (collect cfg s).1.lo = s.lo ∧
      s.store.topRound ≤ (collect cfg s).1.store.topRound ∧
      ∀ k h, Output.propose k h ∉ (collect cfg s).2 := by
    unfold Node.collect
    split
    · rename_i t htop
      dsimp only
      split
      · rename_i hG
        refine ⟨rfl, rfl, rfl, (Keeps.prune_top s.store hG.le
          ((horizonAt_le_top s t).trans (ht t htop))).2.2, fun k h hk => ?_⟩
        simp only [List.mem_cons, List.mem_map] at hk
        rcases hk with hk | ⟨c, -, hk⟩ <;> cases hk
      · exact ⟨rfl, rfl, rfl, le_rfl, fun _ _ h => absurd h List.not_mem_nil⟩
    · exact ⟨rfl, rfl, rfl, le_rfl, fun _ _ h => absurd h List.not_mem_nil⟩
  obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := key
  exact ⟨hR.mono h₁ h₃ h₂.ge h₄, h₄, fun k h hk => absurd hk (h₅ k h),
    by rw [h₂]; exact le_max_left _ _⟩

omit [Fintype Validator] in
/-- **A pass keeps the store's reach**, the node's own block at its top
stored. -/
theorem advance_reached {s : State Validator BlockId Payload} (hR : Reached cfg s)
    (ho : OwnTop cfg s) :
    Reached cfg (advance cfg s).1 ∧ Reaches cfg s (advance cfg s).2 (advance cfg s).1 := by
  simp only [Node.advance]
  obtain ⟨hb, hbr⟩ := progress_reached (cfg := cfg) (s.store.topRound + 2) hR
  have hbo := OwnTop.progress (cfg := cfg) (s.store.topRound + 2) ho
  generalize Node.progress cfg (s.store.topRound + 2) s = b at hb hbr hbo
  obtain ⟨hd, hdr⟩ := decideStep_reached (cfg := cfg) hb
  have hdt : ∀ t, (decideStep cfg b.1).1.top = some t →
      t ≤ (decideStep cfg b.1).1.store.topRound := by
    intro t htd
    rw [decideStep_top] at htd
    rw [decideStep_store]
    obtain ⟨j, -, hj, hjr, -⟩ := hbo t htd
    exact hjr ▸ le_topRound hj
  generalize decideStep cfg b.1 = d at hd hdr hdt
  obtain ⟨hg, hgr⟩ := collect_reached (cfg := cfg) hd hdt
  generalize collect cfg d.1 = g at hg hgr
  generalize hfl : flush cfg (g.1.pending.length + 1) g.1.store g.1.pending = fl
  have hft : g.1.store.topRound ≤ fl.1.topRound := by
    rw [← hfl]; exact (Grows.flush _ _ _).topRound (flush_base _ _ _)
  have hf : Reached cfg
      { g.1 with
        store := fl.1
        pending := fl.2 } :=
    hg.mono rfl rfl le_rfl hft
  have hfin : Reaches cfg g.1 []
      { g.1 with
        store := fl.1
        pending := fl.2 } :=
    ⟨hft, fun _ _ h => absurd h List.not_mem_nil, le_max_left _ _⟩
  have := (hbr.trans hdr).trans (hgr.trans hfin)
  rw [List.append_nil] at this
  exact ⟨hf, this⟩

omit [Fintype Validator] in
/-- **Settling a node not recovering keeps the store's reach.** -/
theorem settle_reached {s : State Validator BlockId Payload} (hR : Reached cfg s)
    (ho : OwnTop cfg s) (hs : s.recovering = false) :
    Reached cfg (settle cfg s).1 ∧ Reaches cfg s (settle cfg s).2 (settle cfg s).1 := by
  rw [settle_of_idle hs]
  have := quiesce_rel (cfg := cfg) (P := fun x => Reached cfg x ∧ OwnTop cfg x)
    (R := fun a out b => Reaches cfg a out b) Reaches.refl (fun _ _ _ _ _ h₁ h₂ => h₁.trans h₂)
    (fun x hx => ⟨(advance_reached hx.1 hx.2).2, (advance_reached hx.1 hx.2).1,
      OwnTop.advance hx.2⟩) (passes cfg s) s ⟨hR, ho⟩
  exact ⟨this.2.1, this.1⟩

/-! ## Through a step -/

variable (cfg) in
/-- **The certificate's height after a step**, from `s` to `s'` on input
`inp`: raised at most to the slots at the store's rounds, or adopted from a
certificate offered with `q` distinct signers. -/
def CertBound (s : State Validator BlockId Payload) (inp : Input Validator BlockId Payload)
    (s' : State Validator BlockId Payload) : Prop :=
  s'.certHeight ≤ max s.certHeight (decidable cfg s'.store.topRound) ∨
    ∃ p c ds, inp = .certOffer p c ds ∧ cfg.q ≤ c.signers.length ∧ c.signers.Nodup ∧
      s'.certHeight ≤ max c.height (decidable cfg s'.store.topRound)

/-- **A step keeps the store's reach**, of a node not recovering, other
than a restart and a timer that finds it stalled twice: the store's top
round no lower, each proposal at a height within the slots at its rounds,
and the certificate's height bounded (`CertBound`). -/
theorem step_reached {s : State Validator BlockId Payload} {inp : Input Validator BlockId Payload}
    (hR : Reached cfg s) (ho : OwnTop cfg s) (hs : s.recovering = false) (hr : inp ≠ .restart)
    (hst : ∀ r, inp = .timer r → stallsTwice cfg s r = false) :
    Reached cfg (Node.step cfg s inp).1 ∧
      s.store.topRound ≤ (Node.step cfg s inp).1.store.topRound ∧
      (∀ k h, Output.propose k h ∈ (Node.step cfg s inp).2 →
        k ≤ decidable cfg (Node.step cfg s inp).1.store.topRound) ∧
      CertBound cfg s inp (Node.step cfg s inp).1 := by
  -- a step that settles a state reaching what `s` does, after outputs proposing nothing
  have hset : ∀ (x : State Validator BlockId Payload)
      (pre : List (Output Validator BlockId Payload)),
      Reached cfg x → OwnTop cfg x → x.recovering = false →
      s.store.topRound ≤ x.store.topRound → (∀ k h, Output.propose k h ∉ pre) →
      CertBound cfg s inp x →
      Reached cfg (Node.settle cfg x).1 ∧
        s.store.topRound ≤ (Node.settle cfg x).1.store.topRound ∧
        (∀ k h, Output.propose k h ∈ pre ++ (Node.settle cfg x).2 →
          k ≤ decidable cfg (Node.settle cfg x).1.store.topRound) ∧
        CertBound cfg s inp (Node.settle cfg x).1 := by
    intro x pre hx hxo hxs hxt hpre hxc
    obtain ⟨h₁, h₂, h₃, h₄⟩ := settle_reached hx hxo hxs
    have hd := decidable_mono (cfg := cfg) h₂
    refine ⟨h₁, hxt.trans h₂, fun k h hk => ?_, ?_⟩
    · rcases List.mem_append.mp hk with hk | hk
      · exact absurd hk (hpre k h)
      · exact h₃ k h hk
    · rcases hxc with hxc | ⟨p, c, ds, hi, hq, hnd, hxc⟩
      · exact Or.inl (h₄.trans (max_le (hxc.trans (max_le_max le_rfl hd)) (le_max_right _ _)))
      · exact Or.inr ⟨p, c, ds, hi, hq, hnd,
          h₄.trans (max_le (hxc.trans (max_le_max le_rfl hd)) (le_max_right _ _))⟩
  -- a step that leaves the state alone, its outputs proposing nothing
  have hnil : ∀ out : List (Output Validator BlockId Payload), (∀ k h, Output.propose k h ∉ out) →
      Reached cfg s ∧ s.store.topRound ≤ s.store.topRound ∧
        (∀ k h, Output.propose k h ∈ out → k ≤ decidable cfg s.store.topRound) ∧
        CertBound cfg s inp s :=
    fun out hout => ⟨hR, le_rfl, fun k h hk => absurd hk (hout k h), Or.inl (le_max_left _ _)⟩
  have hself : CertBound cfg s inp s := Or.inl (le_max_left _ _)
  cases inp with
  | start =>
    simp only [Node.step]
    split
    · split
      · rename_i h₁ h₂
        have ht := (Grows.insert s.store (hnew := h₂.1) (hab := h₂.2.1)
          (hrefs := fun _ => Finset.empty_subset _)
          (hpred := fun _ j hj => absurd hj (Finset.notMem_empty j))).topRound rfl
        refine hset _ _ (hR.mono rfl rfl le_rfl ht) (fun r hr => ?_) rfl ht (by simp)
          (Or.inl (le_max_left _ _))
        change some 0 = some r at hr
        rw [Option.some.injEq] at hr
        subst hr
        refine ⟨_, rfl, Finset.mem_insert_self _ _, ?_, ?_⟩ <;>
          simp [Store.blk, Store.insert, lookup, Std.TreeMap.getD_insert_self, Config.genesis]
      · exact hnil [] (by simp)
    · exact hnil [] (by simp)
  | deliver id b =>
    simp only [Node.step]
    split
    · have ht := (Grows.flush (cfg := cfg) (s.pending.length + 1) s.store
        ((id, b) :: s.pending)).topRound (flush_base _ _ _)
      refine hset _ _ (hR.mono rfl rfl le_rfl ht)
        (ho.grow (Grows.flush _ _ _) (flush_base _ _ _) rfl rfl) hs ht ?_ (Or.inl (le_max_left _ _))
      intro k h hk
      simp only [List.mem_append] at hk
      rcases hk with (hk | hk) | hk
      · obtain ⟨_, _, he⟩ := evidence_relay hk; cases he
      · split at hk <;> simp at hk
      · split at hk <;> simp at hk
    · split
      · rename_i h; exact absurd h.2.2.1 (by simp [hs])
      · exact hnil [] (by simp)
  | timer r =>
    rw [step_timer_eq]
    refine hset _ _ (hR.mono rfl rfl le_rfl le_rfl) (ho.grow (Grows.refl _) rfl rfl rfl)
      (timerState_idle hs (hst r rfl)) le_rfl ?_ hself
    intro k h hk; unfold timerOut at hk; split at hk <;> split at hk <;> simp at hk
  | restart => exact absurd rfl hr
  | baseOffer p G =>
    simp only [Node.step, hs, Bool.false_eq_true, false_and, if_false]
    exact hnil [] (by simp)
  | baseRequest p =>
    refine hnil _ fun k h hk => ?_
    simp only [Node.step, List.mem_cons, List.mem_append, List.mem_map] at hk
    rcases hk with ((hk | ⟨c, -, hk⟩) | ⟨e, -, hk⟩) | hk
    · cases hk
    · cases hk
    · cases hk
    · rw [if_neg (by simp [hs])] at hk; cases hk
  | fetchRequest p G ids =>
    refine hnil _ fun k h hk => ?_
    simp only [Node.step, answer, List.mem_map] at hk
    obtain ⟨j, -, hk⟩ := hk; cases hk
  | decisionRequest p lo =>
    refine hnil _ fun k h hk => ?_
    simp only [Node.step] at hk
    split at hk
    · unfold serveFrom at hk
      split at hk
      · split at hk <;> simp at hk
      · simp at hk
    · simp at hk
  | certOffer p c ds =>
    rcases certOffer_cases (cfg := cfg) s p c ds with ⟨ds', -, -, ha, he⟩ |
      ⟨-, hcf, he⟩ | he
    · rw [he, adopt_eq]
      have ha' := ha
      unfold adoptable at ha'
      simp only [Bool.and_eq_true, decide_eq_true_eq] at ha'
      have hcx : c.height ≤ (adopted s c ds').certHeight := by
        unfold adopted State.certHeight; dsimp only
        split
        · simp
        · rename_i h; simpa [State.certHeight] using not_lt.mp h
      refine hset _ _ ⟨hR.1, ?_⟩ (ho.grow (Grows.refl _) rfl rfl rfl) hs le_rfl (by simp) ?_
      · change c.height ≤ _; exact hcx.trans (le_max_left _ _)
      · by_cases hlt : s.certHeight < c.height
        · refine Or.inr ⟨p, c, ds, rfl, ha'.1.1.1.1, ha'.1.1.1.2, ?_⟩
          have : (adopted s c ds').certHeight = c.height := by
            change ((if s.certHeight < c.height then some c else s.cert).map Cert.height).getD 0 = _
            rw [if_pos hlt]; rfl
          rw [this]; exact le_max_left _ _
        · refine Or.inl ?_
          have : (adopted s c ds').certHeight = s.certHeight := by
            change ((if s.certHeight < c.height then some c else s.cert).map Cert.height).getD 0 = _
            rw [if_neg hlt]; rfl
          rw [this]; exact le_max_left _ _
    · rw [he]
      unfold confirms at hcf
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hcf
      obtain ⟨⟨⟨⟨⟨-, -⟩, hlt⟩, hle⟩, -⟩, -⟩ := hcf
      have hcD : c.height ≤ decidable cfg s.store.topRound := by
        have := hR.2; rw [max_def] at this; split at this <;> omega
      unfold Node.confirm
      refine hset _ [] ⟨hR.1, hR.2.trans (max_le_max hlt.le le_rfl)⟩
        (ho.grow (Grows.refl _) rfl rfl rfl) hs le_rfl (by simp) (Or.inl ?_)
      exact hcD.trans (le_max_right _ _)
    · rw [he]; exact hnil [] (by simp)
  | announced p c =>
    rcases announced_cases (cfg := cfg) s p c with ⟨-, hcf, he⟩ | he | he <;> rw [he]
    · unfold confirms at hcf
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hcf
      obtain ⟨⟨⟨⟨⟨-, -⟩, hlt⟩, hle⟩, -⟩, -⟩ := hcf
      have hcD : c.height ≤ decidable cfg s.store.topRound := by
        have := hR.2; rw [max_def] at this; split at this <;> omega
      unfold Node.confirm
      refine hset _ [] ⟨hR.1, hR.2.trans (max_le_max hlt.le le_rfl)⟩
        (ho.grow (Grows.refl _) rfl rfl rfl) hs le_rfl (by simp) (Or.inl ?_)
      exact hcD.trans (le_max_right _ _)
    · exact hnil _ (by simp)
    · exact hnil [] (by simp)
  | proposal p k kh =>
    rw [step_proposal]
    split
    · have hc := certifyAt_cert_le (cfg := cfg) { s with props := (p, k, kh) :: (s.props.filter
        fun x => x.1 ≠ p ∨ x.2.1 ≠ k ∧ (k ≤ s.lo + cfg.ahead ∨ x.2.1 ≤ s.lo + cfg.ahead)) } k kh
      refine hset _ _ ⟨hR.1, hR.2.trans (max_le_max (record_certHeight s p k kh) le_rfl)⟩
        (ho.grow (Grows.refl _) rfl rfl rfl) hs le_rfl (by simp) (Or.inl ?_)
      rcases hc with hc | hc
      · exact (le_of_eq hc).trans (le_max_left _ _)
      · exact hc.trans (hR.1.trans (le_max_right _ _))
    · exact hnil [] (by simp)

/-! ## Along a trace -/

section Trace

variable {tr : Trace Validator BlockId Payload} {H : Finset Validator}

/-- **A steady node's store reaches** what it proposed and decided past its
certificate, before every event. -/
theorem reached_before {v : Validator} (hnv : Steady cfg tr v) (i : ℕ) :
    Reached (cfg.at v) (stateBefore cfg tr i v) ∧ OwnTop (cfg.at v) (stateBefore cfg tr i v) :=
  inv_before (cfg := cfg) hnv (fun s => Reached (cfg.at v) s ∧ OwnTop (cfg.at v) s)
    ⟨Reached.init, fun _ h => by simp [stateBefore, inputsBefore, run, State.init] at h⟩
    (fun _ _ h hs hr hst => ⟨(step_reached h.1 h.2 hs hr hst).1, h.2.step hs hr hst⟩) i

omit [Fintype Validator] in
/-- A slot below the slots at rounds at most `R` lies at a round at most `R`. -/
theorem slotRound_pred_le {k R : ℕ} (hk : 0 < k) (h : k ≤ decidable cfg R) :
    cfg.slots.slotRound (k - 1) ≤ R :=
  slotRound_le_of_decidable (cfg := cfg) (by omega)

/-- **A steady node's proposal lies within its store's reach**: the round
of the slot below a height it proposed lies at or below its store's top
round after the event. -/
theorem propose_reached {w : Validator} (hnw : Steady cfg tr w) {e : ℕ}
    {inp : Input Validator BlockId Payload} (he : tr[e]? = some (w, inp)) {k : ℕ} {h : BlockId}
    (hk : 0 < k) (hp : Output.propose k h ∈ outputsAt cfg tr e) :
    cfg.slots.slotRound (k - 1) ≤ (stateBefore cfg tr (e + 1) w).store.topRound := by
  rw [outputsAt_eq he] at hp
  obtain ⟨hR, hO⟩ := reached_before (cfg := cfg) hnw e
  have hs := (fired_before (cfg := cfg) hnw e).1
  have := (step_reached hR hO hs (hnw e _ he).1 (hnw e _ he).2).2.2.1 k h hp
  rw [stateBefore_succ he, if_pos rfl]
  exact slotRound_pred_le (cfg := cfg.at w) hk this

/-- **Where a steady node's certificate comes from**: its height lies within
the slots at its store's rounds, or within the height of a certificate of
`q` distinct signers it was offered earlier. -/
theorem cert_backed {v : Validator} (hnv : Steady cfg tr v) :
    ∀ i, ∃ H₀, (stateBefore cfg tr i v).certHeight ≤
        max H₀ (decidable cfg (stateBefore cfg tr i v).store.topRound) ∧
      (H₀ = 0 ∨ ∃ j < i, ∃ p c ds, tr[j]? = some (v, .certOffer p c ds) ∧
        cfg.q ≤ c.signers.length ∧ c.signers.Nodup ∧ H₀ ≤ c.height)
  | 0 => ⟨0, by simp [stateBefore, inputsBefore, run, State.init, State.certHeight], Or.inl rfl⟩
  | i + 1 => by
    obtain ⟨H₀, hH, hj⟩ := cert_backed hnv i
    have hlift : ∀ {j : ℕ}, j < i → j < i + 1 := fun h => by omega
    have hj' : H₀ = 0 ∨ ∃ j < i + 1, ∃ p c ds, tr[j]? = some (v, .certOffer p c ds) ∧
        cfg.q ≤ c.signers.length ∧ c.signers.Nodup ∧ H₀ ≤ c.height :=
      hj.imp_right fun ⟨j, hji, rest⟩ => ⟨j, hlift hji, rest⟩
    rcases before_succ_cases (cfg := cfg) (tr := tr) v i with heq | ⟨inp, he, heq⟩
    · rw [heq]; exact ⟨H₀, hH, hj'⟩
    · obtain ⟨hR, hO⟩ := reached_before (cfg := cfg) hnv i
      have hs := (fired_before (cfg := cfg) hnv i).1
      obtain ⟨-, ht, -, hc⟩ := step_reached hR hO hs (hnv i _ he).1 (hnv i _ he).2
      rw [heq]
      have hd := decidable_mono (cfg := cfg) ht
      rcases hc with hc | ⟨p, c, ds, rfl, hq, hnd, hc⟩
      · exact ⟨H₀, hc.trans (max_le (hH.trans (max_le_max le_rfl hd)) (le_max_right _ _)), hj'⟩
      · exact ⟨c.height, hc, Or.inr ⟨i, by omega, p, c, ds, he, hq, hnd, le_rfl⟩⟩

omit [Fintype Validator] in
/-- Slot rounds rise with slots. -/
theorem slotRound_mono {k k' : ℕ} (h : k ≤ k') :
    cfg.slots.slotRound k ≤ cfg.slots.slotRound k' :=
  Nat.mul_le_mul_left _ (Nat.div_le_div_right h)

/-- **A reliable node's frontier is reached by a reliable store**: the round
of the last slot a reliable node has decided and its certificate certifies
lies at or below the top round of a reliable node's store, at or before
the event, if a quorum holds a reliable node. -/
theorem stall_witness {T : Finset Validator} (hTH : T ⊆ H)
    (hcert : Boot.TimelyCerts cfg H tr) (hnr : ∀ v ∈ T, Steady cfg tr v)
    (hqT : Fintype.card Validator < cfg.q + T.card) {v : Validator} (hv : v ∈ T) (i : ℕ)
    (hk : 0 < min (stateBefore cfg tr i v).lo (stateBefore cfg tr i v).certHeight) :
    ∃ w ∈ T, ∃ e ≤ i, cfg.slots.slotRound (min (stateBefore cfg tr i v).lo
      (stateBefore cfg tr i v).certHeight - 1) ≤ (stateBefore cfg tr e w).store.topRound := by
  set k := min (stateBefore cfg tr i v).lo (stateBefore cfg tr i v).certHeight
  have hkc : k ≤ (stateBefore cfg tr i v).certHeight := min_le_right _ _
  obtain ⟨H₀, hH, hj⟩ := cert_backed (cfg := cfg) (hnr v hv) i
  by_cases hD : k ≤ decidable cfg (stateBefore cfg tr i v).store.topRound
  · exact ⟨v, hv, i, le_rfl, slotRound_pred_le (cfg := cfg) hk hD⟩
  · have hkH : k ≤ H₀ := by
      have := hkc.trans hH; rw [max_def] at this; split at this <;> omega
    rcases hj with h0 | ⟨j, hji, p, c, ds, hj, hq, hnd, hHc⟩
    · omega
    -- a reliable signer
    have hsig : ∃ w ∈ c.signers, w ∈ T := by
      by_contra hno
      have hsub : c.signers.toFinset ⊆ Tᶜ := fun w hw =>
        Finset.mem_compl.mpr fun hwT => hno ⟨w, List.mem_toFinset.mp hw, hwT⟩
      have h₁ := Finset.card_le_card hsub
      rw [Finset.card_compl, List.toFinset_card_of_nodup hnd] at h₁
      have := Finset.card_le_univ T
      omega
    obtain ⟨w, hwc, hwT⟩ := hsig
    obtain ⟨e, hej, hew, hep⟩ := hcert j v p c ds hj (hTH hv) w hwc (hTH hwT)
    obtain ⟨inp, he⟩ := Converge.event_of_map hew
    have hck : 0 < c.height := by omega
    refine ⟨w, hwT, e + 1, by omega, ?_⟩
    exact (slotRound_mono (cfg := cfg) (by omega)).trans
      (propose_reached (cfg := cfg) (hnr w hwT) he hck hep)

omit [Fintype Validator] [DecidableEq Validator] in
/-- A stored block is read at its raw round. -/
theorem blk_round (st : Store Validator BlockId Payload) (j : BlockId) :
    (st.blk j).round = (st.map.getD j st.junk).round := by
  simp [Store.blk, lookup, atBase_round]

omit [Fintype Validator] in
/-- **A store holds every round from its horizon to a block's**, if its
blocks above the horizon are valid at a positive quorum. -/
theorem exists_at_round {q : ℕ} (hq : 0 < q) {st : Store Validator BlockId Payload}
    (hv : StoreValid q st) :
    ∀ (d : ℕ) {j : BlockId}, j ∈ st.ids → ∀ (R : ℕ), st.base ≤ R → (st.blk j).round = R + d →
      ∃ i ∈ st.ids, (st.blk i).round = R
  | 0, j, hj, R, _, hjR => ⟨j, hj, hjR⟩
  | d + 1, j, hj, R, hb, hjR => by
    have hlt : st.base < (st.map.getD j st.junk).round := by rw [← blk_round]; omega
    have hrv := hv j hj hlt
    rw [← Store.blk_of_lt hlt] at hrv
    have hcard := hrv.quorum (by omega)
    obtain ⟨a, ha⟩ := Finset.card_pos.mp (lt_of_lt_of_le hq hcard)
    obtain ⟨i, hi, -⟩ := Finset.mem_image.mp ha
    have hii : i ∈ st.ids := st.complete j hj i hi
    have hir : (st.blk i).round + 1 = (st.blk j).round := st.pred j hj i hi
    exact exists_at_round hq hv d hii R hb (by omega)

/-- **A block stored by an honest node, of an honest author, was built
before**: at an earlier event of its author. -/
theorem built_before (htime : Converge.TimelyAuthentic cfg H tr) {w : Validator} (hw : w ∈ H)
    {e : ℕ} {j : BlockId} (hj : j ∈ (stateBefore cfg tr e w).store.ids)
    (hu : ((stateBefore cfg tr e w).store.map.getD j
      (stateBefore cfg tr e w).store.junk).creator ∈ H) :
    ∃ b < e, ∃ inp, tr[b]? = some (((stateBefore cfg tr e w).store.map.getD j
        (stateBefore cfg tr e w).store.junk).creator, inp) ∧
      (j, (stateBefore cfg tr e w).store.map.getD j (stateBefore cfg tr e w).store.junk) ∈
        persists (outputsAt cfg tr b) := by
  set x := (j, (stateBefore cfg tr e w).store.map.getD j (stateBefore cfg tr e w).store.junk)
  have hinv := Converge.inv_before (cfg := cfg) (tr := tr) e w
  have hk := hinv.known j hj
  simp only [Converge.knownBefore, Set.mem_setOf_eq, List.mem_append] at hk
  rcases hk with hd | hp
  · obtain ⟨d, hde, inp, hd', hdel⟩ := mem_delivered_before (cfg.at w) w e hd
    obtain ⟨p, hpd, hpv, hpb⟩ := htime d w inp hd' hw x hdel hu
    obtain ⟨inpp, hp'⟩ := Converge.event_of_map hpv
    exact ⟨p, by omega, inpp, hp', Converge.persists_of_broadcasts hpb⟩
  · have hc : x.2.creator = w := (hinv.good x hp).2.1
    obtain ⟨b, hbe, hbw, hxb⟩ := mem_persists_before (cfg := cfg) (tr := tr) w e hp
    obtain ⟨inpb, hb⟩ := Converge.event_of_map hbw
    refine ⟨b, hbe, inpb, ?_, hxb⟩
    rw [hb]; change some (w, inpb) = some (x.2.creator, inpb); rw [hc]

/-- **A reliable store above a round holds a reliable block a round
higher**: if a steady node's store reaches round `r + 2` at event `e`, a
reliable node built a block of round `r + 1` before, if a quorum holds a
reliable node. -/
theorem reliable_builder {T : Finset Validator} (hTH : T ⊆ H) (hq : 0 < cfg.q)
    (htime : Converge.TimelyAuthentic cfg H tr) (hnr : ∀ v ∈ T, Steady cfg tr v)
    (hqT : Fintype.card Validator < cfg.q + T.card) {w : Validator} (hw : w ∈ T) {e r : ℕ}
    (hR : r + 2 ≤ (stateBefore cfg tr e w).store.topRound) :
    ∃ u ∈ T, ∃ b < e, ∃ inp, tr[b]? = some (u, inp) ∧
      ∃ x ∈ persists (outputsAt cfg tr b), x.2.round = r + 1 := by
  have hnw := hnr w hw
  set st := (stateBefore cfg tr e w).store
  by_cases hA : (stateBefore cfg tr e w).top.isSome ∧
      r + 1 ≤ (stateBefore cfg tr e w).top.getD 0
  · obtain ⟨b, hbe, hbw, x, hx, hxr⟩ := built_by hnw e hA.1 hA.2
    obtain ⟨inp, hb⟩ := Converge.event_of_map hbw
    exact ⟨w, hw, b, hbe, inp, hb, x, hx, hxr⟩
  -- the horizon lies at or below `r`
  have hbase : st.base ≤ r := by
    rcases ht : (stateBefore cfg tr e w).top with _ | t
    · have := (Held.run (cfg := cfg.at w) (inputsBefore tr e w) Held.init).low ht
      change st.base = 0 at this; omega
    · have h₁ := base_le_top_sub hnw e ht
      have h₂ : t ≤ r := by
        rw [ht] at hA; simp at hA; omega
      change st.base ≤ t - cfg.lag at h₁; omega
  have hv : StoreValid cfg.q st := (Converge.inv_before (cfg := cfg) (tr := tr) e w).valid
  -- a stored block at the top round, then one at round `r + 2`
  have hne : st.ids.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    have : st.topRound = 0 := by unfold Store.topRound; rw [h]; rfl
    omega
  obtain ⟨j, hj, hjmax⟩ := Finset.exists_max_image st.ids (fun i => (st.blk i).round) hne
  have hjtop : (st.blk j).round = st.topRound :=
    le_antisymm (le_topRound hj) (Finset.sup_le fun i hi => hjmax i hi)
  obtain ⟨y, hy, hyr⟩ := exists_at_round hq hv (st.topRound - (r + 2)) hj
    (r + 2) (by omega) (by omega)
  -- its references hold `q` distinct authors of round `r + 1`, one reliable
  have hylt : st.base < (st.map.getD y st.junk).round := by rw [← blk_round]; omega
  have hrv := hv y hy hylt
  rw [← Store.blk_of_lt hylt] at hrv
  have hcard := hrv.quorum (by omega)
  have hrel : ∃ i ∈ (st.blk y).refs, (st.blk i).creator ∈ T := by
    by_contra hno
    have hsub : creators st.blk (st.blk y) ⊆ Tᶜ := by
      intro a ha
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
      exact Finset.mem_compl.mpr fun hT => hno ⟨i, hi, hT⟩
    have h₁ := Finset.card_le_card hsub
    rw [Finset.card_compl] at h₁
    have := Finset.card_le_univ T
    omega
  obtain ⟨i, hi, hiT⟩ := hrel
  have hii : i ∈ st.ids := st.complete y hy i hi
  have hir : (st.blk i).round + 1 = (st.blk y).round := st.pred y hy i hi
  have hilt : st.base < (st.map.getD i st.junk).round := by rw [← blk_round]; omega
  have hraw := Store.blk_of_lt hilt
  rw [hraw] at hiT hir
  obtain ⟨b, hbe, inp, hb, hxb⟩ := built_before htime (hTH hw) hii (hTH hiT)
  exact ⟨_, hiT, b, hbe, inp, hb, _, hxb, by change (st.map.getD i st.junk).round = r + 1; omega⟩

end Trace

/-! ## No stall past GST -/

section Stall

variable {H T : Finset Validator} {tr : Trace Validator BlockId Payload} {time : ℕ → ℕ}
  {gst Δ Δₛ t₁ : ℕ}

/-- **A timer that finds a reliable node stalled is followed by its
build**: past GST, a reliable node stalled at round `r` when `r`'s timer
fires at `j` is above `r` by `max (time j) gst + 3Δ + Δₛ`, if a quorum
holds a reliable node and `Λ` is positive. The certificate behind its
frontier rests on a reliable store above `r + 1`, so a reliable node
built a block of round `r + 1` (`stall_witness`, `reliable_builder`); the
block arrives by then with `q` authors of round `r` it lends, and the
round's timer has fired. -/
theorem stall_builds (hq : 2 ≤ cfg.q) (hl : cfg.limit = none) (hσ : cfg.σ = boundedSel)
    (hadm : cfg.Admissible) (hf : Hᶜ.card ≤ cfg.f) (hid : Function.Injective cfg.idOf)
    (htime : Converge.TimelyAuthentic cfg H tr)
    (hcert : Boot.TimelyCerts cfg H tr) (hinj : Converge.HashInjective cfg H tr)
    (hchain : Boot.ChainInjective cfg H tr) (hTH : T ⊆ H) (hnr : ∀ v ∈ T, Steady cfg tr v)
    (hqT : Fintype.card Validator < cfg.q + T.card) (hlag : 1 ≤ cfg.lag)
    (hmono : Live.TimeMono tr time) (hdel : Live.DeliveredWithin cfg T tr time gst Δ t₁)
    (hsync : Live.SyncedWithin cfg H T tr time gst Δₛ t₁) {v : Validator} (hv : v ∈ T)
    {j r : ℕ} (hj : tr[j]? = some (v, .timer r))
    (hst : stalledAt (cfg.at v) (stateBefore cfg tr j v) r = true) {τ : ℕ}
    (hτ : max (time j) gst + 3 * Δ + Δₛ ≤ τ) (ht₁ : τ ≤ t₁) :
    r + 1 ≤ topAt cfg tr time v τ := by
  have hnv := hnr v hv
  have hcmp : ∀ u ∈ T, ∀ w ∈ T, ∀ i k, (stateBefore cfg tr i u).decided.reverse <+:
      (stateBefore cfg tr k w).decided.reverse ∨
        (stateBefore cfg tr k w).decided.reverse <+: (stateBefore cfg tr i u).decided.reverse :=
    fun u hu w hw i k => decided_comparable hσ hadm hf htime hcert hinj hchain
      (hTH hu) (hTH hw) i k
  have hjl : j < tr.length := (List.getElem?_eq_some_iff.mp hj).1
  set E := eventsBy tr time τ with hE
  have hjE : j < E := (lt_eventsBy hmono hjl).mpr (by omega)
  -- the stall: the round of the frontier's last slot lies more than `Λ` above `r`
  unfold stalledAt at hst
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hst
  obtain ⟨-, htj, hk, hkr⟩ := hst
  change r + cfg.lag < cfg.slots.slotRound _ at hkr
  by_contra hlt
  have hle : topAt cfg tr time v τ ≤ r := by omega
  -- `v` is at round `r` at `τ`
  have hZt : (stateBefore cfg tr E v).top = some r := by
    obtain ⟨h₂, h₃, -, -⟩ := rises_before (cfg := cfg) hnv hjE.le
    rw [htj] at h₂ h₃
    obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp (h₃ rfl)
    rw [ht] at h₂ ⊢
    change ((stateBefore cfg tr E v).top).getD 0 ≤ r at hle
    rw [ht] at hle
    simp only [Option.getD_some] at h₂ hle
    rw [show t = r by omega]
  -- a reliable block of round `r + 1`, built before `j`
  obtain ⟨w, hw, e, hej, hwe⟩ := stall_witness hTH hcert hnr hqT hv j hk
  have hr2 : r + 2 ≤ (stateBefore cfg tr e w).store.topRound := by
    have := lt_of_lt_of_le hkr hwe; omega
  obtain ⟨u, hu, b, hbe, inp, hb, x, hx, hxr⟩ :=
    reliable_builder hTH (by omega) htime hnr hqT hw hr2
  have hbl : b < tr.length := (List.getElem?_eq_some_iff.mp hb).1
  have htb : time b ≤ time j := hmono b j (by omega) hjl
  by_cases huv : u = v
  · subst huv
    obtain ⟨t, ht, hxt⟩ := built_le_top hb hx
    have h₁ := (rises_before (cfg := cfg) hnv (show b + 1 ≤ j by omega)).1
    rw [ht, htj] at h₁
    simp only [Option.getD_some] at h₁
    omega
  -- it arrives, with its references
  have hbn : (stateBefore cfg tr E v).store.base ≤ r := by
    have := base_le_top_sub hnv E hZt; omega
  obtain ⟨hxi, hxround, hxc, -⟩ := block_arrives hl hq hσ hadm hf htime hcert hinj hchain hTH hnr
    hmono hdel hsync hcmp hu hv huv hb hx htb hτ ht₁ (t := r) hZt (by omega)
    (by rw [hxr]; exact hbn.trans (Nat.le_succ r))
  set st := (stateBefore cfg tr E v).store
  set X := (stateBefore cfg tr E v).exposed
  have hxi' : x.1 ∈ st.ids := hxi
  have hxr' : (st.blk x.1).round = r + 1 := by rw [← hxr]; exact hxround
  have hxc' : (st.blk x.1).creator = u := hxc
  have hv' : StoreValid cfg.q st := (Converge.inv_before (cfg := cfg) (tr := tr) E v).valid
  have hxlt : st.base < (st.map.getD x.1 st.junk).round := by
    rw [← blk_round]; omega
  have hrv := hv' x.1 hxi' hxlt
  rw [← Store.blk_of_lt hxlt] at hrv
  have hcard := hrv.quorum (by omega)
  have huX : u ∉ X := honest_not_exposed hinj htime (hTH hv) E (hTH hu)
  have hsub : creators st.blk (st.blk x.1) ⊆ usableAuthors st X r := by
    intro a ha
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
    have hii : i ∈ st.ids := st.complete x.1 hxi' i hi
    have hir : (st.blk i).round + 1 = (st.blk x.1).round := st.pred x.1 hxi' i hi
    refine mem_usableAuthors.mpr ⟨i, hii, by omega, ?_, rfl⟩
    unfold usable
    refine Bool.or_eq_true_iff.mpr (Or.inr (decide_eq_true ⟨x.1, Finset.mem_filter.mpr
      ⟨mem_blocksAt.mpr ⟨hxi', ?_⟩, ?_, hi⟩⟩))
    · change (st.blk x.1).round = (st.blk i).round + 1; omega
    · rw [hxc']; exact huX
  -- the round's timer has fired, so `v` builds, against its being settled
  have hfired : r ∈ (stateBefore cfg tr E v).fired :=
    fired_stays hnv hj E hjE (by rw [hZt]; simp)
  obtain ⟨j₀, hj₀, hj₀i, hj₀r, hj₀c⟩ := ownTop_before (cfg := cfg) hnv E r hZt
  have hsome := tryBuild_isSome (cfg := cfg.at v) hZt (Or.inl hfired)
    (hcard.trans (Finset.card_le_card hsub))
    (fun j hj => by rw [hj₀] at hj; cases hj; exact ⟨hj₀i, hj₀r, hj₀c⟩) hbn
    (fun R => fresh_before hid htime (hTH hv) hZt R)
  rcases settled_before (cfg := cfg) hq hnv E with h | h
  · rw [hZt] at h; cases h
  · rw [h.build] at hsome; cases hsome

end Stall

end Node

end LeanDag
