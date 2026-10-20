import LeanDag.Node.Helpers.Certify
/-!
# The proposals a node keeps

Over any run a node keeps its proposals sparse (`Sparse`): one per
signer and height, each above its certificate's height, and of each
signer at most one above `lo + ahead`. A signer's kept proposals then
number at most `lo + ahead − certHeight + 1` (`Sparse.signer_le`), and
all of them `n` times that (`Sparse.length_le`).
-/

namespace LeanDag

namespace Node

variable {Validator BlockId Payload : Type} [Fintype Validator] [DecidableEq Validator]
variable [LinearOrder BlockId]
variable {cfg : Config Validator BlockId Payload}

variable (cfg) in
/-- **Sparse proposals**: one per signer and height, each above the
certificate's height, and of each signer at most one above `lo + ahead`. -/
structure Sparse (s : State Validator BlockId Payload) : Prop where
  nodup : (s.props.map fun x => (x.1, x.2.1)).Nodup
  over : ∀ x ∈ s.props, s.certHeight < x.2.1
  latest : ∀ x ∈ s.props, ∀ y ∈ s.props, x.1 = y.1 → s.lo + cfg.ahead < x.2.1 →
    s.lo + cfg.ahead < y.2.1 → x.2.1 = y.2.1

/-! ## Keeping it -/

omit [Fintype Validator] in
/-- **Keeping fewer proposals**, each above the certificate's height, with
the decided frontier no lower, keeps them sparse. -/
theorem Sparse.mono {s s' : State Validator BlockId Payload} (h : Sparse cfg s)
    (hp : s'.props.Sublist s.props) (hc : ∀ x ∈ s'.props, s'.certHeight < x.2.1)
    (hlo : s.lo ≤ s'.lo) : Sparse cfg s' where
  nodup := h.nodup.sublist (hp.map _)
  over := hc
  latest := fun x hx y hy hxy h₁ h₂ =>
    h.latest x (hp.subset hx) y (hp.subset hy) hxy (by omega) (by omega)

omit [Fintype Validator] in
theorem Sparse.frame {s s' : State Validator BlockId Payload} (h : Sparse cfg s)
    (hp : s'.props = s.props) (hc : s'.cert = s.cert) (hlo : s.lo ≤ s'.lo) : Sparse cfg s' :=
  h.mono (hp ▸ List.Sublist.refl _)
    (fun x hx => by
      have : s'.certHeight = s.certHeight := by simp [State.certHeight, hc]
      rw [this]; exact h.over x (hp ▸ hx)) hlo

omit [Fintype Validator] in
/-- Dropping the proposals at or below the certificate held keeps them
sparse. -/
theorem Sparse.above {s s' : State Validator BlockId Payload} (h : Sparse cfg s)
    (hp : s'.props = above s'.cert s.props) (hlo : s.lo ≤ s'.lo) : Sparse cfg s' :=
  h.mono (hp ▸ List.filter_sublist) (fun _ hx => (mem_above.mp (hp ▸ hx)).2) hlo

omit [Fintype Validator] in
/-- **Recording a proposal keeps them sparse.** -/
theorem Sparse.record {s : State Validator BlockId Payload} (h : Sparse cfg s) (v : Validator)
    (k : ℕ) (hd : BlockId) : Sparse cfg (Node.record cfg s v k hd) := by
  set w := s.lo + cfg.ahead
  set ps := (v, k, hd) :: s.props.filter fun x => x.1 ≠ v ∨ x.2.1 ≠ k ∧ (k ≤ w ∨ x.2.1 ≤ w)
  have hsub : (Node.record cfg s v k hd).props.Sublist ps := List.filter_sublist
  refine ⟨?_, fun x hx => (mem_record.mp hx).2, fun x hx y hy hxy h₁ h₂ => ?_⟩
  · refine List.Nodup.sublist (hsub.map _) (List.nodup_cons.mpr ⟨fun hm => ?_, ?_⟩)
    · obtain ⟨x, hx, he⟩ := List.mem_map.mp hm
      have hf := of_decide_eq_true (List.mem_filter.mp hx).2
      simp only [Prod.mk.injEq] at he
      rcases hf with hf | hf
      · exact hf he.1
      · exact hf.1 he.2
    · exact h.nodup.sublist (List.filter_sublist.map _)
  · have hlo : (Node.record cfg s v k hd).lo = s.lo := rfl
    rw [hlo] at h₁ h₂
    rcases (mem_record.mp hx).1 with rfl | ⟨hx, hfx⟩ <;>
      rcases (mem_record.mp hy).1 with rfl | ⟨hy, hfy⟩
    · rfl
    · exfalso
      dsimp only at h₁ hxy
      rcases hfy with hfy | ⟨-, hfy⟩
      · exact hfy hxy.symm
      · omega
    · exfalso
      dsimp only at h₂ hxy
      rcases hfx with hfx | ⟨-, hfx⟩
      · exact hfx hxy
      · omega
    · exact h.latest x hx y hy hxy h₁ h₂

omit [Fintype Validator] in
theorem Sparse.proposeFrom : ∀ (fuel : ℕ) {s : State Validator BlockId Payload},
    Sparse cfg s → Sparse cfg (Node.proposeFrom cfg fuel s).1
  | 0, _, h => h
  | fuel + 1, s, h => by
    rw [proposeFrom_succ]
    split
    · rename_i s₁ o hn
      obtain ⟨-, rfl, -⟩ := proposeNext_some hn
      exact Sparse.proposeFrom fuel ((h.record _ _ _).frame rfl rfl le_rfl)
    · exact h

omit [Fintype Validator] in
theorem Sparse.decideStep {s : State Validator BlockId Payload} (h : Sparse cfg s) :
    Sparse cfg (Node.decideStep cfg s).1 := by
  unfold Node.decideStep
  dsimp only
  split
  · exact Sparse.proposeFrom _ (h.frame rfl rfl (Nat.le_add_right _ _))
  · exact Sparse.proposeFrom _ h

omit [Fintype Validator] in
theorem Sparse.advance {s : State Validator BlockId Payload} (h : Sparse cfg s) :
    Sparse cfg (Node.advance cfg s).1 := by
  simp only [Node.advance]
  obtain ⟨a₁, b₁, c₁, -⟩ := progress_frame (cfg := cfg) (s.store.topRound + 2) s
  have h₂ := (h.frame a₁ b₁ c₁.ge).decideStep
  obtain ⟨a₃, b₃, c₃, -⟩ := collect_frame (cfg := cfg)
    (Node.decideStep cfg (progress cfg (s.store.topRound + 2) s).1).1
  exact (h₂.frame a₃ b₃ c₃.ge).frame rfl rfl le_rfl

omit [Fintype Validator] in
theorem Sparse.settle {s : State Validator BlockId Payload} (h : Sparse cfg s) :
    Sparse cfg (Node.settle cfg s).1 := by
  rcases settle_cases (cfg := cfg) s with he | ⟨s₁, hr, he⟩ <;> rw [he]
  · exact h.advance
  · refine Sparse.advance (h.frame ?_ ?_ ?_) <;>
    · unfold Node.tryResume at hr
      split at hr
      · dsimp only at hr
        split at hr
        · split at hr
          · rw [Option.some.injEq] at hr; subst hr; rfl
          · cases hr
        · cases hr
      · cases hr

omit [Fintype Validator] in
theorem Sparse.bootFrom {s : State Validator BlockId Payload} (h : Sparse cfg s) :
    Sparse cfg (Node.bootFrom cfg s).1 := by
  rcases bootFrom_cases (cfg := cfg) s with he | ⟨s₂, ads, hbt, he⟩ <;> rw [he]
  · exact h
  · obtain ⟨t, G, c, ds, -, -, -, -, -, -, -, -, -, hlo, -, -, -, -, -, -, -, hp, -⟩ :=
      tryBoot_some hbt
    exact (h.above hp (by rw [hlo]; exact le_max_left _ _)).advance

/-! ## A step, and a run -/

/-- **Every step keeps the proposals sparse.** -/
theorem Sparse.step {s : State Validator BlockId Payload} (h : Sparse cfg s)
    (i : Input Validator BlockId Payload) : Sparse cfg (Node.step cfg s i).1 := by
  cases i with
  | start =>
    simp only [Node.step]
    split
    · split
      · exact Sparse.settle (h.frame rfl rfl le_rfl)
      · exact h
    · exact h
  | deliver id b =>
    simp only [Node.step]
    split
    · exact Sparse.settle (h.frame rfl rfl le_rfl)
    · exact h
  | timer r => exact Sparse.settle (h.frame rfl rfl le_rfl)
  | fetchRequest peer G ids => exact h
  | restart =>
    exact Sparse.settle (h.mono (List.nil_sublist _) (fun _ hx => by simp [State.recover] at hx)
      le_rfl)
  | baseRequest => exact h
  | baseOffer p G bs =>
    rw [step_offer]
    split
    · exact Sparse.bootFrom (h.frame rfl rfl le_rfl)
    · exact h
  | certOffer p c ds =>
    rw [step_certOffer]
    split
    · exact Sparse.bootFrom (h.frame rfl rfl le_rfl)
    · split
      · rename_i ha
        rw [adopt_eq]
        exact (h.above (s' := adopted s c ds) rfl (adoptable_lo ha.2).le).settle
      · exact h
  | proposal p k kh =>
    rw [step_proposal]
    split
    · obtain ⟨n, hn⟩ := seek_eq (cfg := cfg) (Node.record cfg s p k kh) k kh
      rw [hn]
      exact (h.record p k kh).frame rfl rfl le_rfl
    · exact h
  | decisionRequest => exact h

/-- **A run keeps the proposals sparse.** -/
theorem Sparse.run : ∀ (is : List (Input Validator BlockId Payload))
    {s : State Validator BlockId Payload}, Sparse cfg s → Sparse cfg (Node.run cfg s is).1
  | [], _, h => h
  | i :: is, _, h => Sparse.run is (h.step i)

omit [Fintype Validator] in
theorem Sparse.init : Sparse cfg (State.init cfg) :=
  ⟨List.nodup_nil, fun _ hx => absurd hx List.not_mem_nil,
    fun _ hx => absurd hx List.not_mem_nil⟩

/-! ## The bound -/

omit [Fintype Validator] in
/-- **A signer's kept proposals** number at most
`lo + ahead − certHeight + 1`. -/
theorem Sparse.signer_le {s : State Validator BlockId Payload} (h : Sparse cfg s)
    (v : Validator) :
    (s.props.filter fun x => x.1 = v).length ≤ s.lo + cfg.ahead - s.certHeight + 1 := by
  set w := s.lo + cfg.ahead
  set L := s.props.filter fun x => x.1 = v
  have hL : ∀ x ∈ L, x ∈ s.props ∧ x.1 = v := fun x hx => by
    simpa using List.mem_filter.mp hx
  -- the heights of the signer's proposals are distinct
  set H := L.map fun x => x.2.1
  have hH : H.Nodup := by
    have hm : L.map (fun x => (x.1, x.2.1)) = H.map (Prod.mk v) := by
      rw [List.map_map]
      exact List.map_congr_left fun x hx => by rw [(hL x hx).2]; rfl
    have := h.nodup.sublist ((List.filter_sublist : L.Sublist s.props).map _)
    rw [hm] at this
    exact this.of_map _
  have hmem : ∀ a ∈ H, ∃ x ∈ s.props, x.1 = v ∧ x.2.1 = a := fun a ha => by
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
    exact ⟨x, (hL x hx).1, (hL x hx).2, rfl⟩
  -- at most `w − certHeight` of them at or below `w`
  have hlow : (H.filter fun a => a ≤ w).length ≤ w - s.certHeight := by
    rw [← List.toFinset_card_of_nodup (hH.filter _), ← Nat.card_Ioc]
    refine Finset.card_le_card fun a ha => ?_
    obtain ⟨ha, haw⟩ := List.mem_filter.mp (List.mem_toFinset.mp ha)
    obtain ⟨x, hx, -, rfl⟩ := hmem a ha
    exact Finset.mem_Ioc.mpr ⟨h.over x hx, of_decide_eq_true haw⟩
  -- and at most one above it
  have hhigh : (H.filter fun a => ¬ a ≤ w).length ≤ 1 := by
    rw [← List.toFinset_card_of_nodup (hH.filter _)]
    refine Finset.card_le_one.mpr fun a ha b hb => ?_
    obtain ⟨ha, haw⟩ := List.mem_filter.mp (List.mem_toFinset.mp ha)
    obtain ⟨hb, hbw⟩ := List.mem_filter.mp (List.mem_toFinset.mp hb)
    obtain ⟨x, hx, hxv, rfl⟩ := hmem a ha
    obtain ⟨y, hy, hyv, rfl⟩ := hmem b hb
    exact h.latest x hx y hy (hxv.trans hyv.symm) (not_le.mp (of_decide_eq_true haw))
      (not_le.mp (of_decide_eq_true hbw))
  have hlen : L.length = H.length := (List.length_map _).symm
  rw [hlen, List.length_eq_length_filter_add (fun a => decide (a ≤ w))]
  simp only [decide_not] at hhigh
  omega

omit [LinearOrder BlockId] in
/-- The proposals number the sum over signers of each signer's. -/
theorem length_eq_sum_signer (ps : List (Validator × ℕ × BlockId)) :
    ps.length = ∑ v, (ps.filter fun x => x.1 = v).length := by
  induction ps with
  | nil => simp
  | cons x ps ih =>
    simp only [List.filter_cons, List.length_cons, ih]
    rw [Finset.sum_congr rfl fun v _ => (apply_ite List.length _ _ _ :
      (if decide (x.1 = v) = true then x :: ps.filter fun x => x.1 = v
        else ps.filter fun x => x.1 = v).length = _)]
    simp only [List.length_cons, decide_eq_true_eq]
    rw [Finset.sum_congr rfl fun v _ => (by split <;> rfl :
      (if x.1 = v then (ps.filter fun x => x.1 = v).length + 1
        else (ps.filter fun x => x.1 = v).length) =
        (ps.filter fun x => x.1 = v).length + if x.1 = v then 1 else 0)]
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq]
    simp

/-- **All the kept proposals** number at most `n` times
`lo + ahead − certHeight + 1`. -/
theorem Sparse.length_le {s : State Validator BlockId Payload} (h : Sparse cfg s) :
    s.props.length ≤ Fintype.card Validator * (s.lo + cfg.ahead - s.certHeight + 1) := by
  rw [length_eq_sum_signer]
  calc ∑ v, (s.props.filter fun x => x.1 = v).length
      ≤ ∑ _v : Validator, (s.lo + cfg.ahead - s.certHeight + 1) :=
        Finset.sum_le_sum fun v _ => h.signer_le v
    _ = _ := by rw [Finset.sum_const, smul_eq_mul, Finset.card_univ]

end Node

end LeanDag
