import LeanDag.Node.Helpers.Decided
import LeanDag.Node.Helpers.Wait
/-!
# Certifying the heights a node decides

Over a run without a restart a node keeps (`Kept`): its own proposal at
every multiple of `m` up to the height it last proposed and above its
certificate's, of the head of its first decisions there; its own
proposals only at heights it decided; and a certificate at every height
where its own proposal and `q` signers of one head meet. A peer's
proposal received at most `ahead` above the next undecided slot stays
kept until the certificate reaches its height, unless the peer sends
another head at that height. After each step the node has proposed
every height its decisions reach above its certificate (`Covered`).
-/

namespace LeanDag

namespace Node

variable {Validator BlockId Payload : Type} [Fintype Validator] [DecidableEq Validator]
variable [LinearOrder BlockId]
variable {cfg : Config Validator BlockId Payload}

/-- The distinct signers of the head `h` at height `k` among some proposals. -/
def signersOf (ps : List (Validator × ℕ × BlockId)) (k : ℕ) (h : BlockId) : Finset Validator :=
  ((ps.filter fun x => decide (x.2 = (k, h))).map Prod.fst).toFinset

omit [Fintype Validator] in
theorem mem_signersOf {ps : List (Validator × ℕ × BlockId)} {k : ℕ} {h : BlockId}
    {v : Validator} : v ∈ signersOf ps k h ↔ (v, k, h) ∈ ps := by
  simp only [signersOf, List.mem_toFinset, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨x, ⟨hx, hxk⟩, rfl⟩
    rw [← hxk]; exact hx
  · intro hv
    exact ⟨_, ⟨hv, rfl⟩, rfl⟩

omit [Fintype Validator] in
theorem signersOf_mono {ps ps' : List (Validator × ℕ × BlockId)} {k : ℕ} {h : BlockId}
    (hs : ∀ v, (v, k, h) ∈ ps → (v, k, h) ∈ ps') : signersOf ps k h ⊆ signersOf ps' k h :=
  fun v hv => mem_signersOf.mpr (hs v (mem_signersOf.mp hv))

variable (cfg) in
/-- **A good certificate**: of `q` distinct signers, at or below the next
undecided slot, with the head of the node's decisions at its height, a
multiple of `m`. -/
def CertGood (s : State Validator BlockId Payload) : Prop :=
  ∀ c, s.cert = some c → cfg.q ≤ c.signers.length ∧ c.signers.Nodup ∧ c.height ≤ s.lo ∧
    c.head = cfg.headOf (s.decided.reverse.take c.height) ∧ cfg.m ∣ c.height

variable (cfg) in
/-- **What a node keeps of its proposals**, with the peers' proposals `P`
it received in time. -/
structure Kept (P : List (Validator × ℕ × BlockId)) (s : State Validator BlockId Payload) :
    Prop where
  ledger : Ledger cfg s
  own_le : ∀ x ∈ s.props, x.1 = cfg.me → x.2.1 ≤ s.lo
  own_head : ∀ x ∈ s.props, x.1 = cfg.me → x.2.2 = cfg.headOf (s.decided.reverse.take x.2.1)
  own_dvd : ∀ x ∈ s.props, x.1 = cfg.me → cfg.m ∣ x.2.1
  own_mem : ∀ k, 0 < k → cfg.m ∣ k → k ≤ s.lastProposed → s.certHeight < k →
    (cfg.me, k, cfg.headOf (s.decided.reverse.take k)) ∈ s.props
  certified : ∀ k h, (cfg.me, k, h) ∈ s.props → cfg.q ≤ (signersOf s.props k h).card →
    k ≤ s.certHeight
  peers : ∀ x ∈ P, (x ∈ s.props ∨ x.2.1 ≤ s.certHeight) ∧ x.2.1 ≤ s.lo + cfg.ahead
  cert : CertGood cfg s

variable (cfg) in
/-- **Every height reached is proposed**: the next height to propose lies
above the decided frontier. -/
def Covered (s : State Validator BlockId Payload) : Prop := s.lo < nextHeight cfg s

/-! ## Heights -/

omit [Fintype Validator] in
/-- A multiple of `m` above the height last proposed and the certificate's
is at least the next height. -/
theorem nextHeight_le {s : State Validator BlockId Payload} {k : ℕ} (hm : cfg.m ∣ k)
    (hk : max s.lastProposed s.certHeight < k) : nextHeight cfg s ≤ k := by
  obtain ⟨j, rfl⟩ := hm
  unfold nextHeight
  apply Nat.mul_le_mul_left
  have := (Nat.div_lt_iff_lt_mul cfg.m_pos).mpr (by rw [Nat.mul_comm]; exact hk)
  omega

omit [Fintype Validator] in
theorem nextHeight_mono {s s' : State Validator BlockId Payload}
    (hp : s.lastProposed ≤ s'.lastProposed) (hc : s.certHeight ≤ s'.certHeight) :
    nextHeight cfg s ≤ nextHeight cfg s' := by
  unfold nextHeight
  apply Nat.mul_le_mul_left
  have := Nat.div_le_div_right (c := cfg.m) (max_le_max hp hc)
  omega

/-! ## Recording -/

omit [Fintype Validator] in
theorem record_certHeight (s : State Validator BlockId Payload) (v : Validator) (k : ℕ)
    (h : BlockId) : s.certHeight ≤ (record cfg s v k h).certHeight := by
  unfold record certify
  dsimp only
  split
  · rename_i hc
    change s.certHeight ≤ k
    exact hc.2.1.le
  · exact le_rfl

omit [Fintype Validator] in
theorem mem_record {s : State Validator BlockId Payload} {v : Validator} {k : ℕ} {h : BlockId}
    {y : Validator × ℕ × BlockId} :
    y ∈ (record cfg s v k h).props ↔
      (y = (v, k, h) ∨ y ∈ s.props ∧ (y.1 ≠ v ∨ y.2.1 ≠ k ∧
        (k ≤ s.lo + cfg.ahead ∨ y.2.1 ≤ s.lo + cfg.ahead))) ∧
      (record cfg s v k h).certHeight < y.2.1 := by
  unfold record above
  simp only [List.mem_filter, List.mem_cons, decide_eq_true_eq]
  rfl

omit [Fintype Validator] in
/-- **Recording certifies** the recorded height, once `q` signers of its
head are kept, the node's own among them, and its decisions reach it. -/
theorem record_certifies {s : State Validator BlockId Payload} {v : Validator} {k : ℕ}
    {h : BlockId}
    (hq : cfg.q ≤ (signersOf ((v, k, h) :: s.props.filter fun x =>
      x.1 ≠ v ∨ x.2.1 ≠ k ∧ (k ≤ s.lo + cfg.ahead ∨ x.2.1 ≤ s.lo + cfg.ahead)) k h).card)
    (hk : k ≤ s.lo)
    (hme : (cfg.me, k, h) ∈ (v, k, h) :: s.props.filter fun x =>
      x.1 ≠ v ∨ x.2.1 ≠ k ∧ (k ≤ s.lo + cfg.ahead ∨ x.2.1 ≤ s.lo + cfg.ahead)) :
    k ≤ (record cfg s v k h).certHeight := by
  by_cases hc : s.certHeight < k
  · unfold record certify
    dsimp only
    rw [if_pos ⟨by rw [← List.card_toFinset]; exact hq, hc, hk, hme⟩]
    exact le_rfl
  · exact (not_lt.mp hc).trans (record_certHeight s v k h)

omit [Fintype Validator] in
/-- **A recorded proposal is kept**, or the certificate reaches its height. -/
theorem record_self (s : State Validator BlockId Payload) (v : Validator) (k : ℕ) (h : BlockId) :
    (v, k, h) ∈ (record cfg s v k h).props ∨ k ≤ (record cfg s v k h).certHeight := by
  by_cases hc : (record cfg s v k h).certHeight < k
  · exact Or.inl (mem_record.mpr ⟨Or.inl rfl, hc⟩)
  · exact Or.inr (not_lt.mp hc)

omit [Fintype Validator] in
/-- **A good certificate stays good** as the decisions extend. -/
theorem CertGood.extend {s s' : State Validator BlockId Payload} (h : CertGood cfg s)
    (hL : Ledger cfg s) (hc : s'.cert = s.cert) (hlo : s.lo ≤ s'.lo)
    (hd : ∃ ds, s'.decided.reverse = s.decided.reverse ++ ds) : CertGood cfg s' := by
  obtain ⟨ds, hds⟩ := hd
  intro c hcs
  obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := h c (hc ▸ hcs)
  have hkd : c.height ≤ s.decided.reverse.length := by
    rw [List.length_reverse, hL.length]; exact h₃
  refine ⟨h₁, h₂, h₃.trans hlo, ?_, h₅⟩
  rw [hds, List.take_append_of_le_length hkd]; exact h₄

omit [Fintype Validator] in
/-- **Recording keeps the certificate good**, the node's own proposals,
and the one recorded if its own, having the heads of its decisions. -/
theorem CertGood.record {s : State Validator BlockId Payload} (h : CertGood cfg s)
    (hown : ∀ x ∈ s.props, x.1 = cfg.me → x.2.2 = cfg.headOf (s.decided.reverse.take x.2.1))
    (hdvd : ∀ x ∈ s.props, x.1 = cfg.me → cfg.m ∣ x.2.1)
    {v : Validator} {k : ℕ} {hd : BlockId}
    (hv : v = cfg.me → k ≤ s.lo ∧ hd = cfg.headOf (s.decided.reverse.take k) ∧ cfg.m ∣ k) :
    CertGood cfg (Node.record cfg s v k hd) := by
  intro c hc
  change (certify cfg { s with props := (v, k, hd) :: s.props.filter fun x =>
    x.1 ≠ v ∨ x.2.1 ≠ k ∧ (k ≤ s.lo + cfg.ahead ∨ x.2.1 ≤ s.lo + cfg.ahead) } k hd) = some c at hc
  unfold certify at hc
  dsimp only at hc
  split at hc
  · rename_i hcond
    rw [Option.some.injEq] at hc
    subst hc
    rcases List.mem_cons.mp hcond.2.2.2 with he | he
    · simp only [Prod.mk.injEq] at he
      obtain ⟨-, hh, hm⟩ := hv he.1.symm
      exact ⟨hcond.1, List.nodup_dedup _, hcond.2.2.1, hh, hm⟩
    · exact ⟨hcond.1, List.nodup_dedup _, hcond.2.2.1, hown _ (List.mem_filter.mp he).1 rfl,
        hdvd _ (List.mem_filter.mp he).1 rfl⟩
  · exact h c hc

omit [Fintype Validator] in
/-- **Recording keeps what the node keeps**, its own proposal at a height
it decided with the head there, a peer's with no other head at a kept
height. -/
theorem Kept.record {P : List (Validator × ℕ × BlockId)} {s : State Validator BlockId Payload}
    (hK : Kept cfg P s) {v : Validator} {k₀ : ℕ} {h₀ : BlockId}
    (hv : v = cfg.me → k₀ ≤ s.lo ∧ h₀ = cfg.headOf (s.decided.reverse.take k₀) ∧ cfg.m ∣ k₀)
    (hc : ∀ x ∈ P, x.1 = v → x.2.1 = k₀ → x.2.2 = h₀) :
    Kept cfg P (Node.record cfg s v k₀ h₀) := by
  have hcH := record_certHeight (cfg := cfg) s v k₀ h₀
  set s' := Node.record cfg s v k₀ h₀ with hs'
  have hlo : s'.lo = s.lo := rfl
  have hdec : s'.decided = s.decided := rfl
  have hlp : s'.lastProposed = s.lastProposed := rfl
  -- what `s'` keeps came from `s` or is the recorded one
  have hsub : ∀ y ∈ s'.props, y = (v, k₀, h₀) ∨ y ∈ s.props := fun y hy =>
    (mem_record.mp hy).1.imp id (fun h => h.1)
  refine ⟨hK.ledger, fun x hx hme => ?_, fun x hx hme => ?_, fun x hx hme => ?_,
    fun k hk hm hkl hkc => ?_, fun k h hme hq => ?_, fun x hx => ?_,
    hK.cert.record hK.own_head hK.own_dvd hv⟩
  · rcases hsub x hx with rfl | hx
    · exact (hv hme).1
    · exact hK.own_le x hx hme
  · rcases hsub x hx with rfl | hx
    · exact (hv hme).2.1
    · exact hK.own_head x hx hme
  · rcases hsub x hx with rfl | hx
    · exact (hv hme).2.2
    · exact hK.own_dvd x hx hme
  · have hold := hK.own_mem k hk hm hkl (lt_of_le_of_lt hcH hkc)
    rw [hdec]
    refine mem_record.mpr ⟨?_, hkc⟩
    by_cases hvm : v = cfg.me
    · obtain ⟨hk₀, hh₀, -⟩ := hv hvm
      by_cases hkk : k = k₀
      · subst hkk; exact Or.inl (by rw [hvm, hh₀])
      · exact Or.inr ⟨hold, Or.inr ⟨hkk, Or.inl (hk₀.trans (Nat.le_add_right _ _))⟩⟩
    · exact Or.inr ⟨hold, Or.inl (fun h => hvm h.symm)⟩
  · have hps : ∀ y ∈ s'.props, y ∈ (v, k₀, h₀) :: s.props.filter fun x =>
        x.1 ≠ v ∨ x.2.1 ≠ k₀ ∧ (k₀ ≤ s.lo + cfg.ahead ∨ x.2.1 ≤ s.lo + cfg.ahead) := by
      intro y hy
      rcases (mem_record.mp hy).1 with rfl | ⟨hy, hf⟩
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (List.mem_filter.mpr ⟨hy, by simpa using hf⟩)
    by_cases hkh : (k, h) = (k₀, h₀)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.injEq _ _ _ _ ▸ hkh
      have hq' := hq.trans (Finset.card_le_card (signersOf_mono (fun u hu => hps _ hu)))
      have hk₀ : k ≤ s.lo := by
        rcases hsub _ hme with he | he
        · exact (hv (Prod.mk.inj he).1.symm).1
        · exact hK.own_le _ he rfl
      exact record_certifies hq' hk₀ (hps _ hme)
    · have hold : ∀ u, (u, k, h) ∈ s'.props → (u, k, h) ∈ s.props := fun u hu => by
        rcases hsub _ hu with he | he
        · exact absurd (by simp only [Prod.mk.injEq] at he ⊢; exact ⟨he.2.1, he.2.2⟩) hkh
        · exact he
      exact (hK.certified k h (hold _ hme)
        (hq.trans (Finset.card_le_card (signersOf_mono hold)))).trans hcH
  · obtain ⟨hin, hw⟩ := hK.peers x hx
    refine ⟨?_, by rw [hlo]; exact hw⟩
    by_cases hkc : s'.certHeight < x.2.1
    · rcases hin with hin | hin
      · refine Or.inl (mem_record.mpr ⟨?_, hkc⟩)
        by_cases hxv : x.1 = v ∧ x.2.1 = k₀
        · left
          have := hc x hx hxv.1 hxv.2
          rw [← hxv.1, ← hxv.2, ← this]
        · right
          refine ⟨hin, ?_⟩
          by_cases hx1 : x.1 = v
          · exact Or.inr ⟨fun h => hxv ⟨hx1, h⟩, Or.inr hw⟩
          · exact Or.inl hx1
      · exact absurd (lt_of_le_of_lt (hin.trans hcH) hkc) (lt_irrefl _)
    · exact Or.inr (not_lt.mp hkc)

omit [Fintype Validator] in
theorem Covered.record {s : State Validator BlockId Payload} (h : Covered cfg s) (v : Validator)
    (k : ℕ) (hd : BlockId) : Covered cfg (Node.record cfg s v k hd) :=
  lt_of_lt_of_le h (nextHeight_mono le_rfl (record_certHeight s v k hd))

/-! ## Growing -/

omit [Fintype Validator] in
/-- **A change that keeps the proposals**, raises the decided frontier and
the certificate, and extends the decisions keeps what the node keeps. -/
theorem Kept.grow {P : List (Validator × ℕ × BlockId)} {s s' : State Validator BlockId Payload}
    (hK : Kept cfg P s) (hL : Ledger cfg s') (hp : s'.props = s.props)
    (hc : s.certHeight ≤ s'.certHeight) (hlo : s.lo ≤ s'.lo)
    (hlp : s'.lastProposed = s.lastProposed)
    (hd : ∃ ds, s'.decided.reverse = s.decided.reverse ++ ds) (hcg : CertGood cfg s') :
    Kept cfg P s' := by
  obtain ⟨ds, hds⟩ := hd
  refine ⟨hL, fun x hx hme => ?_, fun x hx hme => ?_, fun x hx hme => ?_,
    fun k hk hm hkl hkc => ?_, fun k h hme hq => ?_, fun x hx => ?_, hcg⟩
  · rw [hp] at hx; exact (hK.own_le x hx hme).trans hlo
  · rw [hp] at hx
    have hkd : x.2.1 ≤ s.decided.reverse.length := by
      rw [List.length_reverse, hK.ledger.length]; exact hK.own_le x hx hme
    rw [hds, List.take_append_of_le_length hkd]
    exact hK.own_head x hx hme
  · rw [hp] at hx; exact hK.own_dvd x hx hme
  · rw [hlp] at hkl
    have hkd : k ≤ s.decided.reverse.length := by
      rw [List.length_reverse, hK.ledger.length]; exact hkl.trans hK.ledger.2.1
    rw [hp, hds, List.take_append_of_le_length hkd]
    exact hK.own_mem k hk hm hkl (lt_of_le_of_lt hc hkc)
  · rw [hp] at hme hq; exact (hK.certified k h hme hq).trans hc
  · obtain ⟨hin, hw⟩ := hK.peers x hx
    exact ⟨by rw [hp]; exact hin.imp_right fun h => h.trans hc, hw.trans (by omega)⟩

omit [Fintype Validator] [DecidableEq Validator] [LinearOrder BlockId] in
theorem mem_above {c : Option (Cert Validator BlockId)} {ps : List (Validator × ℕ × BlockId)}
    {y : Validator × ℕ × BlockId} : y ∈ above c ps ↔ y ∈ ps ∧ (c.map Cert.height).getD 0 < y.2.1 :=
  by simp [above]

omit [Fintype Validator] in
/-- **Dropping the proposals at or below the certificate's height** keeps
what the node keeps. -/
theorem Kept.above {P : List (Validator × ℕ × BlockId)} {s s' : State Validator BlockId Payload}
    (hK : Kept cfg P s) (hp : s'.props = above s.cert s.props) (hc : s'.cert = s.cert)
    (hlo : s'.lo = s.lo) (hlp : s'.lastProposed = s.lastProposed) (hd : s'.decided = s.decided)
    (hch : s'.chain = s.chain) : Kept cfg P s' := by
  have hcH : s'.certHeight = s.certHeight := by simp [State.certHeight, hc]
  have hsub : ∀ y ∈ s'.props, y ∈ s.props := fun y hy => (mem_above.mp (hp ▸ hy)).1
  refine ⟨hK.ledger.of_eq hd hlo hlp hch, fun x hx hme => ?_, fun x hx hme => ?_,
    fun x hx hme => hK.own_dvd x (hsub x hx) hme, fun k hk hm hkl hkc => ?_,
    fun k h hme hq => ?_, fun x hx => ?_,
    hK.cert.extend hK.ledger hc hlo.ge ⟨[], by rw [hd, List.append_nil]⟩⟩
  · rw [hlo]; exact hK.own_le x (hsub x hx) hme
  · rw [hd]; exact hK.own_head x (hsub x hx) hme
  · rw [hlp] at hkl; rw [hcH] at hkc
    rw [hp, hd]; exact mem_above.mpr ⟨hK.own_mem k hk hm hkl hkc, hkc⟩
  · rw [hcH]
    exact hK.certified k h (hsub _ hme)
      (hq.trans (Finset.card_le_card (signersOf_mono fun u hu => hsub _ hu)))
  · obtain ⟨hin, hw⟩ := hK.peers x hx
    refine ⟨?_, by rw [hlo]; exact hw⟩
    rw [hcH]
    by_cases hx₂ : x.2.1 ≤ s.certHeight
    · exact Or.inr hx₂
    · exact Or.inl (by rw [hp]; exact mem_above.mpr ⟨hin.resolve_right hx₂, not_le.mp hx₂⟩)

omit [Fintype Validator] in
/-- A change of nothing the claims read. -/
theorem Kept.frame {P : List (Validator × ℕ × BlockId)} {s s' : State Validator BlockId Payload}
    (hK : Kept cfg P s) (hp : s'.props = s.props) (hc : s'.cert = s.cert) (hlo : s'.lo = s.lo)
    (hlp : s'.lastProposed = s.lastProposed) (hd : s'.decided = s.decided)
    (hch : s'.chain = s.chain) : Kept cfg P s' :=
  hK.grow (hK.ledger.of_eq hd hlo hlp hch) hp (by simp [State.certHeight, hc]) hlo.ge hlp
    ⟨[], by rw [hd, List.append_nil]⟩
    (hK.cert.extend hK.ledger hc hlo.ge ⟨[], by rw [hd, List.append_nil]⟩)

omit [Fintype Validator] in
theorem Covered.frame {s s' : State Validator BlockId Payload} (h : Covered cfg s)
    (hc : s'.cert = s.cert) (hlo : s'.lo = s.lo) (hlp : s'.lastProposed = s.lastProposed) :
    Covered cfg s' := by
  unfold Covered nextHeight State.certHeight at *
  rw [hc, hlo, hlp]; exact h

/-! ## Proposing -/

omit [Fintype Validator] in
/-- **Proposing once keeps what the node keeps.** -/
theorem Kept.proposeNext {P : List (Validator × ℕ × BlockId)}
    {s s₁ : State Validator BlockId Payload} {o : Output Validator BlockId Payload} (hK : Kept cfg P s) (hP : ∀ x ∈ P, x.1 ≠ cfg.me)
    (hn : proposeNext cfg s = some (s₁, o)) : Kept cfg P s₁ := by
  have hL₁ := (proposeNext_ledger hK.ledger hn).1
  obtain ⟨hk₀, rfl, -⟩ := proposeNext_some hn
  set k₀ := nextHeight cfg s
  set hd := ((s.decided.take (s.lo - s.lastProposed)).reverse.take (k₀ - s.lastProposed)).foldl
    cfg.extend s.chain
  have hhd : hd = cfg.headOf (s.decided.reverse.take k₀) := hL₁.2.2
  have hr := hK.record (v := cfg.me) (k₀ := k₀) (h₀ := hd) (fun _ => ⟨hk₀, hhd, Dvd.intro _ rfl⟩)
    (fun x hx h => absurd h (hP x hx))
  refine ⟨hL₁, hr.own_le, hr.own_head, hr.own_dvd, fun k hk hm hkl hkc => ?_, hr.certified,
    hr.peers, hr.cert⟩
  change k ≤ k₀ at hkl
  change (Node.record cfg s cfg.me k₀ hd).certHeight < k at hkc
  by_cases hlp : k ≤ s.lastProposed
  · exact hr.own_mem k hk hm hlp hkc
  · have hck : s.certHeight < k := lt_of_le_of_lt (record_certHeight s _ _ _) hkc
    have hkk : k = k₀ := le_antisymm hkl (nextHeight_le hm (max_lt (not_le.mp hlp) hck))
    subst hkk
    change (cfg.me, nextHeight cfg s, cfg.headOf (s.decided.reverse.take (nextHeight cfg s))) ∈
      (Node.record cfg s cfg.me (nextHeight cfg s) hd).props
    rw [← hhd]
    exact mem_record.mpr ⟨Or.inl rfl, hkc⟩

omit [Fintype Validator] in
theorem proposeNext_frame {s s₁ : State Validator BlockId Payload}
    {o : Output Validator BlockId Payload} (hn : proposeNext cfg s = some (s₁, o)) :
    s₁.lo = s.lo ∧ s.lastProposed < s₁.lastProposed ∧ s.certHeight ≤ s₁.certHeight := by
  obtain ⟨-, rfl, -⟩ := proposeNext_some hn
  exact ⟨rfl, lastProposed_lt_nextHeight s, record_certHeight _ _ _ _⟩

omit [Fintype Validator] in
theorem Kept.proposeFrom {P : List (Validator × ℕ × BlockId)} (hP : ∀ x ∈ P, x.1 ≠ cfg.me) :
    ∀ (fuel : ℕ) {s : State Validator BlockId Payload}, Kept cfg P s →
      Kept cfg P (Node.proposeFrom cfg fuel s).1 ∧
        (s.lo < fuel + s.lastProposed → Covered cfg (Node.proposeFrom cfg fuel s).1)
  | 0, s, hK => ⟨hK, fun h => absurd hK.ledger.2.1 (by simp only [Nat.zero_add] at h; omega)⟩
  | fuel + 1, s, hK => by
    rw [proposeFrom_succ]
    split
    · rename_i s₁ o hn
      obtain ⟨hlo, hlp, -⟩ := proposeNext_frame hn
      obtain ⟨h₁, h₂⟩ := Kept.proposeFrom hP fuel (hK.proposeNext hP hn)
      exact ⟨h₁, fun h => h₂ (by omega)⟩
    · rename_i hn
      refine ⟨hK, fun _ => ?_⟩
      unfold Node.proposeNext at hn
      dsimp only at hn
      split at hn
      · simp at hn
      · rename_i hk; exact not_le.mp hk

omit [Fintype Validator] in
/-- **Proposing keeps what the node keeps**, and every height reached is
then proposed. -/
theorem Kept.proposeAt {P : List (Validator × ℕ × BlockId)} {s : State Validator BlockId Payload}
    (hK : Kept cfg P s) (hP : ∀ x ∈ P, x.1 ≠ cfg.me) :
    Kept cfg P (Node.proposeAt cfg s).1 ∧ Covered cfg (Node.proposeAt cfg s).1 := by
  obtain ⟨h₁, h₂⟩ := Kept.proposeFrom hP (s.lo + 1) hK
  exact ⟨h₁, h₂ (by omega)⟩

/-! ## Building, deciding, collecting -/

omit [Fintype Validator] in
theorem tryBuild_frame {s s' : State Validator BlockId Payload}
    {out : List (Output Validator BlockId Payload)} (h : tryBuild cfg s = some (s', out)) :
    s'.props = s.props ∧ s'.cert = s.cert ∧ s'.lo = s.lo ∧ s'.lastProposed = s.lastProposed ∧
      s'.decided = s.decided ∧ s'.chain = s.chain := by
  unfold tryBuild at h
  split at h
  · dsimp only at h
    split at h
    · split at h
      · rw [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
      · exact absurd h (by simp)
    · exact absurd h (by simp)
  · exact absurd h (by simp)

omit [Fintype Validator] in
theorem progress_frame : ∀ (fuel : ℕ) (s : State Validator BlockId Payload),
    (progress cfg fuel s).1.props = s.props ∧ (progress cfg fuel s).1.cert = s.cert ∧
      (progress cfg fuel s).1.lo = s.lo ∧
      (progress cfg fuel s).1.lastProposed = s.lastProposed ∧
      (progress cfg fuel s).1.decided = s.decided ∧ (progress cfg fuel s).1.chain = s.chain
  | 0, s => ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  | fuel + 1, s => by
    unfold Node.progress
    split
    · rename_i s₁ out h
      obtain ⟨a₁, b₁, c₁, d₁, e₁, f₁⟩ := tryBuild_frame h
      obtain ⟨a₂, b₂, c₂, d₂, e₂, f₂⟩ := progress_frame fuel s₁
      exact ⟨a₂.trans a₁, b₂.trans b₁, c₂.trans c₁, d₂.trans d₁, e₂.trans e₁, f₂.trans f₁⟩
    · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

omit [Fintype Validator] in
theorem collect_frame (s : State Validator BlockId Payload) :
    (collect cfg s).1.props = s.props ∧ (collect cfg s).1.cert = s.cert ∧
      (collect cfg s).1.lo = s.lo ∧ (collect cfg s).1.lastProposed = s.lastProposed ∧
      (collect cfg s).1.decided = s.decided ∧ (collect cfg s).1.chain = s.chain := by
  unfold Node.collect
  split
  · dsimp only
    split <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

omit [Fintype Validator] in
/-- **Deciding keeps what the node keeps**, and every height reached is
then proposed. -/
theorem Kept.decideStep {P : List (Validator × ℕ × BlockId)} {s : State Validator BlockId Payload}
    (hK : Kept cfg P s) (hP : ∀ x ∈ P, x.1 ≠ cfg.me) :
    Kept cfg P (Node.decideStep cfg s).1 ∧ Covered cfg (Node.decideStep cfg s).1 := by
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
    have hL := hK.ledger
    have hL₁ : Ledger cfg s₁ := by
      have hlp : s.lastProposed ≤ s.decided.reverse.length := by
        rw [List.length_reverse, hL.length]; exact hL.2.1
      refine ⟨by rw [hD₁]; exact Ledger.append hL.1 hfst, hL.2.1.trans (Nat.le_add_right _ _), ?_⟩
      change s.chain = cfg.headOf (s₁.decided.reverse.take s.lastProposed)
      rw [hD₁, List.take_append_of_le_length hlp]; exact hL.2.2
    exact (hK.grow hL₁ rfl le_rfl (Nat.le_add_right _ _) rfl ⟨ds, hD₁⟩
      (hK.cert.extend hL rfl (Nat.le_add_right _ _) ⟨ds, hD₁⟩)).proposeAt hP
  · exact hK.proposeAt hP

omit [Fintype Validator] in
/-- **Advancing keeps what the node keeps**, and every height reached is
then proposed. -/
theorem Kept.advance {P : List (Validator × ℕ × BlockId)} {s : State Validator BlockId Payload}
    (hK : Kept cfg P s) (hP : ∀ x ∈ P, x.1 ≠ cfg.me) :
    Kept cfg P (Node.advance cfg s).1 ∧ Covered cfg (Node.advance cfg s).1 := by
  simp only [Node.advance]
  obtain ⟨a₁, b₁, c₁, d₁, e₁, f₁⟩ := progress_frame (cfg := cfg) (s.store.topRound + 2) s
  have h₁ := hK.frame a₁ b₁ c₁ d₁ e₁ f₁
  obtain ⟨h₂, hc₂⟩ := h₁.decideStep hP
  generalize Node.decideStep cfg (progress cfg (s.store.topRound + 2) s).1 = d at h₂ hc₂
  obtain ⟨a₃, b₃, c₃, d₃, e₃, f₃⟩ := collect_frame (cfg := cfg) d.1
  exact ⟨h₂.frame a₃ b₃ c₃ d₃ e₃ f₃, hc₂.frame b₃ c₃ d₃⟩

variable (cfg) in
/-- **A certificate good for a state**: of `q` distinct signers at a
multiple of `m`, at or below the state's certificate's height, with the
head of its decisions there. -/
def GoodFor (c : Cert Validator BlockId) (s : State Validator BlockId Payload) : Prop :=
  cfg.q ≤ c.signers.length ∧ c.signers.Nodup ∧ cfg.m ∣ c.height ∧ c.height ≤ s.certHeight ∧
    c.head = cfg.headOf (s.decided.reverse.take c.height)

omit [Fintype Validator] in
theorem Kept.hold {P : List (Validator × ℕ × BlockId)} {s : State Validator BlockId Payload}
    (h : Kept cfg P s) : Kept cfg P s.hold :=
  ⟨h.ledger, h.own_le, h.own_head, h.own_dvd, h.own_mem, h.certified, h.peers, h.cert⟩

omit [Fintype Validator] in
/-- The certificate's height lies at or below the next undecided slot. -/
theorem Kept.certHeight_le {P : List (Validator × ℕ × BlockId)}
    {s : State Validator BlockId Payload} (hK : Kept cfg P s) : s.certHeight ≤ s.lo := by
  unfold State.certHeight
  rcases hc : s.cert with _ | c
  · simp
  · simpa using (hK.cert c hc).2.2.1

omit [Fintype Validator] in
/-- **A good certificate stays good** as the certificate rises and the
decisions extend. -/
theorem GoodFor.transfer {P : List (Validator × ℕ × BlockId)} {c : Cert Validator BlockId}
    {s s' : State Validator BlockId Payload} (h : GoodFor cfg c s) (hK : Kept cfg P s)
    (hc : s.certHeight ≤ s'.certHeight) (hd : ∃ ds, s'.decided.reverse = s.decided.reverse ++ ds) :
    GoodFor cfg c s' := by
  obtain ⟨ds, hds⟩ := hd
  obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := h
  have hkd : c.height ≤ s.decided.reverse.length := by
    rw [List.length_reverse, hK.ledger.length]; exact h₄.trans hK.certHeight_le
  refine ⟨h₁, h₂, h₃, h₄.trans hc, ?_⟩
  rw [hds, List.take_append_of_le_length hkd]; exact h₅

omit [Fintype Validator] in
theorem proposeFrom_certHeight : ∀ (fuel : ℕ) (s : State Validator BlockId Payload),
    s.certHeight ≤ (Node.proposeFrom cfg fuel s).1.certHeight
  | 0, _ => le_rfl
  | fuel + 1, s => by
    rw [proposeFrom_succ]
    split
    · rename_i s₁ o hn
      exact (proposeNext_frame hn).2.2.trans (proposeFrom_certHeight fuel s₁)
    · exact le_rfl

omit [Fintype Validator] in
theorem certHeight_advance (s : State Validator BlockId Payload) :
    s.certHeight ≤ (Node.advance cfg s).1.certHeight := by
  simp only [Node.advance]
  generalize hp : progress cfg (s.store.topRound + 2) s = p
  have b₁ : p.1.cert = s.cert := hp ▸ (progress_frame (cfg := cfg) _ s).2.1
  have h₂ : p.1.certHeight ≤ (Node.decideStep cfg p.1).1.certHeight := by
    unfold Node.decideStep; dsimp only
    split <;> (refine le_trans ?_ (proposeFrom_certHeight (cfg := cfg) _ _); exact le_rfl)
  generalize Node.decideStep cfg p.1 = d at h₂
  have b₃ : (Node.collect cfg d.1).1.cert = d.1.cert := (collect_frame (cfg := cfg) d.1).2.1
  change s.certHeight ≤ (Node.collect cfg d.1).1.certHeight
  unfold State.certHeight at h₂ ⊢
  rw [b₃, ← b₁]; exact h₂

omit [Fintype Validator] in
theorem certHeight_quiesce (n : ℕ) (s : State Validator BlockId Payload) :
    s.certHeight ≤ (quiesce cfg n s).1.certHeight :=
  (quiesce_rel (P := fun _ => True) (R := fun a _ b => a.certHeight ≤ b.certHeight)
    (fun _ => le_rfl) (fun _ _ _ _ _ h₁ h₂ => h₁.trans h₂)
    (fun s _ => ⟨certHeight_advance s, trivial⟩) n s trivial).1

omit [Fintype Validator] in
theorem collect_announce {s : State Validator BlockId Payload} {c : Cert Validator BlockId}
    (h : Output.announce c ∈ (Node.collect cfg s).2) : s.cert = some c := by
  unfold Node.collect at h
  split at h
  · dsimp only at h
    split at h
    · rcases List.mem_cons.mp h with h | h
      · cases h
      · obtain ⟨c', hc', he⟩ := List.mem_map.mp h
        cases he
        exact Option.mem_def.mp (Option.mem_toList.mp hc')
    · simp at h
  · simp at h

omit [Fintype Validator] in
/-- **A certificate a pass announces** is good for the state it leaves. -/
theorem Kept.advance_announce {P : List (Validator × ℕ × BlockId)}
    {s : State Validator BlockId Payload} (hK : Kept cfg P s) (hP : ∀ x ∈ P, x.1 ≠ cfg.me)
    {c : Cert Validator BlockId} (h : Output.announce c ∈ (Node.advance cfg s).2) :
    GoodFor cfg c (Node.advance cfg s).1 := by
  simp only [Node.advance] at h ⊢
  obtain ⟨a₁, b₁, c₁, d₁, e₁, f₁⟩ := progress_frame (cfg := cfg) (s.store.topRound + 2) s
  have h₁ := hK.frame a₁ b₁ c₁ d₁ e₁ f₁
  obtain ⟨bs, hbs⟩ := progress_built (cfg := cfg) (s.store.topRound + 2) s
  have h₂ := (h₁.decideStep hP).1
  have hd2 : ∀ o ∈ (Node.decideStep cfg (progress cfg (s.store.topRound + 2) s).1).2,
      o ≠ Output.announce c := by
    intro o ho
    unfold Node.decideStep at ho
    dsimp only at ho
    split at ho
    · rcases List.mem_append.mp ho with ho | ho
      · obtain ⟨_, -, rfl⟩ := List.mem_map.mp ho; simp
      · obtain ⟨-, -, -, -, -, hpo⟩ := proposeAt_eq (cfg := cfg) _
        obtain ⟨k, hk, rfl⟩ := hpo _ ho; simp
    · obtain ⟨-, -, -, -, -, hpo⟩ := proposeAt_eq (cfg := cfg) _
      obtain ⟨k, hk, rfl⟩ := hpo _ ho; simp
  generalize Node.decideStep cfg (progress cfg (s.store.topRound + 2) s).1 = d at h₂ hd2 h
  rw [hbs] at h
  rcases List.mem_append.mp h with h | h
  · rcases List.mem_append.mp h with h | h
    · simp [built] at h
    · exact absurd rfl (hd2 _ h)
  · have hdc := collect_announce h
    obtain ⟨-, b₃, -, -, e₃, -⟩ := collect_frame (cfg := cfg) d.1
    obtain ⟨q₁, q₂, q₃, q₄, q₅⟩ := h₂.cert c hdc
    refine ⟨q₁, q₂, q₅, ?_, ?_⟩
    · change c.height ≤ ((Node.collect cfg d.1).1.cert.map Cert.height).getD 0
      rw [b₃, hdc]; simp
    · change c.head = cfg.headOf ((Node.collect cfg d.1).1.decided.reverse.take c.height)
      rw [e₃]; exact q₄

omit [Fintype Validator] in
theorem Kept.quiesce {P : List (Validator × ℕ × BlockId)} (hP : ∀ x ∈ P, x.1 ≠ cfg.me) :
    ∀ (n : ℕ) {s : State Validator BlockId Payload}, Kept cfg P s →
      Kept cfg P (Node.quiesce cfg (n + 1) s).1 ∧ Covered cfg (Node.quiesce cfg (n + 1) s).1 ∧
        ∀ c, Output.announce c ∈ (Node.quiesce cfg (n + 1) s).2 →
          GoodFor cfg c (Node.quiesce cfg (n + 1) s).1
  | n, s, hK => by
    rcases quiesce_succ_cases (cfg := cfg) n s with he | he <;> rw [he]
    · exact ⟨(hK.advance hP).1, (hK.advance hP).2, fun c hc => hK.advance_announce hP hc⟩
    · cases n with
      | zero =>
        simp only [Node.quiesce, List.append_nil]
        exact ⟨(hK.advance hP).1, (hK.advance hP).2, fun c hc => hK.advance_announce hP hc⟩
      | succ n =>
        obtain ⟨h₁, h₂, h₃⟩ := Kept.quiesce hP n (hK.advance hP).1
        refine ⟨h₁, h₂, fun c hc => ?_⟩
        rcases List.mem_append.mp hc with hc | hc
        · exact (hK.advance_announce hP hc).transfer (hK.advance hP).1
            (certHeight_quiesce _ _)
            ⟨_, (quiesce_appends (cfg := cfg) (n + 1) (hK.advance hP).1.ledger).1.1⟩
        · exact h₃ c hc

omit [Fintype Validator] in
theorem Kept.settle {P : List (Validator × ℕ × BlockId)} {s : State Validator BlockId Payload}
    (hK : Kept cfg P s) (hP : ∀ x ∈ P, x.1 ≠ cfg.me) (hr : s.recovering = false) :
    Kept cfg P (Node.settle cfg s).1 ∧ Covered cfg (Node.settle cfg s).1 ∧
      ∀ c, Output.announce c ∈ (Node.settle cfg s).2 → GoodFor cfg c (Node.settle cfg s).1 := by
  obtain ⟨n, hn⟩ := passes_succ (cfg := cfg) s.hold
  rw [settle_of_idle hr, hn]; exact Kept.quiesce hP n hK.hold

/-! ## A step, and a run -/

omit [Fintype Validator] in
/-- **Confirming a certificate keeps what the node keeps**, and every
height reached is then proposed. -/
theorem Kept.confirm {P : List (Validator × ℕ × BlockId)} {s : State Validator BlockId Payload}
    (hK : Kept cfg P s) (hP : ∀ x ∈ P, x.1 ≠ cfg.me) (hrec : s.recovering = false)
    {c : Cert Validator BlockId} (hcf : confirms cfg s c = true) :
    Kept cfg P (Node.confirm cfg s c).1 ∧ Covered cfg (Node.confirm cfg s c).1 ∧
      ∀ c', Output.announce c' ∈ (Node.confirm cfg s c).2 →
        GoodFor cfg c' (Node.confirm cfg s c).1 := by
  unfold confirms at hcf
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hcf
  have hcH : s.certHeight ≤
      ({ s with cert := some c } : State Validator BlockId Payload).certHeight :=
    hcf.1.1.2.le
  have hcg : CertGood cfg ({ s with cert := some c } : State Validator BlockId Payload) := by
    intro c' hc'
    rw [show c' = c from (Option.some.inj hc').symm]
    exact ⟨hcf.1.1.1.1, hcf.1.1.1.2, hcf.1.2, hK.own_head _ hcf.2 rfl, hK.own_dvd _ hcf.2 rfl⟩
  have hK₁ := hK.grow (s' := { s with cert := some c }) hK.ledger rfl hcH le_rfl rfl
    ⟨[], by rw [List.append_nil]⟩ hcg
  exact (hK₁.above (s' := { s with cert := some c, props := Node.above (some c) s.props })
    rfl rfl rfl rfl rfl rfl).settle hP hrec

/-- **A step keeps what the node keeps**, short of a restart, a
recovering node, and a proposal of another head at a kept peer's height
from that peer; and every height reached is then proposed. -/
theorem Kept.step {P : List (Validator × ℕ × BlockId)} {s : State Validator BlockId Payload}
    {inp : Input Validator BlockId Payload} (hK : Kept cfg P s) (hcov : Covered cfg s)
    (hP : ∀ x ∈ P, x.1 ≠ cfg.me) (hrec : s.recovering = false) (hr : inp ≠ .restart)
    (hc : ∀ x ∈ P, ∀ u k h, inp = .proposal u k h → x.1 = u → x.2.1 = k → x.2.2 = h) :
    Kept cfg P (Node.step cfg s inp).1 ∧ Covered cfg (Node.step cfg s inp).1 ∧
      ∀ c, Output.announce c ∈ (Node.step cfg s inp).2 → GoodFor cfg c (Node.step cfg s inp).1 := by
  -- a step that settles a state that differs from `s` in nothing the claims read
  have hset : ∀ s₀ : State Validator BlockId Payload, s₀.props = s.props → s₀.cert = s.cert →
      s₀.lo = s.lo → s₀.lastProposed = s.lastProposed → s₀.decided = s.decided →
      s₀.chain = s.chain → s₀.recovering = false →
      Kept cfg P (Node.settle cfg s₀).1 ∧ Covered cfg (Node.settle cfg s₀).1 ∧
        ∀ c, Output.announce c ∈ (Node.settle cfg s₀).2 → GoodFor cfg c (Node.settle cfg s₀).1 :=
    fun s₀ a b c d e f g => (hK.frame a b c d e f).settle hP g
  -- outputs before a settle's announce nothing
  have hpre : ∀ (r : State Validator BlockId Payload × List (Output Validator BlockId Payload))
      (outs : List (Output Validator BlockId Payload)), (∀ c, Output.announce c ∉ outs) →
      Kept cfg P r.1 ∧ Covered cfg r.1 ∧ (∀ c, Output.announce c ∈ r.2 → GoodFor cfg c r.1) →
      Kept cfg P r.1 ∧ Covered cfg r.1 ∧ ∀ c, Output.announce c ∈ outs ++ r.2 → GoodFor cfg c r.1 :=
    fun r outs hn ⟨h₁, h₂, h₃⟩ => ⟨h₁, h₂, fun c hc =>
      (List.mem_append.mp hc).elim (fun h => absurd h (hn c)) (h₃ c)⟩
  have hnil : Kept cfg P s ∧ Covered cfg s ∧
      ∀ c, Output.announce c ∈ ([] : List (Output Validator BlockId Payload)) → GoodFor cfg c s :=
    ⟨hK, hcov, fun _ h => absurd h List.not_mem_nil⟩
  cases inp with
  | start =>
    simp only [Node.step]
    split
    · split
      · refine hpre (Node.settle cfg _) _ ?_ (hset _ rfl rfl rfl rfl rfl rfl rfl)
        simp
      · exact hnil
    · exact hnil
  | deliver id b =>
    simp only [Node.step]
    split
    · refine hpre (Node.settle cfg _) _ ?_ (hset _ rfl rfl rfl rfl rfl rfl hrec)
      intro c; split_ifs <;> simp
    · exact hnil
  | timer r => exact hset _ rfl rfl rfl rfl rfl rfl hrec
  | fetchRequest peer G ids => exact ⟨hK, hcov, fun c hc => by simp [Node.step, answer] at hc⟩
  | restart => exact absurd rfl hr
  | baseOffer p G bs =>
    simp only [Node.step]
    rw [if_neg (by simp [hrec])]
    exact hnil
  | certOffer p c ds =>
    rcases certOffer_cases (cfg := cfg) s p c ds with ⟨h₁, -, -⟩ | ⟨-, ds', -, -, ha, he⟩ |
      ⟨-, -, hcf, he⟩ | ⟨-, he⟩
    · rw [hrec] at h₁; cases h₁
    · obtain ⟨hL₁, hD⟩ := adopted_ledger hK.ledger ha
      have hcH : s.certHeight ≤ (adopted s c ds').certHeight := by
        unfold adopted State.certHeight; dsimp only
        split
        · rename_i h; simp only [Option.map_some, Option.getD_some]
          exact h.le
        · exact le_rfl
      have hcg : CertGood cfg ({ adopted s c ds' with props := s.props } :
          State Validator BlockId Payload) := by
        have ha' := ha
        unfold adoptable at ha'
        simp only [Bool.and_eq_true, decide_eq_true_eq] at ha'
        by_cases hlt : s.certHeight < c.height
        · intro c' hc'
          have hcc : ({ adopted s c ds' with props := s.props } :
              State Validator BlockId Payload).cert = some c := by
            simp [adopted, hlt]
          rw [hcc, Option.some.injEq] at hc'
          subst hc'
          refine ⟨ha'.1.1.1.1, ha'.1.1.1.2, le_rfl, ?_, adoptable_dvd ha⟩
          change c.head = cfg.headOf ((ds'.reverse ++ s.decided).reverse.take c.height)
          have hlen : (ds'.reverse ++ s.decided).reverse.length = c.height := by
            rw [List.reverse_append, List.reverse_reverse, List.length_append, List.length_reverse,
              hK.ledger.length]
            have := congrArg List.length ha'.1.2
            simp only [List.length_map, List.length_range'] at this
            have := ha'.1.1.2.1
            omega
          rw [← hlen, List.take_length, List.reverse_append, List.reverse_reverse]
          exact (adoptable_head hK.ledger ha).symm
        · have hcc : ({ adopted s c ds' with props := s.props } :
              State Validator BlockId Payload).cert = s.cert := by
            simp [adopted, hlt]
          exact hK.cert.extend hK.ledger hcc (adoptable_lo ha).le ⟨ds', hD⟩
      have hK₁ := hK.grow (s' := { adopted s c ds' with props := s.props }) hL₁ rfl hcH
        (adoptable_lo ha).le rfl ⟨ds', hD⟩ hcg
      rw [he, adopt_eq]
      exact hpre (Node.settle cfg (adopted s c ds')) _ (by simp)
        ((hK₁.above (s' := adopted s c ds') rfl rfl rfl rfl rfl rfl).settle hP hrec)
    · rw [he]; exact hK.confirm hP hrec hcf
    · rw [he]; exact hnil
  | announced p c =>
    rcases announced_cases (cfg := cfg) s p c with ⟨-, hcf, he⟩ | he | he <;> rw [he]
    · exact hK.confirm hP hrec hcf
    · exact ⟨hK, hcov, fun c hc => by simp at hc⟩
    · exact hnil
  | proposal p k kh =>
    rw [step_proposal]
    split
    · rename_i hp
      obtain ⟨n, hn⟩ := seek_eq (cfg := cfg) (Node.record cfg s p k kh) k kh
      have hno : ∀ c, Output.announce c ∉ (seek cfg (Node.record cfg s p k kh) k kh).2 := by
        intro c; unfold seek; dsimp only; split <;> simp
      rw [hn] at ⊢
      have hr := hK.record (v := p) (k₀ := k) (h₀ := kh) (fun h => absurd h hp)
        (fun x hx h1 h2 => hc x hx p k kh rfl h1 h2)
      exact hpre (Node.settle cfg { Node.record cfg s p k kh with sought := n }) _ hno
        ((hr.frame (s' := { Node.record cfg s p k kh with sought := n }) rfl rfl rfl rfl rfl
          rfl).settle hP hrec)
    · exact hnil
  | baseRequest => exact ⟨hK, hcov, fun c hc => by simp [Node.step] at hc⟩
  | decisionRequest peer lo =>
    refine ⟨hK, hcov, fun c hc => ?_⟩
    simp only [Node.step] at hc
    split at hc
    · unfold serveFrom at hc
      split at hc
      · split at hc <;> simp at hc
      · simp at hc
    · simp at hc

/-- **A run keeps what the node keeps**, under the step's conditions. -/
theorem Kept.run {P : List (Validator × ℕ × BlockId)} (hP : ∀ x ∈ P, x.1 ≠ cfg.me) :
    ∀ (is : List (Input Validator BlockId Payload)) {s : State Validator BlockId Payload},
      Kept cfg P s → Covered cfg s → s.recovering = false → (∀ i ∈ is, i ≠ .restart) →
      (∀ x ∈ P, ∀ u k h, Input.proposal u k h ∈ is → x.1 = u → x.2.1 = k → x.2.2 = h) →
      Kept cfg P (Node.run cfg s is).1 ∧ Covered cfg (Node.run cfg s is).1 ∧
        (Node.run cfg s is).1.recovering = false
  | [], s, hK, hcov, hrec, _, _ => ⟨hK, hcov, hrec⟩
  | i :: is, s, hK, hcov, hrec, hr, hc => by
    simp only [Node.run]
    have hri : i ≠ .restart := hr i (List.mem_cons_self ..)
    obtain ⟨hK₁, hcov₁, -⟩ := hK.step hcov hP hrec hri
      (fun x hx u k h hi => hc x hx u k h (hi ▸ List.mem_cons_self ..))
    exact Kept.run hP is hK₁ hcov₁ (step_calm hrec hri).1
      (fun j hj => hr j (List.mem_cons_of_mem _ hj))
      (fun x hx u k h hi => hc x hx u k h (List.mem_cons_of_mem _ hi))

omit [Fintype Validator] in
theorem Kept.init : Kept cfg [] (State.init cfg) :=
  ⟨Ledger.init, fun x hx => absurd hx List.not_mem_nil, fun x hx => absurd hx List.not_mem_nil,
    fun x hx => absurd hx List.not_mem_nil, fun k hk _ hkl => absurd hkl (by
    change ¬ k ≤ 0; omega), fun k h hx => absurd hx List.not_mem_nil, fun x hx => absurd hx
    List.not_mem_nil, fun c hc => absurd hc (by simp [State.init])⟩

omit [Fintype Validator] in
theorem Covered.init : Covered cfg (State.init cfg) := by
  unfold Covered nextHeight
  change 0 < cfg.m * (max 0 0 / cfg.m + 1)
  simp [cfg.m_pos]

/-- **A peer's proposal kept from its receipt**: over a run without a
restart, a proposal received at most `ahead` above the next undecided
slot, from a peer that sends no other head at its height, is kept at
the end, or the certificate reaches its height. -/
theorem kept_peer {u : Validator} {k : ℕ} {h : BlockId}
    {is₁ is₂ : List (Input Validator BlockId Payload)} (hu : u ≠ cfg.me)
    (hr : ∀ i ∈ is₁ ++ .proposal u k h :: is₂, i ≠ .restart)
    (hw : k ≤ (Node.run cfg (State.init cfg) is₁).1.lo + cfg.ahead)
    (hc : ∀ h', Input.proposal u k h' ∈ is₂ → h' = h) :
    let s := (Node.run cfg (State.init cfg) (is₁ ++ .proposal u k h :: is₂)).1
    Kept cfg [] s ∧ Covered cfg s ∧ ((u, k, h) ∈ s.props ∨ k ≤ s.certHeight) := by
  intro s
  have hr₁ : ∀ i ∈ is₁, i ≠ .restart := fun i hi => hr i (List.mem_append_left _ hi)
  obtain ⟨hK₀, hcov₀, hrec₀⟩ := Kept.run (P := []) (cfg := cfg) (by simp) is₁ Kept.init
    Covered.init rfl hr₁ (by simp)
  set s₀ := (Node.run cfg (State.init cfg) is₁).1
  -- the receipt
  obtain ⟨n, hn⟩ := seek_eq (cfg := cfg) (record cfg s₀ u k h) k h
  set s₁ := (Node.step cfg s₀ (.proposal u k h)).1
  have hs₁ : s₁ = (Node.settle cfg { record cfg s₀ u k h with sought := n }).1 := by
    simp only [s₁, step_proposal, if_pos hu, hn]
  have hKc : Kept cfg [(u, k, h)] s₁ ∧ Covered cfg s₁ := by
    rw [hs₁]
    have hr := hK₀.record (v := u) (k₀ := k) (h₀ := h) (fun h => absurd h hu) (by simp)
    have hK' : Kept cfg [(u, k, h)] { record cfg s₀ u k h with sought := n } :=
      ⟨hr.ledger, hr.own_le, hr.own_head, hr.own_dvd, hr.own_mem, hr.certified, fun x hx => by
        rw [List.mem_singleton.mp hx]
        exact ⟨record_self s₀ u k h, hw⟩, hr.cert⟩
    exact (hK'.settle (by simpa using hu) hrec₀).imp_right And.left
  obtain ⟨hK₁, hcov₁⟩ := hKc
  have hrec₁ : s₁.recovering = false :=
    (step_calm hrec₀ (hr _ (List.mem_append_right _ (List.mem_cons_self ..)))).1
  obtain ⟨hK₂, hcov₂, -⟩ := Kept.run (cfg := cfg) (P := [(u, k, h)]) (by simpa using hu) is₂
    hK₁ hcov₁ hrec₁ (fun i hi => hr i (List.mem_append_right _ (List.mem_cons_of_mem _ hi)))
    (fun x hx u' k' h' hi h1 h2 => by
      rw [List.mem_singleton.mp hx] at h1 h2 ⊢
      subst h1 h2
      exact (hc h' hi).symm)
  have hrun : s = (Node.run cfg s₁ is₂).1 := by
    simp only [s, run_append, Node.run, s₁, s₀]
  rw [hrun]
  exact ⟨⟨hK₂.ledger, hK₂.own_le, hK₂.own_head, hK₂.own_dvd, hK₂.own_mem, hK₂.certified, by simp,
    hK₂.cert⟩,
    hcov₂,
    (hK₂.peers _ (List.mem_singleton_self _)).1⟩

end Node

end LeanDag
