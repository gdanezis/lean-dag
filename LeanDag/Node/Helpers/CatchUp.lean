import LeanDag.Node.Helpers.Replay
import LeanDag.Node.Helpers.SyncTrace
import LeanDag.Node.Helpers.Reliable
import LeanDag.Node.Helpers.Recover
import LeanDag.Node.Live.Statement
/-!
# Catch-up on a peer's proof

`docs/node-sync.md` D16. Along a trace, a node keeps what its proofs read
(`keeps_before`): every proof it keeps decides its slot again
(`proofsHold_before`), and it keeps a proof of every slot it decided
(`paired_before`). So a reliable node that asks for the proof of a slot,
once a reliable peer has decided it, is past that slot two message delays
later (`caught_up`): the peer replies with a kept proof, whose verdict is
the same at every node (`verdictOn_at`), and a step asks only for a proof
at or below its next undecided slot (`askProof_le_lo`). A node behind asks
for the proof of its next undecided slot at a timer within `askDelay`
(`asks_within`), so it moves up a slot once a reliable peer is past it
(`moves_up`), and is past every slot the peer decided within a bound per
slot between (`decides_behind`).
-/

namespace LeanDag

namespace Node

variable {Validator BlockId Payload : Type} [Fintype Validator] [DecidableEq Validator]
variable [LinearOrder BlockId]
variable {cfg : Config Validator BlockId Payload} {tr : Trace Validator BlockId Payload}

/-- **What a node knew lies under its hash.** -/
theorem knownBefore_hashed {i : ℕ} {v : Validator} {x : BlockId × Block Validator BlockId Payload}
    (hx : x ∈ Converge.knownBefore cfg tr i v) : x.1 = cfg.idOf x.2 := by
  simp only [Converge.knownBefore, Set.mem_setOf_eq, List.mem_append] at hx
  rcases hx with hx | hx
  · exact id_of_delivered (cfg := cfg.at v) hx
  · exact ((Converge.inv_before (cfg := cfg) (tr := tr) i v).good x hx).1

/-- **A node keeps what its proofs read** from an event to a later one, at
an injective hash. -/
theorem keeps_before (hσ : cfg.σ = boundedSel) (hid : Function.Injective cfg.idOf)
    (v : Validator) {i j : ℕ} (hij : i ≤ j) :
    KeepsProofs (cfg.at v) (stateBefore cfg tr i v) (stateBefore cfg tr j v) := by
  induction j, hij using Nat.le_induction with
  | base => exact KeepsProofs.refl _
  | succ j _ ih =>
    refine ih.trans ?_
    by_cases he : ∃ inp, tr[j]? = some (v, inp)
    · obtain ⟨inp, hj⟩ := he
      rw [Converge.step_before hj]
      exact KeepsProofs.step (cfg := cfg.at v) hσ hid (Converge.inv_before j v)
        (fun _ hx => knownBefore_hashed hx) inp
    · rw [Converge.same_before fun inp h => he ⟨inp, h⟩]
      exact KeepsProofs.refl _

theorem stateBefore_zero (v : Validator) : stateBefore cfg tr 0 v = State.init (cfg.at v) := by
  simp [stateBefore, inputsBefore, run]

/-- **Every proof a node keeps decides its slot again**, at an injective
hash. -/
theorem proofsHold_before (hσ : cfg.σ = boundedSel) (hid : Function.Injective cfg.idOf)
    (v : Validator) (i : ℕ) : ProofsHold (cfg.at v) (stateBefore cfg tr i v) :=
  (stateBefore_zero (cfg := cfg) (tr := tr) v ▸ ProofsHold.init).keeps
    (keeps_before hσ hid v (Nat.zero_le i))

/-- **A node keeps a proof of every slot it decided**, at an injective
hash. -/
theorem paired_before (hσ : cfg.σ = boundedSel) (hid : Function.Injective cfg.idOf)
    (v : Validator) (i : ℕ) :
    ∀ x ∈ (stateBefore cfg tr i v).decided, ∃ P, (x.1, P) ∈ (stateBefore cfg tr i v).proofs :=
  (keeps_before hσ hid v (Nat.zero_le i)).paired fun x hx => by
    rw [stateBefore_zero] at hx; simp [State.init] at hx

omit [Fintype Validator] in
/-- **A pass asks for no proof.** -/
theorem askProof_not_mem_advance (s : State Validator BlockId Payload) (k : ℕ) :
    Output.askProof k ∉ (Node.advance cfg s).2 := by
  obtain ⟨bs, hbs⟩ := progress_built (cfg := cfg) (s.disk.topRound + 2) s
  rw [advance_snd]
  simp only [Node.pass]
  intro h
  rcases List.mem_append.mp h with h | h
  · rcases List.mem_append.mp h with h | h
    · rw [hbs] at h; simp [built] at h
    · unfold Node.decideStep at h
      dsimp only at h
      split at h <;> simp at h
  · obtain ⟨_, -, -, -, he⟩ := mem_arm h
    cases he

omit [Fintype Validator] in
/-- **A settle asks for no proof.** -/
theorem askProof_not_mem_settle (s : State Validator BlockId Payload) (k : ℕ) :
    Output.askProof k ∉ (Node.settle cfg s).2 :=
  (quiesce_rel (cfg := cfg) (P := fun _ => True)
    (R := fun _ out _ => Output.askProof k ∉ out) (fun _ => List.not_mem_nil)
    (fun _ _ _ _ _ h₁ h₂ h => (List.mem_append.mp h).elim h₁ h₂)
    (fun s _ => ⟨askProof_not_mem_advance s k, trivial⟩) _ s trivial).1

/-- **A step asks for the proof of a slot at or below its next undecided
slot.** -/
theorem askProof_le_lo {s : State Validator BlockId Payload} {inp : Input Validator BlockId Payload}
    {k : ℕ} (h : Output.askProof k ∈ (Node.step cfg s inp).2) : k ≤ (Node.step cfg s inp).1.lo := by
  have hset := askProof_not_mem_settle (cfg := cfg) (k := k)
  -- a receipt asks only for blocks before settling
  have hrec : ∀ (p : State Validator BlockId Payload × List (Output Validator BlockId Payload)),
      (p = (s, []) ∨ ∃ s₁ pre, (∀ o ∈ pre, ∃ peer t fr ids, o = .sync peer t fr ids) ∧
        p = ((Node.settle cfg s₁).1, pre ++ (Node.settle cfg s₁).2)) →
      Output.askProof k ∉ p.2 := by
    rintro p (rfl | ⟨s₁, pre, hpre, rfl⟩) hk
    · exact List.not_mem_nil hk
    · rcases List.mem_append.mp hk with hk | hk
      · obtain ⟨_, _, _, _, he⟩ := hpre _ hk; cases he
      · exact hset s₁ hk
  cases inp with
  | start =>
    revert h
    simp only [Node.step]
    split
    · split
      · intro h
        rcases List.mem_append.mp h with h | h
        · simp at h
        · exact absurd h (hset _)
      · intro h; exact absurd h List.not_mem_nil
    · intro h; exact absurd h List.not_mem_nil
  | deliver u id b =>
    exact absurd h (hrec _ ((step_receipt_deliver s u id b).imp_right
      fun ⟨s₁, pre, _, hpre, he⟩ => ⟨s₁, pre, hpre, he⟩))
  | stream u L =>
    exact absurd h (hrec _ ((step_receipt_stream s u L).imp_right
      fun ⟨s₁, pre, _, hpre, he⟩ => ⟨s₁, pre, hpre, he⟩))
  | timer r =>
    rw [step_timer_fst]
    rcases step_timer_snd (cfg := cfg) s r with he | he <;> rw [he] at h <;>
      rcases List.mem_append.mp h with h | h
    · exact absurd h (hset _)
    · exact (Output.askProof.inj (mem_askBehind h)).le
    · exact absurd h (hset _)
    · rcases mem_resend h with ⟨_, _, _, _, he⟩ | ⟨_, _, -, -, he | he | he⟩ | he <;>
        first | exact (Output.askProof.inj he).le | cases he
  | syncRequest peer t fr ids =>
    simp only [Node.step] at h
    split at h <;> simp at h
  | ask peer r =>
    simp only [Node.step] at h
    split at h
    · simp at h
    · split at h <;> simp at h
  | restart =>
    simp only [Node.step] at h ⊢
    rcases List.mem_append.mp h with h | h
    · rcases List.mem_append.mp h with h | h
      · rcases mem_resend h with ⟨_, _, _, _, he⟩ | ⟨_, _, -, -, he | he | he⟩ | he
        · cases he
        · cases he
        · cases he
        · cases he
        · rw [Output.askProof.inj he]
          exact (rises_settle (cfg := cfg) { s with recovering := true }).2.2
      · unfold Node.rearm at h
        split at h
        · split at h <;> simp at h
        · simp at h
    · exact absurd h (hset _)
  | askProof peer k' =>
    simp only [Node.step] at h
    split at h
    · split at h <;> simp at h
    · simp at h
  | proof u k' L =>
    revert h
    simp only [Node.step]
    split
    · split
      · intro h
        rcases List.mem_cons.mp h with h | h
        · cases h
        rcases List.mem_append.mp h with h | h
        · exact absurd h (hset _)
        · rw [Output.askProof.inj (List.mem_singleton.mp h)]
      · intro h; exact absurd h List.not_mem_nil
    · intro h; exact absurd h List.not_mem_nil

/-- **A timer step asks for the proof of the next undecided slot**, at a
node that drops, unless the node's top then lies within a wave of that
slot's round and the step does not resend: its top changed, or the timer
is of neither its top round nor the one below. -/
theorem askProof_timer (hdr : cfg.drops = true) (s : State Validator BlockId Payload) (r : ℕ) :
    Output.askProof (Node.step cfg s (.timer r)).1.lo ∈ (Node.step cfg s (.timer r)).2 ∨
      ((Node.step cfg s (.timer r)).1.top.getD 0 ≤
          cfg.slots.slotRound (Node.step cfg s (.timer r)).1.lo + cfg.p.waveLength ∧
        ¬ ((Node.step cfg s (.timer r)).1.top = s.top ∧
          (s.top = some r ∨ s.top = some (r + 1)))) := by
  set res := Node.settle cfg { s with fired := fire s r, recovering := false } with hres
  have hst : Node.step cfg s (.timer r) =
      if res.1.top = s.top ∧ (s.top = some r ∨ s.top = some (r + 1)) then
        (res.1, res.2 ++ Node.resend cfg res.1)
      else (res.1, res.2 ++ Node.askBehind cfg res.1) := rfl
  rw [hst]
  by_cases h : res.1.top = s.top ∧ (s.top = some r ∨ s.top = some (r + 1))
  · rw [if_pos h]
    exact Or.inl (List.mem_append_right _ (by simp [Node.resend, hdr]))
  · rw [if_neg h]
    by_cases hl : cfg.slots.slotRound res.1.lo + cfg.p.waveLength < res.1.top.getD 0
    · refine Or.inl (List.mem_append_right _ ?_)
      unfold Node.askBehind
      rw [if_pos ⟨hdr, hl⟩]
      exact List.mem_singleton_self _
    · exact Or.inr ⟨by dsimp only; omega, h⟩

/-- **A reliable node catches up on a reliable peer's proof** (D16): when
a reliable node `u` asks for the proof of a slot `k`, and a reliable peer
`v` has decided `k` by then, `u` is past `k` within two message delays
past GST, at an injective hash and authentic evidence, at a node that
drops. -/
theorem caught_up (hσ : cfg.σ = boundedSel) (hw : 2 ≤ cfg.p.waveLength)
    (hl : 1 ≤ cfg.p.linkSize) (hcm : 1 ≤ cfg.p.commitThreshold)
    (hc : cfg.p.voteIsCert = false → 1 ≤ cfg.p.certThreshold)
    (hid : Function.Injective cfg.idOf) (hdr : cfg.drops = true)
    {H T : Finset Validator} (htime : Converge.TimelyAuthentic cfg H tr)
    (hev : Converge.EvidenceAuthentic cfg H tr) (hTH : T ⊆ H) {time : ℕ → ℕ} {gst Δ t₁ : ℕ}
    (hdel : Live.DeliveredWithin cfg T tr time gst Δ t₁)
    {u v : Validator} (hu : u ∈ T) (hv : v ∈ T) (hvu : v ≠ u) {i k : ℕ}
    {inp : Input Validator BlockId Payload} (hi : tr[i]? = some (u, inp))
    (hask : Output.askProof k ∈ outputsAt cfg tr i)
    {d : Option BlockId} (hvk : (k, d) ∈ (stateBefore cfg tr i v).decided)
    (ht : max (time i) gst + 2 * Δ ≤ t₁) :
    ∃ j, i < j ∧ j < tr.length ∧ time j ≤ max (time i) gst + 2 * Δ ∧
      k < (stateBefore cfg tr (j + 1) u).lo := by
  have hk : k ≤ (stateBefore cfg tr (i + 1) u).lo := by
    rw [outputsAt_eq hi] at hask
    rw [Converge.step_before hi]
    exact askProof_le_lo hask
  -- the request reaches `v`, which keeps a proof of `k`
  obtain ⟨j₁, hij₁, hj₁, ht₁⟩ := hdel i u inp hi hu (v, .askProof u k) ⟨_, hask, hvu, rfl⟩ hv
    (by omega)
  have hkv := (keeps_before hσ hid v hij₁.le).decided _ hvk
  obtain ⟨P, hP⟩ := paired_before hσ hid v j₁ _ hkv
  obtain ⟨L, hL⟩ : ∃ L, proofReply (cfg.at v) (stateBefore cfg tr j₁ v) k = some L := by
    unfold proofReply
    obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp
      (List.find?_isSome.mpr ⟨_, hP, by simp⟩ :
        ((stateBefore cfg tr j₁ v).proofs.find? fun p => p.1 = k).isSome)
    rw [hp]; exact ⟨_, rfl⟩
  obtain ⟨d', -, hv'⟩ := verdictOn_reply (cfg := cfg.at v) hσ hw hl hcm hc
    (proofsHold_before hσ hid v j₁)
    (fun x hx => knownBefore_hashed ((Converge.inv_before j₁ v).known x hx)) hL
  -- `v` replies with it
  have hrep : Output.proof u k L ∈ outputsAt cfg tr j₁ := by
    have hnd := Converge.not_detected htime hev (hTH hu) (hTH hv) j₁
    have hdr' : (cfg.at v).drops = true := hdr
    rw [outputsAt_eq hj₁]
    simp only [Node.step]
    rw [if_pos ⟨hdr', hnd⟩, hL]
    exact List.mem_singleton_self _
  -- the reply reaches `u`, which decides `k` on it unless past `k`
  have hmax : max (time j₁) gst ≤ max (time i) gst + Δ :=
    max_le ht₁ ((le_max_right _ _).trans (Nat.le_add_right _ _))
  obtain ⟨j₂, hj₁j₂, hj₂, ht₂⟩ :=
    hdel j₁ v _ hj₁ hv (u, .proof v k L) ⟨_, hrep, rfl, rfl⟩ hu (by omega)
  refine ⟨j₂, by omega, (List.getElem?_eq_some_iff.mp hj₂).1, by omega, ?_⟩
  have hlo : k ≤ (stateBefore cfg tr j₂ u).lo :=
    hk.trans (rises_before (cfg := cfg) u (show i + 1 ≤ j₂ by omega)).2.2
  rw [Converge.step_before hj₂]
  by_cases hk' : k = (stateBefore cfg tr j₂ u).lo
  · have hnd := Converge.not_detected htime hev (hTH hv) (hTH hu) j₂
    have hvu' : verdictOn (cfg.at u) k L = some d' := verdictOn_at hσ hw hl hcm hc hv'
    have hdec : (Node.step (cfg.at u) (stateBefore cfg tr j₂ u) (.proof v k L)).1 =
        (Node.settle (cfg.at u)
          (tidy (decideOn (cfg.at u) (stateBefore cfg tr j₂ u) k d' L))).1 := by
      simp only [Node.step]
      rw [if_pos ⟨(hdr : (cfg.at u).drops = true), hnd, hk'⟩]
      simp only [hvu']
    rw [hdec]
    have h₁ := (rises_settle (cfg := cfg.at u)
      (tidy (decideOn (cfg.at u) (stateBefore cfg tr j₂ u) k d' L))).2.2
    have h₂ := (decideOn_rest (cfg := cfg.at u) (stateBefore cfg tr j₂ u) k d' L).2.2.2.2.1
    rw [(tidy_eq _).2.2.2.2.2.1, h₂] at h₁
    omega
  · exact lt_of_lt_of_le (lt_of_le_of_ne hlo hk') (rises_step (cfg := cfg.at u)).2.2

/-! ## Asking when behind -/

section Asking

variable {T : Finset Validator} {time : ℕ → ℕ} {t_r t₁ : ℕ}

/-- **A node's kept decisions are the slots below its next undecided
one.** -/
theorem ledger_before (v : Validator) (i : ℕ) : Ledger (stateBefore cfg tr i v) :=
  (run_appends (cfg := cfg.at v) (inputsBefore tr i v) Ledger.init).2

variable (cfg) in
/-- **The delay of a request for a proof**, from round `n` with the next
undecided slot at most `k`: twice the timeout of the round below each
round from `n` to a wave above the round of slot `k`. -/
def askDelay (k n : ℕ) : ℕ :=
  ∑ r ∈ Finset.Icc n (max n (cfg.slots.slotRound k + cfg.p.waveLength)), 2 * cfg.timeout (r - 1)

theorem two_timeout_le_askDelay (k n : ℕ) : 2 * cfg.timeout (n - 1) ≤ askDelay cfg k n :=
  Finset.single_le_sum (f := fun r => 2 * cfg.timeout (r - 1)) (fun _ _ => Nat.zero_le _)
    (Finset.mem_Icc.mpr ⟨le_rfl, le_max_left _ _⟩)

theorem askDelay_step {k n n' : ℕ} (h : n < n')
    (h' : n' ≤ cfg.slots.slotRound k + cfg.p.waveLength) :
    2 * cfg.timeout (n - 1) + askDelay cfg k n' ≤ askDelay cfg k n := by
  unfold askDelay
  rw [max_eq_right h', max_eq_right (show n ≤ _ by omega),
    Finset.Icc_eq_cons_Ioc (show n ≤ _ by omega),
    Finset.sum_cons]
  exact Nat.add_le_add_left (Finset.sum_le_sum_of_subset fun x hx => by
    simp only [Finset.mem_Icc, Finset.mem_Ioc] at hx ⊢; omega) _

/-- **A reliable node behind asks for a proof**, at a node that drops: from
event `E` on, at round `n` with its next undecided slot at most `k`, a
reliable node that does not restart asks at a timer for the proof of its
next undecided slot, or is past `k`, within `askDelay k n` of the events
before `E`. The retry timer of its round fires (`retry_fires`) and asks
(`askProof_timer`), unless the node built above its round within a wave of
its next undecided slot's round; then the retry timer of the round it
built does, within the next term of the delay. -/
theorem asks_within (hmono : Live.TimeMono tr time) (hup : Live.UpFrom T tr time t_r t₁)
    (hfire : Live.TimersFireUp cfg T tr time t₁) (hdr : cfg.drops = true) {u : Validator}
    (hu : u ∈ T) (k : ℕ) {E n τ : ℕ} (hts : (stateBefore cfg tr E u).top = some n)
    (hlo : (stateBefore cfg tr E u).lo ≤ k) (hrE : ∀ j, E ≤ j → j < tr.length → t_r ≤ time j)
    (hτ : ∀ a < E, a < tr.length → time a ≤ τ) (ht₁ : τ + askDelay cfg k n ≤ t₁) :
    ∃ g, E ≤ g ∧ time g ≤ τ + askDelay cfg k n ∧ (tr[g]?.map Prod.fst) = some u ∧
      (k < (stateBefore cfg tr (g + 1) u).lo ∨
        Output.askProof (stateBefore cfg tr (g + 1) u).lo ∈ outputsAt cfg tr g) := by
  set R := cfg.slots.slotRound k + cfg.p.waveLength with hR
  induction hm : R + 1 - n using Nat.strong_induction_on generalizing E n τ with
  | _ m ih =>
  obtain ⟨a, f, haE, hEf, hf, htf⟩ := retry_fires hup hfire hu hts hrE
    (fun a ha hal => by
      have := hτ a ha hal; have := two_timeout_le_askDelay (cfg := cfg) k n; omega)
  have hfl : f < tr.length := (List.getElem?_eq_some_iff.mp hf).1
  have hal : a < tr.length := by omega
  have hta := hτ a haE hal
  have h2t := two_timeout_le_askDelay (cfg := cfg) k n
  have hfu : (tr[f]?.map Prod.fst) = some u := by rw [hf]; rfl
  have hstep := askProof_timer (cfg := cfg.at u) hdr (stateBefore cfg tr f u) (n - 1)
  rw [← Converge.step_before hf, ← outputsAt_eq hf] at hstep
  rcases hstep with hask | ⟨hlag, hne⟩
  · exact ⟨f, hEf, by omega, hfu, Or.inr hask⟩
  by_cases hk : k < (stateBefore cfg tr (f + 1) u).lo
  · exact ⟨f, hEf, by omega, hfu, Or.inl hk⟩
  -- the node built above `n`, within a wave of its next undecided slot's round
  obtain ⟨h₁, h₂, -⟩ := rises_before (cfg := cfg) (tr := tr) u hEf
  obtain ⟨h₃, h₄, -⟩ := rises_before (cfg := cfg) (tr := tr) u (Nat.le_succ f)
  rw [hts] at h₁ h₂
  obtain ⟨n₀, hn₀⟩ := Option.isSome_iff_exists.mp (h₂ rfl)
  obtain ⟨n', hn'⟩ := Option.isSome_iff_exists.mp (h₄ (h₂ rfl))
  rw [hn₀] at h₁ h₃
  rw [hn'] at h₃ hlag
  simp only [Option.getD_some] at h₁ h₃ hlag
  have hnn' : n < n' := by
    by_contra hle
    have hfn : (stateBefore cfg tr f u).top = some n := by rw [hn₀]; congr 1; omega
    have hf'n : (stateBefore cfg tr (f + 1) u).top = some n := by rw [hn']; congr 1; omega
    refine hne ⟨hf'n.trans hfn.symm, ?_⟩
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · left; rw [hfn, h0]
    · right; rw [hfn, Nat.sub_add_cancel hpos]
  have hlag' : n' ≤ cfg.slots.slotRound (stateBefore cfg tr (f + 1) u).lo + cfg.p.waveLength :=
    hlag
  have hn'R : n' ≤ R := hlag'.trans (Nat.add_le_add_right
    (cfg.slots.mono (show (stateBefore cfg tr (f + 1) u).lo ≤ k by omega)) _)
  have hstepd := askDelay_step (cfg := cfg) hnn' hn'R
  have hlo' : (stateBefore cfg tr (f + 1) u).lo ≤ k := by omega
  obtain ⟨g, hfg, htg, hgu, hres⟩ := ih (R + 1 - n') (by omega) hn' hlo'
    (fun j hj hjl => hrE j (by omega) hjl) (fun a' ha' _ => hmono a' f (by omega) hfl)
    (by omega) rfl
  exact ⟨g, by omega, by omega, hgu, hres⟩

/-- **A reliable node behind moves up a slot**, at a node that drops: from
event `E` on, at round `n` with its next undecided slot at most `k`, once
a reliable peer is past `k`, the node's next undecided slot rises within
`askDelay k n` of the events before `E` and two message delays past GST,
if no reliable node restarts. The node asks for the proof of its next
undecided slot (`asks_within`), which the peer has decided
(`caught_up`). -/
theorem moves_up (hσ : cfg.σ = boundedSel) (hw : 2 ≤ cfg.p.waveLength)
    (hl : 1 ≤ cfg.p.linkSize) (hcm : 1 ≤ cfg.p.commitThreshold)
    (hc : cfg.p.voteIsCert = false → 1 ≤ cfg.p.certThreshold)
    (hid : Function.Injective cfg.idOf) (hdr : cfg.drops = true)
    {H : Finset Validator} (htime : Converge.TimelyAuthentic cfg H tr)
    (hev : Converge.EvidenceAuthentic cfg H tr) (hTH : T ⊆ H) {gst Δ : ℕ}
    (hmono : Live.TimeMono tr time) (hdel : Live.DeliveredWithin cfg T tr time gst Δ t₁)
    (hup : Live.UpFrom T tr time 0 t₁) (hfire : Live.TimersFireUp cfg T tr time t₁)
    {u v : Validator} (hu : u ∈ T) (hv : v ∈ T) (hvu : v ≠ u) {E n τ k : ℕ}
    (hts : (stateBefore cfg tr E u).top = some n) (hlo : (stateBefore cfg tr E u).lo ≤ k)
    (hvk : k < (stateBefore cfg tr E v).lo) (hτ : ∀ a < E, a < tr.length → time a ≤ τ)
    (ht₁ : max (τ + askDelay cfg k n) gst + 2 * Δ ≤ t₁) :
    ∃ j, E ≤ j ∧ j < tr.length ∧ time j ≤ max (τ + askDelay cfg k n) gst + 2 * Δ ∧
      (stateBefore cfg tr E u).lo < (stateBefore cfg tr (j + 1) u).lo := by
  obtain ⟨g, hEg, htg, hgu, hres⟩ := asks_within hmono hup hfire hdr hu k hts hlo
    (fun _ _ _ => Nat.zero_le _) hτ (by omega)
  have hg₁ := (rises_before (cfg := cfg) (tr := tr) u (show E ≤ g + 1 by omega)).2.2
  have hmax : max (time g) gst ≤ max (τ + askDelay cfg k n) gst := max_le_max htg le_rfl
  obtain ⟨inp, hg⟩ := Converge.event_of_map hgu
  have hgl : g < tr.length := (List.getElem?_eq_some_iff.mp hg).1
  by_cases hk : k < (stateBefore cfg tr (g + 1) u).lo
  · exact ⟨g, hEg, hgl, by omega, by omega⟩
  have hask := hres.resolve_left hk
  have hvg := (rises_before (cfg := cfg) (tr := tr) v hEg).2.2
  obtain ⟨d, hd⟩ := (ledger_before (cfg := cfg) (tr := tr) v g).mem
    (k := (stateBefore cfg tr (g + 1) u).lo) (by omega)
  obtain ⟨j, hgj, hjl, htj, hj⟩ := caught_up hσ hw hl hcm hc hid hdr htime hev hTH hdel hu hv
    hvu hg hask hd (by omega)
  exact ⟨j, by omega, hjl, by omega, by omega⟩

/-- The events before `E` lie at or before `t` exactly when `E` is at most
the number of events by `t`. -/
theorem le_eventsBy (hmono : Live.TimeMono tr time) {E t : ℕ} (hE : E ≤ tr.length)
    (hτ : ∀ a < E, a < tr.length → time a ≤ t) : E ≤ eventsBy tr time t := by
  rcases Nat.eq_zero_or_pos E with rfl | hpos
  · exact Nat.zero_le _
  · have := (lt_eventsBy hmono (show E - 1 < tr.length by omega)).mpr
      (hτ _ (by omega) (by omega))
    omega

/-- **The delay of a request for a proof is at most the retry delays of
the rounds up to `M`**, for `M` at or above the node's round and a wave
above the round of slot `k`. -/
theorem askDelay_le {k n M : ℕ} (hn : n ≤ M) (hk : cfg.slots.slotRound k + cfg.p.waveLength ≤ M) :
    askDelay cfg k n ≤ ∑ r ∈ Finset.range (M + 1), 2 * cfg.timeout (r - 1) := by
  have := max_le hn hk
  exact Finset.sum_le_sum_of_subset fun x hx => by
    simp only [Finset.mem_Icc, Finset.mem_range] at hx ⊢; omega

/-- **A reliable node behind decides the slots a reliable peer has
decided** (catch-up), at a node that drops: from event `E` on, once a
reliable peer is past slot `k`, a reliable node that has started is past
`k` by `max τ gst + g (D + 2Δ)`, for `τ` a time at or after the events
before `E`, `g` the slots from its next undecided one to `k`, and `D` the
retry delays of the rounds up to `M`, if no reliable node restarts and its
round stays at or below `M`, with `M` a wave above the round of slot `k`
or more. Each slot takes a request and a reply (`moves_up`). -/
theorem decides_behind (hσ : cfg.σ = boundedSel) (hw : 2 ≤ cfg.p.waveLength)
    (hl : 1 ≤ cfg.p.linkSize) (hcm : 1 ≤ cfg.p.commitThreshold)
    (hc : cfg.p.voteIsCert = false → 1 ≤ cfg.p.certThreshold)
    (hid : Function.Injective cfg.idOf) (hdr : cfg.drops = true)
    {H : Finset Validator} (htime : Converge.TimelyAuthentic cfg H tr)
    (hev : Converge.EvidenceAuthentic cfg H tr) (hTH : T ⊆ H) {gst Δ : ℕ}
    (hmono : Live.TimeMono tr time) (hdel : Live.DeliveredWithin cfg T tr time gst Δ t₁)
    (hup : Live.UpFrom T tr time 0 t₁) (hfire : Live.TimersFireUp cfg T tr time t₁)
    {u v : Validator} (hu : u ∈ T) (hv : v ∈ T) (hvu : v ≠ u) {k M : ℕ}
    (hkM : cfg.slots.slotRound k + cfg.p.waveLength ≤ M) :
    ∀ {E τ : ℕ}, E ≤ tr.length → (stateBefore cfg tr E u).top.isSome →
      k < (stateBefore cfg tr E v).lo → (∀ a < E, a < tr.length → time a ≤ τ) →
      (stateAt cfg tr time u (max τ gst + (k + 1 - (stateBefore cfg tr E u).lo) *
        ((∑ r ∈ Finset.range (M + 1), 2 * cfg.timeout (r - 1)) + 2 * Δ))).top.getD 0 ≤ M →
      max τ gst + (k + 1 - (stateBefore cfg tr E u).lo) *
        ((∑ r ∈ Finset.range (M + 1), 2 * cfg.timeout (r - 1)) + 2 * Δ) ≤ t₁ →
      k < (stateAt cfg tr time u (max τ gst + (k + 1 - (stateBefore cfg tr E u).lo) *
        ((∑ r ∈ Finset.range (M + 1), 2 * cfg.timeout (r - 1)) + 2 * Δ))).lo := by
  set D := (∑ r ∈ Finset.range (M + 1), 2 * cfg.timeout (r - 1)) + 2 * Δ with hD
  intro E τ hE hts hvk hτ hM ht₁
  induction hg : k + 1 - (stateBefore cfg tr E u).lo using Nat.strong_induction_on
    generalizing E τ with
  | _ g ih =>
  rw [hg] at hM ht₁
  have hEB : E ≤ eventsBy tr time (max τ gst + g * D) := le_eventsBy hmono hE
    (fun a ha hal => (hτ a ha hal).trans ((le_max_left τ gst).trans (Nat.le_add_right _ _)))
  have hrE := rises_before (cfg := cfg) (tr := tr) u hEB
  by_cases hk : k < (stateBefore cfg tr E u).lo
  · exact lt_of_lt_of_le hk hrE.2.2
  obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp hts
  have hnM : n ≤ M := by
    have := hrE.1; rw [hn] at this; simp only [Option.getD_some] at this
    exact this.trans hM
  have hask := askDelay_le (cfg := cfg) (k := k) hnM hkM
  have hg1 : 1 ≤ g := by omega
  have hgD : D ≤ g * D := Nat.le_mul_of_pos_left D hg1
  obtain ⟨j, hEj, hjl, htj, hj⟩ := moves_up hσ hw hl hcm hc hid hdr htime hev hTH hmono hdel
    hup hfire hu hv hvu hn (by omega) hvk hτ (by
      have : max (τ + askDelay cfg k n) gst ≤ max τ gst + askDelay cfg k n := max_le
        (Nat.add_le_add_right (le_max_left _ _) _) ((le_max_right _ _).trans (Nat.le_add_right _ _))
      omega)
  have htj' : time j ≤ max τ gst + D := by
    have : max (τ + askDelay cfg k n) gst ≤ max τ gst + askDelay cfg k n := max_le
      (Nat.add_le_add_right (le_max_left _ _) _) ((le_max_right _ _).trans (Nat.le_add_right _ _))
    omega
  have hj1 : j + 1 ≤ eventsBy tr time (max τ gst + g * D) :=
    (lt_eventsBy hmono hjl).mpr (by omega)
  by_cases hkj : k < (stateBefore cfg tr (j + 1) u).lo
  · exact lt_of_lt_of_le hkj (rises_before (cfg := cfg) (tr := tr) u hj1).2.2
  -- the next slot, from the event after `j`
  set g' := k + 1 - (stateBefore cfg tr (j + 1) u).lo with hg'
  have hgg : g' < g := by omega
  have hB : max (time j) gst + g' * D ≤ max τ gst + g * D := by
    have : g' * D + D ≤ g * D := by
      have := Nat.mul_le_mul_right D (show g' + 1 ≤ g by omega)
      rwa [Nat.add_mul, one_mul] at this
    have : max (time j) gst ≤ max τ gst + D := max_le htj' ((le_max_right _ _).trans
      (Nat.le_add_right _ _))
    omega
  have hmonoB := eventsBy_mono (tr := tr) (time := time) hB
  have hrB := rises_before (cfg := cfg) (tr := tr) u hmonoB
  have hr₁ := rises_before (cfg := cfg) (tr := tr) u (show E ≤ j + 1 by omega)
  have := ih g' hgg (E := j + 1) (τ := time j) hjl (hr₁.2.1 hts)
    (lt_of_lt_of_le hvk (rises_before (cfg := cfg) (tr := tr) v (show E ≤ j + 1 by omega)).2.2)
    (fun a ha _ => hmono a j (by omega) hjl) (hrB.1.trans hM) (hB.trans ht₁) hg'.symm
  exact lt_of_lt_of_le this hrB.2.2

end Asking

end Node

end LeanDag
