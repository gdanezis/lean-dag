import LeanDag.Node.Helpers.Replay
import LeanDag.Node.Helpers.SyncTrace
import LeanDag.Node.Helpers.Reliable
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
at or below its next undecided slot (`askProof_le_lo`).
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
    ∃ j, i < j ∧ time j ≤ max (time i) gst + 2 * Δ ∧ k < (stateBefore cfg tr (j + 1) u).lo := by
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
  refine ⟨j₂, by omega, by omega, ?_⟩
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

end Node

end LeanDag
