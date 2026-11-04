import LeanDag.Node.Helpers.Grow
import LeanDag.Node.Helpers.SyncSteps
/-!
# The cut a request carries

A step raises the floor (`diskRises_step`), so it raises the node's cut
(`cutOf_mono`), and every request a step sends carries the frontier of the
node at some point of the step, which lies at or above the node's cut
before the step (`step_sync_cut`, D15).
-/

namespace LeanDag

namespace Node

variable {Validator BlockId Payload : Type} [Fintype Validator] [DecidableEq Validator]
variable [LinearOrder BlockId]
variable {cfg : Config Validator BlockId Payload}

omit [Fintype Validator] in
/-- **The cut rises with the floor.** -/
theorem cutOf_mono {s s' : State Validator BlockId Payload} (h : s.floor ≤ s'.floor) :
    cutOf cfg s ≤ cutOf cfg s' := by
  unfold cutOf; split <;> omega

omit [Fintype Validator] in
/-- **A request in a resend carries the node's frontier.** -/
theorem resend_frontier {s : State Validator BlockId Payload} {peer : Validator} {i : BlockId}
    {fr : Validator → ℕ} {ids : List BlockId} (h : Output.sync peer i fr ids ∈ resend cfg s) :
    fr = frontierOf cfg s := by
  unfold resend at h
  rcases List.mem_append.mp h with h | h
  · rcases List.mem_append.mp h with h | h
    · split at h <;> simp at h
    · unfold resync at h
      obtain ⟨e, -, heq⟩ := List.mem_map.mp h
      simp only [request, Output.sync.injEq] at heq
      exact heq.2.2.1.symm
  · split at h <;> simp at h

/-- **A request a step sends carries a frontier at or above the node's cut
before the step** (D15). -/
theorem step_sync_cut (s : State Validator BlockId Payload) (inp : Input Validator BlockId Payload)
    {peer : Validator} {i : BlockId} {fr : Validator → ℕ} {ids : List BlockId}
    (h : Output.sync peer i fr ids ∈ (Node.step cfg s inp).2) (a : Validator) :
    cutOf cfg s ≤ fr a := by
  have hset : ∀ x : State Validator BlockId Payload,
      Output.sync peer i fr ids ∉ (Node.settle cfg x).2 := fun x hx =>
    noAsk_settle x _ hx peer i fr ids rfl
  have hfr : ∀ x : State Validator BlockId Payload, s.floor ≤ x.floor → fr = frontierOf cfg x →
      cutOf cfg s ≤ fr a := fun x hx hf => by
    rw [hf]; exact (cutOf_mono hx).trans (le_max_left _ _)
  cases inp with
  | start =>
    rw [step_start_eq] at h
    split_ifs at h
    · rcases List.mem_append.mp h with h | h
      · simp at h
      · exact absurd h (hset _)
    · simp at h
    · simp at h
  | deliver u id b =>
    rw [step_deliver_eq] at h
    split_ifs at h
    · exact absurd h (hset _)
    · rcases List.mem_cons.mp h with h | h
      · simp only [request, Output.sync.injEq] at h
        exact hfr _ le_rfl h.2.2.1
      · exact absurd h (hset _)
    · simp at h
    · simp at h
  | stream u L =>
    cases hf : s.syncs.find? fun e => decide (e.1 = u) with
    | none => simp [Node.step, hf] at h
    | some e =>
      rw [step_stream_eq s u L hf] at h
      split at h
      · exact absurd h (hset _)
      · dsimp only at h
        rcases List.mem_append.mp h with h | h
        · split at h
          · simp only [List.mem_singleton, request, Output.sync.injEq] at h
            refine hfr _ ?_ h.2.2.1
            change s.floor ≤ (takeIn cfg s e.2.1 (inHistory cfg e.2.1 L)).floor
            unfold takeIn
            split
            · exact (absorb_rest (cfg := cfg) s _).1.ge
            · exact le_rfl
          · simp at h
        · exact absurd h (hset _)
  | timer r =>
    rcases step_timer_snd (cfg := cfg) s r with h' | h' <;> rw [h'] at h <;>
      rcases List.mem_append.mp h with h | h
    · exact absurd h (hset _)
    · cases mem_askBehind h
    · exact absurd h (hset _)
    · exact hfr _ (diskRises_settle (cfg := cfg)
        { s with fired := fire s r, recovering := false }).1.1 (resend_frontier h)
  | syncRequest peer t fr ids =>
    simp only [Node.step] at h
    split at h <;> simp at h
  | ask peer r =>
    simp only [Node.step] at h
    split at h <;> (try split at h) <;> simp at h
  | restart =>
    change Output.sync peer i fr ids ∈
      resend cfg s ++ rearm cfg s ++ (Node.settle cfg { s with recovering := true }).2 at h
    rcases List.mem_append.mp h with h | h
    · rcases List.mem_append.mp h with h | h
      · exact hfr s le_rfl (resend_frontier h)
      · obtain ⟨r, -, -, h⟩ := mem_rearm h; cases h
    · exact absurd h (hset _)
  | askProof peer k =>
    simp only [Node.step] at h
    split at h <;> (try split at h) <;> simp at h
  | proof u k L =>
    simp only [Node.step] at h
    split at h
    · split at h
      · rcases List.mem_cons.mp h with h | h
        · cases h
        · rcases List.mem_append.mp h with h | h
          · exact absurd h (hset _)
          · simp at h
      · simp at h
    · simp at h

end Node

end LeanDag
