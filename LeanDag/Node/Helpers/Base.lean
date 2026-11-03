import LeanDag.Node.Helpers.CutAbove
import LeanDag.Node.Model.Timed
/-!
# The base the wave argument reads

`docs/dos-bounds.md` Phase 3.2 item 4.3. The argument of V11 reads the
honest disks over a stretch of events from `t₀` to `t₁`, from a round `B`
up (`Base`): there each is read as a record `R` reads it from `B` up
(`CutAbove`), is valid at the row above `B`, and only grows; each honest
node's floor lies at or below its top, and its steps are regular
(`Regular`). Without
dropping the record of the run is such a base from round `0`, over the
whole run (`base_of_false`).
-/

namespace LeanDag

namespace Node

variable {Validator BlockId Payload : Type} [Fintype Validator] [DecidableEq Validator]
variable [LinearOrder BlockId]

variable (cfg : Config Validator BlockId Payload) (H : Finset Validator)
  (tr : Trace Validator BlockId Payload) (time : ℕ → ℕ) in
/-- **A base for the wave argument**: at every event from `t₀` to `t₁`,
every honest disk is read as the record `R` reads it from round `B` up, is
valid at the row above `B`, and grows to every later such event; the
node's floor lies at or below its top, and its step there, if the next
event is still in the stretch, is regular. -/
def Base (R : BlockRecord Validator BlockId Payload (ValidAt cfg.q Clause.none) H)
    (B t₀ t₁ : ℕ) : Prop :=
  ∀ v ∈ H, ∀ k, eventsBy tr time t₀ ≤ k → k ≤ eventsBy tr time t₁ →
    AllGood (CutAbove R B) (stateBefore cfg tr k v).disk ∧
      UpperValid cfg.q cfg.xp (B + 1) (stateBefore cfg tr k v).disk ∧
      (∀ k', k ≤ k' → k' ≤ eventsBy tr time t₁ →
        Grows (stateBefore cfg tr k v).disk (stateBefore cfg tr k' v).disk) ∧
      (stateBefore cfg tr k v).floor ≤ (stateBefore cfg tr k v).top.getD 0 ∧
      (k + 1 ≤ eventsBy tr time t₁ →
        Regular (cfg.at v) (stateBefore cfg tr k v) (stateBefore cfg tr (k + 1) v))

variable {cfg : Config Validator BlockId Payload} {H : Finset Validator}
  {tr : Trace Validator BlockId Payload}

/-- **Without dropping, the record of the run is a base from round `0`**,
over every stretch: every honest disk is a cut of it (`cut_before`), valid,
and grows (`grows_before`), its floor `voteOffset` below its top at most. -/
theorem base_of_false (hσ : cfg.σ = boundedSel) (hadm : cfg.Admissible) (hf : Hᶜ.card ≤ cfg.f)
    (htime : Converge.TimelyAuthentic cfg H tr) (hinj : Converge.HashInjective cfg H tr)
    (hdr : cfg.drops = false) (time : ℕ → ℕ) (t₀ t₁ : ℕ) :
    Base cfg H tr time (globalRecord (hashInjective_of_trace hinj) (authentic_of_timely htime))
      0 t₀ t₁ := by
  intro v hv k _ _
  refine ⟨fun j hj _ => ?_,
    fun j hj _ => (Converge.inv_before (cfg := cfg) (tr := tr) k v).valid hdr j hj,
    fun _ hk _ => grows_before (cfg := cfg) (tr := tr) v hdr hk,
    (Converge.inv_before (cfg := cfg) (tr := tr) k v).floor.trans
      ((floorOf_le_top (cfg := cfg.at v) hdr _).trans (Nat.sub_le _ _)),
    fun _ => Regular.of_false hdr⟩
  obtain ⟨hU, heq⟩ := (cut_before hσ hadm hf htime hinj hdr k v hv).1 j hj
  exact ⟨hU, by rw [heq], by rw [heq], fun _ => heq⟩

end Node

end LeanDag
