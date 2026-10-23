import LeanDag.Node.Refines.Statement
import LeanDag.Node.Live.Proof
import LeanDag.Node.Local.Proof
/-!
# The node refines the scheme — proof

`docs/validator.md` §5, V12. The record is the run's (`globalRecord`).
Its holdings and the verdicts on it are `cut_before`, the loop is
`commitInv_before`, and the self-parents are `selfParent_of_honest`.

Over a timed trace, delivery and synchronisation make blocks arrive
within `A` (`arrival_of_delivered`; with crashes, `arrival_of_recovered`
from `max t_r gst + W`), which gives the wave facts (`waveFacts_of_run`)
and, on a reliable node's view, a leader block decided for each slot of a
reliably led run (`run_commits`). By `Live.decides` the node has output a
decision for each such slot; that decision is a verdict on some view of
the record (`cut_before`), so by the uniqueness of verdicts
(`AnchoredRule.decided_unique`) it is the leader block. The leader block
is honest, so it reaches its author's lower blocks (`own_reaches_record`).
-/

namespace LeanDag

namespace Node

namespace Refines

variable {Validator BlockId Payload : Type} [Fintype Validator] [DecidableEq Validator]
variable [LinearOrder BlockId]

/-- **Arrival within `A` from `G` gives the wave facts and the
leaders.** -/
theorem waves_leads {cfg : Config Validator BlockId Payload} {H T : Finset Validator}
    {tr : Trace Validator BlockId Payload} {time : ℕ → ℕ} {G Δ Δₛ t₁ : ℕ}
    (hσ : cfg.σ = boundedSel) (hadm : cfg.Admissible)
    (hf : Hᶜ.card ≤ cfg.f) (hTH : T ⊆ H) (hqT : cfg.q ≤ T.card)
    (hcT : Fintype.card Validator - cfg.f - cfg.c ≤ T.card) (hq : 2 ≤ cfg.q)
    (hid : Function.Injective cfg.idOf) (hto : ∀ r, 2 * (Δ + Δₛ) < cfg.timeout r)
    (htime : Converge.TimelyAuthentic cfg H tr) (hinj : Converge.HashInjective cfg H tr)
    (hmono : Live.TimeMono tr time) (harr : Arrival cfg T tr time G (Δ + Δₛ) t₁)
    (hwait : Live.TimersAfterSet cfg H tr time) (hstart : Live.StartedBy T tr time G) :
    Waves cfg T tr time G (Δ + Δₛ) t₁
        (globalRecord (hashInjective_of_trace hinj) (authentic_of_timely htime)) ∧
      Leads cfg T tr time G (Δ + Δₛ) t₁
        (globalRecord (hashInjective_of_trace hinj) (authentic_of_timely htime)) := by
  letI := cfg.slots
  refine ⟨fun n₀ N t hbelow hgt htop ht₁ => ?_,
    fun b c n₀ hc hspan hlead hn₀ hbelow t htop ht₁ v hv j hbj hjc => ?_⟩
  · exact waveFacts_of_run hσ hadm hf htime hinj hTH hmono harr hq hto hwait hid hstart hcT
      hbelow (fun w hw => started_at hadm hid htime hTH hmono hstart hw hgt) htop ht₁
  set U := globalRecord (hashInjective_of_trace hinj) (authentic_of_timely htime) with hU
  -- on the node's view the slot commits a leader block
  obtain ⟨V, -, -, hcm⟩ := run_commits hσ hadm hf hTH hqT hcT hq hid hto htime hinj hmono harr
    hwait hstart hc hspan hlead hn₀ hbelow htop ht₁ hv
  obtain ⟨L, hL, hLd⟩ := hcm j hbj (by omega)
  -- the node has output a decision for the slot
  have hlen := Live.decides hσ hadm hf hTH hqT hcT hq hid hto htime hinj hmono harr hwait hstart
    b c n₀ hc hspan hlead hn₀ hbelow t htop ht₁ v hv
  set E := eventsBy tr time (t + (Δ + Δₛ)) with hE
  have hmap := (Local.decisions Validator BlockId Payload (cfg.at v) (inputsBefore tr E v)).2
  have hj : j ∈ (decisionsBy cfg tr time v (t + (Δ + Δₛ))).map Prod.fst := by
    change j ∈ (commitsOf (run (cfg.at v) (State.init (cfg.at v)) (inputsBefore tr E v)).2).map
      Prod.fst
    rw [hmap, List.mem_range]
    rw [decisionsBy_length] at hlen
    change b + c ≤ (stateBefore cfg tr E v).lo at hlen
    change j < (stateBefore cfg tr E v).lo
    omega
  obtain ⟨⟨j', d⟩, hmem, rfl⟩ := List.mem_map.mp hj
  -- that decision is a verdict on the record, so it is the leader block
  obtain ⟨V', hV'⟩ := (cut_before hσ hadm hf htime hinj E v (hTH hv)).2 _ hmem
  haveI : Validity.Quorate (ValidAt (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload) cfg.q Clause.none) cfg.q :=
    Validity.Quorate.of_validAt hadm.2.2.2.1 fun _ _ => Iff.rfl
  have ht : cfg.p.Tolerates H cfg.f cfg.q := ⟨hf, hadm.2.2.2.2, hadm.1⟩
  obtain ⟨-, -, -, hlaws⟩ := Scheme.coveredLaws (boundedSel (P := ValidAt cfg.q Clause.none)
    (honest := H) (Validator := Validator) (BlockId := BlockId) (Payload := Payload)) ht
  have hdL : some L = d := AnchoredRule.decided_unique hlaws trivial hLd.toDecided V' _ hV'
  subst hdL
  -- the leader is honest, so its block reaches its lower blocks
  have hLH : (U.block L).creator ∈ H := by
    rw [hL.2.2]
    have := hlead (j' - b) (by omega)
    rw [Nat.add_sub_cancel' hbj] at this
    exact hTH this
  exact ⟨L, hL, hmem, fun x hx hxc hle =>
    own_reaches_record hσ hadm hf htime hinj hL.1 hx hLH hxc hle⟩

/-- **The node refines the scheme.** -/
theorem holds : Statement := by
  intro Validator BlockId Payload _ _ _ cfg H tr hσ hadm hf htime hinj
  refine ⟨globalRecord (hashInjective_of_trace hinj) (authentic_of_timely htime),
    fun v hv i => (cut_before hσ hadm hf htime hinj i v hv).1,
    fun v hv i => commitInv_before hσ hadm hf htime hinj hv i,
    fun c hc hcH hr => selfParent_of_honest hσ hadm hf htime hinj hc hcH hr, ?_, ?_⟩
  · intro T time gst Δ Δₛ t₁ hTH hqT hcT hq hid hto hmono hdel hwait hsync hstart
    exact waves_leads hσ hadm hf hTH hqT hcT hq hid hto htime hinj hmono
      (arrival_of_delivered hσ hadm hf htime hinj hTH hmono hdel hsync) hwait hstart
  · intro T time gst Δ Δₛ t_r t₁ hTH hqT hcT hq hid hto hmono hdel hfire hwait hsync hup hstart G
    have hgG : gst ≤ G := (le_max_right _ _).trans (Nat.le_add_right _ _)
    have hstart' : Live.StartedBy T tr time G := fun v hv => by
      obtain ⟨i, hi, hit⟩ := hstart v hv
      exact ⟨i, hi, hit.trans hgG⟩
    exact waves_leads hσ hadm hf hTH hqT hcT hq hid hto htime hinj hmono
      (arrival_of_recovered hσ hadm hf hid htime hinj hTH hmono hdel hsync hup hfire hstart)
      hwait hstart'

end Refines

end Node

end LeanDag
