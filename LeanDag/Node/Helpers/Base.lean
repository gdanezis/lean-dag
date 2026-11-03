import LeanDag.Node.Helpers.CutAbove
/-!
# The base the wave argument reads

`docs/dos-bounds.md` Phase 3.2 item 4.3. The argument of V11 reads the
honest disks up to an event `E₁`, from a round `B` up (`Base`): the record
`R` takes in what the honest nodes knew as they read it from `B` up, and,
at a node that drops, a known block at or below `B` is read so too; its
blocks above `B` are blocks the honest nodes knew; at every event up to
`E₁` every honest disk is read as `R` reads it from `B` up (`CutAbove`) and
is valid at the row above `B`, and, when the node drops, its next undecided
slot lies at round `B + 1` or below; and from `E₀` on the disk only grows,
the node's floor lies at or below its top, and its step is regular
(`Regular`). Without dropping the record of the run is such a base from
round `0` (`base_of_false`).
-/

namespace LeanDag

namespace Node

variable {Validator BlockId Payload : Type} [Fintype Validator] [DecidableEq Validator]
variable [LinearOrder BlockId]

variable (cfg : Config Validator BlockId Payload) (H : Finset Validator)
  (tr : Trace Validator BlockId Payload) in
/-- **A base for the wave argument**, from round `B` up and from event `E₀`
to event `E₁`. -/
structure Base (R : BlockRecord Validator BlockId Payload (ValidAt cfg.q Clause.none) H)
    (B E₀ E₁ : ℕ) : Prop where
  grounds : ∀ v ∈ H, Grounds (cfg.at v) (CutAbove R B) (knownAll cfg H tr)
  known : cfg.drops = true → ∀ x ∈ knownAll cfg H tr, x.2.round ≤ B → CutAbove R B x.1 x.2
  real : ∀ c ∈ R.ids, B < (R.block c).round → (c, R.block c) ∈ knownAll cfg H tr
  disk : ∀ v ∈ H, ∀ k, k ≤ E₁ →
    AllGood (CutAbove R B) (stateBefore cfg tr k v).disk ∧
      UpperValid cfg.q cfg.xp (B + 1) (stateBefore cfg tr k v).disk ∧
      (cfg.drops = true → cfg.slots.slotRound (stateBefore cfg tr k v).lo ≤ B + 1)
  window : ∀ v ∈ H, ∀ k, E₀ ≤ k → k ≤ E₁ →
    (∀ k', k ≤ k' → k' ≤ E₁ →
        Grows (stateBefore cfg tr k v).disk (stateBefore cfg tr k' v).disk) ∧
      (stateBefore cfg tr k v).floor ≤ (stateBefore cfg tr k v).top.getD 0 ∧
      (k + 1 ≤ E₁ →
        Regular (cfg.at v) (stateBefore cfg tr k v) (stateBefore cfg tr (k + 1) v))

variable {cfg : Config Validator BlockId Payload} {H : Finset Validator}
  {tr : Trace Validator BlockId Payload}

/-- **A block on an honest disk is valid at the row**, before a base's
end: when the node does not drop, or above the base's round. -/
theorem Base.valid {R : BlockRecord Validator BlockId Payload (ValidAt cfg.q Clause.none) H}
    {B E₀ E₁ : ℕ} (hbase : Base cfg H tr R B E₀ E₁) {v : Validator} (hv : v ∈ H) {k : ℕ}
    (hk : k ≤ E₁) {j : BlockId} (hj : j ∈ (stateBefore cfg tr k v).disk.ids)
    (hr : cfg.drops = false ∨ B + 1 ≤ ((stateBefore cfg tr k v).disk.blk j).round) :
    ((stateBefore cfg tr k v).disk.full j).refs ⊆ (stateBefore cfg tr k v).disk.ids ∧
      rowValid cfg.q cfg.xp (stateBefore cfg tr k v).disk.full
        ((stateBefore cfg tr k v).disk.full j) := by
  rcases hr with hd | hr
  · exact (Converge.inv_before (cfg := cfg) (tr := tr) k v).valid hd j hj
  · exact (hbase.disk v hv k hk).2.1 j hj hr

/-- **Without dropping, the record of the run is a base from round `0`**,
over every stretch: it grounds what the honest nodes knew (`ground`), every
honest disk is a cut of it (`cut_before`), valid, and grows
(`grows_before`), its floor `voteOffset` below its top at most. -/
theorem base_of_false (hσ : cfg.σ = boundedSel) (hadm : cfg.Admissible) (hf : Hᶜ.card ≤ cfg.f)
    (htime : Converge.TimelyAuthentic cfg H tr) (hinj : Converge.HashInjective cfg H tr)
    (hdr : cfg.drops = false) (E₀ E₁ : ℕ) :
    Base cfg H tr (globalRecord (hashInjective_of_trace hinj) (authentic_of_timely htime))
      0 E₀ E₁ := by
  refine ⟨fun v _ => Ground.groundsAbove (cfg := cfg.at v)
      (ground (cfg := cfg) (hashInjective_of_trace hinj) (authentic_of_timely htime)),
    fun h => absurd (hdr.symm.trans h) Bool.false_ne_true, fun c hc _ => ?_,
    fun v hv k _ => ?_, fun v hv k _ _ => ?_⟩
  · obtain ⟨x, hx, rfl⟩ := exists_of_mem_knownIds (mem_globalIds.mp hc).1
    have hcont := content_of_known (hashInjective_of_trace hinj) hx
    change (x.1, content cfg H tr x.1) ∈ _
    rw [hcont]; exact hx
  · refine ⟨fun j hj _ => ?_,
      fun j hj _ => (Converge.inv_before (cfg := cfg) (tr := tr) k v).valid hdr j hj,
      fun h => absurd (hdr.symm.trans h) Bool.false_ne_true⟩
    obtain ⟨hU, heq⟩ := (cut_before hσ hadm hf htime hinj hdr k v hv).1 j hj
    exact ⟨hU, by rw [heq], by rw [heq], fun _ => heq⟩
  · exact ⟨fun _ hk _ => grows_before (cfg := cfg) (tr := tr) v hdr hk,
      (Converge.inv_before (cfg := cfg) (tr := tr) k v).floor.trans
        ((floorOf_le_top (cfg := cfg.at v) hdr _).trans (Nat.sub_le _ _)),
      fun _ => Regular.of_false hdr⟩

end Node

end LeanDag
