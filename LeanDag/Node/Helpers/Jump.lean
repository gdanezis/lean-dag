import LeanDag.Node.Helpers.Catch
import LeanDag.Node.Helpers.Dropping
/-!
# A node that drops is at or above its floor

`docs/dos-bounds.md` Phase 3.2 item 4.3. A node that drops keeps a proof of
every slot it decided (`paired_before`), whose witness decides the slot again
(`proofsHold_before`). At skip and commit thresholds above `f`, the witness of
slot `k − 1` holds an honest block at the round of slot `k − 1` plus
`voteOffset` or above (`witnessAt_author`), so one round above the floor at
slot `k` (`floorAt`) or above. That block lends references the node can build
on (`lent_avoids_before`, `lent_buildable`), so a node whose top lies below
its floor would jump (`tryBuild_drop_isSome`); a settled node does not
(`settled_before`). So past GST a node is at or above its floor at each
event, once it decided a slot and no honest node is past its next undecided
slot (`floor_le_top_before`).
-/

namespace LeanDag

namespace Node

open Scheme

variable {Validator BlockId Payload : Type} [Fintype Validator] [DecidableEq Validator]
variable [LinearOrder BlockId]
variable {cfg : Config Validator BlockId Payload} {tr : Trace Validator BlockId Payload}
variable {H : Finset Validator}

/-- **A node that drops is at or above its floor**, at an event at which its
top is above `nE`, once it decided a slot and no honest node is past its next
undecided slot, at skip and commit thresholds above `f`: the witness of the
slot below lends references it can build on above its top. -/
theorem floor_le_top_before [Infinite BlockId] (hσ : cfg.σ = boundedSel)
    (hadm : cfg.Admissible) (hfa : cfg.Faithful) (hf : Hᶜ.card ≤ cfg.f)
    (hid : Function.Injective cfg.idOf) (htime : Converge.TimelyAuthentic cfg H tr)
    (hinj : Converge.HashInjective cfg H tr) (hq : 2 ≤ cfg.q) (hdr : cfg.drops = true)
    (hsk : cfg.f < cfg.p.skipThreshold) (hcm : cfg.f < cfg.p.commitThreshold)
    {D : Finset Validator} {nE : ℕ} (hsp : Live.Spread cfg H tr D nE)
    {v : Validator} (hv : v ∈ H) {i t : ℕ} (ht : (stateBefore cfg tr i v).top = some t)
    (hnE : nE ≤ t) (hlo : 1 ≤ (stateBefore cfg tr i v).lo)
    (hle : ∀ w ∈ H, ∀ k, k ≤ i → (stateBefore cfg tr k w).lo ≤ (stateBefore cfg tr i v).lo) :
    (stateBefore cfg tr i v).floor ≤ t := by
  letI := cfg.slots
  set Z := stateBefore cfg tr i v with hZ
  set L := Z.lo with hL
  by_contra hlt
  push Not at hlt
  have hSet : Settled (cfg.at v) Z := (settled_before (cfg := cfg) hq v i).resolve_left
    (by rw [ht]; simp)
  -- the scheme's laws
  haveI : Validity.Quorate (ValidAt (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload) cfg.q Clause.none) cfg.q :=
    Validity.Quorate.of_validAt hadm.2.2.2.1 fun _ _ => Iff.rfl
  have htol : cfg.p.Tolerates H cfg.f cfg.q := ⟨hf, hadm.2.2.2.2, hadm.1⟩
  have hw : 2 ≤ cfg.p.waveLength := by
    rcases htol.2.2 with ⟨-, hw, -⟩ | ⟨-, hw, -⟩ | ⟨-, hw, -⟩ | ⟨-, hw, -⟩ <;> omega
  obtain ⟨hl, -, hcv, -⟩ := coveredLaws (boundedSel (P := ValidAt (Validator := Validator)
    (BlockId := BlockId) (Payload := Payload) cfg.q Clause.none) (honest := H)) htol
  have hvo : 1 ≤ cfg.p.voteOffset := by
    unfold Scheme.Params.voteOffset; split <;> omega
  -- the base below the floor at `L`, with no window
  have hbase := base_below (L := L) hσ hadm hf htime hinj hadm.2.2.2.2 hdr (E₀ := i + 1)
    (E₁ := i) hle fun _ _ _ h₁ h₂ => absurd (h₁.trans h₂) (Nat.not_succ_le_self i)
  -- the floor lies at the floor at `L` or below
  have hFL : Z.floor ≤ floorAt cfg L := by
    have := (Converge.inv_before (cfg := cfg) (tr := tr) i v).floor
    unfold floorOf at this; rw [if_pos (show (cfg.at v).drops = true from hdr)] at this
    exact this
  -- the proof of slot `L − 1` and an honest block of its witness
  obtain ⟨d, hd⟩ := (ledger_before (cfg := cfg) (tr := tr) v i).mem (k := L - 1)
    (show L - 1 < L by omega)
  obtain ⟨P, hP⟩ := paired_before (cfg := cfg) (tr := tr) hσ hid v i _ hd
  obtain ⟨U, V, N, d', -, -, hdec, hwit, hPd⟩ := proofsHold_before (cfg := cfg) (tr := tr)
    hσ hid v i _ hP
  dsimp only at hdec hwit hPd
  obtain ⟨x, hxw, hxH, hxr⟩ := witnessAt_author (σ := boundedSel) (U := U) (V := V) hl hcv hw hf
    hsk hcm N (L - 1) d' hdec
  obtain ⟨hxP, hxs⟩ := hwit x hxw
  obtain ⟨hxZ, -, -, hxU⟩ := hPd x hxP
  obtain ⟨-, hUr, hUc, -, -, hxv⟩ := hxU hxs
  -- it lies one round above the floor or higher, and above the top
  set m := (Z.disk.blk x).round - 1 with hm
  have hxr' : cfg.slots.slotRound (L - 1) + cfg.p.voteOffset ≤ (Z.disk.blk x).round := by
    rw [← hUr]; exact hxr
  have hFm : floorAt cfg L ≤ m := by
    have h₁ : floorAt cfg L ≤ cfg.slots.slotRound (L - 1) + (cfg.p.voteOffset - 1) :=
      min_le_right _ _
    omega
  have hzr : (Z.disk.blk x).round = m + 1 := by omega
  have htm : t < m := by omega
  have hzH : (Z.disk.blk x).creator ∈ H := by rw [← hUc]; exact hxH
  have hzm : (Z.disk.blk x).creator ≠ (cfg.at v).me := fun h => by
    have h₁ := own_le_top htime hv ht hxZ h
    rw [hzr] at h₁
    omega
  have hFm' : Z.floor ≤ m := hFL.trans hFm
  -- it lends references the node can build on
  have hav := lent_avoids_before htime hbase hsp hv le_rfl hxZ hzr hzH (hnE.trans htm.le)
    (by omega) (fun _ => by omega) (Or.inr ⟨hfa, hFm'⟩)
  have hinv := Converge.inv_before (cfg := cfg) (tr := tr) i v
  rw [← hZ] at hinv
  obtain ⟨hsub, hbuild⟩ := lent_buildable (cfg := cfg.at v) (hinv.above.mono (by omega)) hxZ hzr
    (by
      by_contra hk
      have := Z.low x hk
      omega) hfa (fresh_before hid htime hv ht (by omega)) Z.evidence
    (fun j hj hjr => (Converge.kept_before hfa v i).exposed hj
      (hinv.above j hj (by rw [hjr]; exact hFm')).2)
  have hlr : ∀ c ∈ lent Z.disk x, c ∈ Z.disk.ids ∧ (Z.disk.blk c).round = m := fun c hc => by
    refine ⟨hsub hc, ?_⟩
    have := Z.disk.pred x hxZ c hc
    change (Z.disk.blk c).round + 1 = (Z.disk.blk x).round at this
    omega
  have hB : buildable (cfg.at v) Z.memory m (refsAt (cfg.at v) Z.memory m none Z.evidence)
      Z.evidence = true :=
    refsAt_buildable_of Z.memory m none Z.evidence (Or.inr ⟨lent Z.disk x,
      by rw [Z.mirrors.lents_eq hFm']; exact lent_mem_lents hxZ hzr hzm hav,
      by rw [Z.mirrors.buildable_eq hFm' hlr]; exact hbuild⟩)
  -- with a quorum of round `m` in memory
  have hqm : (cfg.at v).q ≤ (Z.memory.authorsAt m).card := by
    rw [Z.mirrors.authorsAt_eq hFm', Store.authorsAt_eq]
    exact quorum_below hbase hadm hv le_rfl (m + 1) hxZ hzr m (by omega) (by omega)
  have hxm : x ∈ Z.memory.ids := Z.mirrors.mem_of hxZ (by omega)
  have hmt : m ≤ Z.memory.topRound := by
    rw [Store.topRound_eq]
    have := Finset.le_sup (f := fun i => (Z.memory.blk i).round) hxm
    rw [Z.mirrors.round hxm] at this
    omega
  have hsome := tryBuild_drop_isSome (cfg := cfg.at v) ht hdr hlt htm hmt hqm hB
    (fun n hn => fresh_before hid htime hv ht hn)
  rw [hSet.build] at hsome
  cases hsome

end Node

end LeanDag
