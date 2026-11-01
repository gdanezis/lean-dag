import LeanDag.Node.Bound.Statement
import LeanDag.Node.Helpers.Bound
import LeanDag.Node.Helpers.Arrive
import LeanDag.Node.Local.Proof
import LeanDag.Common.Exclusion
import LeanDag.Node.Helpers.Catch
/-!
# The blocks a node holds a round — proof

Honest `v`'s disk is valid, so a block of it references none of the
authors it exposes and exposes those its references expose, and each
block above round `0` references an honest block one round below, since
fewer than `q` nodes are not honest. Once every honest block of round
`m + 1` exposes `X`, no block of the disk from round `m + 2` on references
`X` (D17, `not_mem_creators_refs_of_correct_exposed`), so no block of `X`
from round `m + 1` on is referenced. Along the trace twins convict and
each author other than `v` has at most two unreferenced blocks a round
(`steady_before`), and `v`'s own blocks lie at distinct rounds
(`Local.oneEach`, `own_known`). So each round from `m + 1` on holds one
block of `v`, one of each other author not convicted, and two of each
convicted.
-/

namespace LeanDag

namespace Node

namespace Bound

theorem bounded : Bounded := by
  intro Validator BlockId Payload _ _ _ cfg H tr v i m k htime hinj hv hq s hexp hk
  set st := s.disk with hst
  have hC : Steady (cfg.at v) s := steady_before hinj hv i
  have hval : StoreValid cfg.q cfg.xp st := (Converge.inv_before (cfg := cfg) (tr := tr) i v).valid
  -- each block above round `0` references an honest block one round below
  have hcb : CorrectBelow st.blk st.ids H := by
    intro b hb hr
    by_contra hno
    push Not at hno
    have hsub : creators st.blk (st.blk b) ⊆ Hᶜ := by
      intro Y hY
      obtain ⟨j, hj, rfl⟩ := mem_creatorsOf.mp hY
      exact Finset.mem_compl.mpr fun hYH =>
        hno j hj (st.complete b hb j hj) hYH (st.pred b hb j hj)
    have := ((hval b hb).quorum hr).trans (Finset.card_le_card hsub)
    change cfg.q ≤ Hᶜ.card at this
    omega
  have hdos : DoSValidOn st.blk st.ids fun b X => X ∈ cfg.xp.ex (st.blk b).payload :=
    fun b hb j hj => (hval b hb).clause.2.2 j hj
  have hup : InheritedOn st.blk st.ids fun b X => X ∈ cfg.xp.ex (st.blk b).payload := by
    intro b hb j hj X hX
    rw [(hval b hb).clause.2.1]
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨j, hj, hX⟩)
  -- from round `m + 1` on, no block of a convicted author is referenced
  have hfree : ∀ X ∈ s.detected, ∀ x ∈ st.ids, (st.blk x).creator = X → m + 1 ≤ (st.blk x).round →
      ∀ z ∈ st.ids, x ∉ (st.blk z).refs := by
    intro X hX x hx hxc hxr z hz hxz
    have hzr : (st.blk x).round + 1 = (st.blk z).round := st.pred z hz x hxz
    exact not_mem_creators_refs_of_correct_exposed (n := m) hcb hdos hup
      (fun c hc hcr hcH => hexp c hc hcr hcH X hX) hz (by omega) (mem_creatorsOf.mpr ⟨x, hxz, hxc⟩)
  -- each author's blocks of round `k`
  set D := s.detected
  set of := fun Y => st.ids.filter fun j => (st.blk j).creator = Y ∧ (st.blk j).round = k
  have hper : ∀ Y, (of Y).card ≤ 1 + if Y ∈ D then 1 else 0 := by
    intro Y
    by_cases hYv : Y = v
    · -- the node's own blocks lie at distinct rounds
      subst hYv
      refine (Finset.card_le_one.mpr fun a ha b hb => ?_).trans (Nat.le_add_right _ _)
      obtain ⟨ha, hac, har⟩ := Finset.mem_filter.mp ha
      obtain ⟨hb, hbc, hbr⟩ := Finset.mem_filter.mp hb
      have hB := Local.oneEach _ _ _ (cfg.at Y) (inputsBefore tr i Y)
      dsimp only at hB
      have hnd := (hB.imp ne_of_lt)
      have hpa := own_known htime hv hv le_rfl
        ((Converge.inv_before (cfg := cfg) (tr := tr) i Y).known a ha) hac
      have hpb := own_known htime hv hv le_rfl
        ((Converge.inv_before (cfg := cfg) (tr := tr) i Y).known b hb) hbc
      have := List.inj_on_of_nodup_map hnd hpa hpb (by simp only; rw [har, hbr])
      exact (Prod.mk.inj this).1
    · by_cases hY : Y ∈ D
      · rw [if_pos hY]
        refine (Finset.card_le_card fun j hj => ?_).trans (hC.1.2 Y hYv k)
        obtain ⟨hj, hjc, hjr⟩ := Finset.mem_filter.mp hj
        exact Finset.mem_filter.mpr ⟨hj, hjc, hjr, hfree Y hY j hj hjc (hjr ▸ hk)⟩
      · rw [if_neg hY]
        exact hC.1.1.card_le_one hY hYv k
  have hsub : st.atRound k ⊆ Finset.univ.biUnion of := by
    intro j hj
    obtain ⟨hj, hjr⟩ := Store.mem_atRound.mp hj
    exact Finset.mem_biUnion.mpr ⟨(st.blk j).creator, Finset.mem_univ _,
      Finset.mem_filter.mpr ⟨hj, rfl, hjr⟩⟩
  calc (st.atRound k).card ≤ ∑ Y, (of Y).card :=
        (Finset.card_le_card hsub).trans Finset.card_biUnion_le
    _ ≤ ∑ Y, (1 + if Y ∈ D then 1 else 0) := Finset.sum_le_sum fun Y _ => hper Y
    _ = Fintype.card Validator + D.card := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one,
          Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter, Nat.cast_id]

/-- **Under spread evidence, an honest block above `nE` exposes every
author an honest node convicted**: those authors are in `D`, its builder
convicted all of `D` and references none of them, so its payload names
them. -/
theorem exposes_spread {Validator BlockId Payload : Type} [Fintype Validator]
    [DecidableEq Validator] [LinearOrder BlockId] {cfg : Config Validator BlockId Payload} {H : Finset Validator}
    {tr : Trace Validator BlockId Payload} {D : Finset Validator} {nE : ℕ}
    (hσ : cfg.σ = boundedSel) (hadm : cfg.Admissible) (hfa : cfg.Faithful)
    (hf : Hᶜ.card ≤ cfg.f) (htime : Converge.TimelyAuthentic cfg H tr)
    (hinj : Converge.HashInjective cfg H tr) (hsp : Live.Spread cfg H tr D nE)
    {v : Validator} (hv : v ∈ H) (i : ℕ) {c : BlockId} {r : ℕ}
    (hc : c ∈ (stateBefore cfg tr i v).disk.ids)
    (hcr : ((stateBefore cfg tr i v).disk.blk c).round = r + 1)
    (hcH : ((stateBefore cfg tr i v).disk.blk c).creator ∈ H) (hrE : nE ≤ r) :
    ∀ X ∈ (stateBefore cfg tr i v).detected,
      X ∈ cfg.xp.ex ((stateBefore cfg tr i v).disk.blk c).payload := by
  intro X hX
  set s := stateBefore cfg tr i v with hs
  -- the author is in `D`
  have hXD : X ∈ D := by
    obtain ⟨e, he, he1, hne⟩ := (Converge.evidenceOn_before (cfg := cfg) (tr := tr) v i).1 X hX
    exact excluded_before_spread hsp hv i 0 (Finset.mem_union_left _
      (Finset.mem_image.mpr ⟨e, Finset.mem_filter.mpr ⟨he, hne⟩, he1⟩))
  -- the block as its builder built it
  have hcut := (cut_before hσ hadm hf htime hinj i v hv).1
  have hcU := (hcut _ hc).1
  have hcc : ((globalRecord (hashInjective_of_trace hinj) (authentic_of_timely htime)).block
      c).creator = (s.disk.blk c).creator := by rw [hcut.eq hc]
  have hcr' : ((globalRecord (hashInjective_of_trace hinj) (authentic_of_timely htime)).block
      c).round = r + 1 := by rw [hcut.eq hc]; exact hcr
  obtain ⟨iw, inpw, xw, oww, hiw, -, hbsw, hshw, -, ⟨-, -, -, -, hew⟩, -, -, -, -, hpay⟩ :=
    built_block (fun _ => 0) hσ hadm hf htime hinj hcH hcU hcc hcr'
  have ho : ∀ j, oww = some j →
      (xw.disk.blk j).creator = (cfg.at (s.disk.blk c).creator).me := fun j hj => by
    rcases hshw.2.2 with ⟨ht, hoe⟩ | ⟨-, hon, -⟩
    · obtain ⟨j', hj', -, -, hjc⟩ := hbsw.own r ht
      rw [hoe, hj'] at hj
      cases hj
      exact hjc
    · rw [hon] at hj; cases hj
  have hAD := refs_avoid_spread (r := r) hsp hiw hcH hbsw hew (by rw [hcr']; omega) ho
  -- its builder had convicted the author
  obtain ⟨e, he, he1, hne⟩ := hbsw.ev.1 X
    (hbsw.det (hsp.2.2 iw _ inpw hiw hcH _ hew (by rw [hcr']; omega) hXD))
  rw [← hcut.eq hc, hpay]
  unfold payloadFor
  erw [(hfa _ _ _).2]
  refine Finset.mem_union_left _ (Finset.mem_image.mpr ⟨e, Finset.mem_filter.mpr
    ⟨Finset.mem_filter.mpr ⟨he, fun hm => ?_⟩, hne⟩, he1⟩)
  obtain ⟨k, hk, hkc⟩ := mem_creatorsOf.mp hm
  exact hAD k hk (by rw [hkc, he1]; exact hXD)

/-- **Under spread evidence the bound holds from round `nE + 1`.** -/
theorem spreads : Spreads := by
  intro Validator BlockId Payload _ _ _ cfg H tr D nE v i k hσ hadm hfa hf hq htime hinj hsp hv
    hk
  exact bounded Validator BlockId Payload cfg H tr v i nE k htime hinj hv hq
    (fun c hc hcr hcH X hX => exposes_spread hσ hadm hfa hf htime hinj hsp hv i hc hcr hcH le_rfl
      X hX) hk

theorem holds : Statement := ⟨bounded, spreads⟩

end Bound

end Node

end LeanDag
