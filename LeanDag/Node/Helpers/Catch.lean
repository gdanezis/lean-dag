import LeanDag.Node.Helpers.Armed
/-!
# Copied references and catch-up

`docs/validator.md` §5.3. A node at round `n` holding a peer's round-`n + 1`
block `z` passes the reach and certificate tests with the references `z`
lends it when the peer's references passed them (`ready_transfer`,
`refsAt_ready`, `lent_buildable`): the leader blocks the tests read are
reached from `z`'s references, so the node holds them and reads the same
votes. A quorum has `f + 1` reliable authors, since `2f + c + 1 ≤ q`
(`two_f_c_lt_q`, `quorum_reliable`), and of the `f + 1` authors of a
round a node is behind one is honest (`behind_honest`). A held block
brings a quorum of each round below it (`quorum_below`). Past GST, once
`f + 1` reliable nodes are at round `n`, every reliable node is at `n`
within `A = Δ + Δₛ` (`catches_up`).
-/

namespace LeanDag

namespace Node

open Scheme

variable {Validator BlockId Payload : Type} [Fintype Validator] [DecidableEq Validator]
variable [LinearOrder BlockId]
variable {cfg : Config Validator BlockId Payload}
variable {P : Validity Validator BlockId Payload} {H : Finset Validator}
variable {U : BlockRecord Validator BlockId Payload P H}

section Cut

variable {st : Store Validator BlockId Payload}

omit [Fintype Validator] [DecidableEq Validator] in
/-- **A record path from a cut is a store path.** -/
theorem IsCut.reachesFrom_store (hc : IsCut U st) {i : BlockId} :
    ∀ {j : BlockId}, j ∈ st.ids → ReachesFrom U.block j i → ReachesFrom st.blk j i := by
  intro j hj h
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ReachesFrom.refl
  | @head a c hstep hrest ih =>
    have hstep : c ∈ (U.block a).refs := hstep
    have hcs : c ∈ (st.blk a).refs := by rw [← hc.eq hj]; exact hstep
    exact Relation.ReflTransGen.head hcs (ih (st.complete a hj c hcs))

omit [Fintype Validator] [DecidableEq Validator] in
/-- **A cut holds a record path's short history**: a block that a block of
the store reaches in the record, at most `m` rounds below it, lies within `m`
steps of it in the store. -/
theorem IsCut.mem_historyUptoFrom [P.Mechanised] (hc : IsCut U st) {j i : BlockId} {m : ℕ}
    (hj : j ∈ st.ids) (hm : (U.block j).round ≤ m + (U.block i).round)
    (h : ReachesFrom U.block j i) :
    i ∈ historyUptoFrom st.blk m j := by
  classical
  have hi : i ∈ st.ids := hc.down hj h
  exact mem_historyUptoFrom_of_round st.toRecord.causal hj
    (by change (st.blk j).round ≤ m + (st.blk i).round
        rw [← hc.round hj, ← hc.round hi]; exact hm)
    (hc.reachesFrom_store hj h)

end Cut

/-- Where votes are certified a round later, an admissible row's
certificate threshold is positive. -/
theorem certThreshold_pos (hadm : cfg.Admissible) (hvc : cfg.p.voteIsCert = false) :
    1 ≤ cfg.p.certThreshold := by
  rcases hadm.1 with ⟨h, -⟩ | ⟨-, -, -, h3, -, -⟩ | ⟨h, -⟩ | ⟨-, -, -, h, -⟩
  · rw [hvc] at h; cases h
  · omega
  · rw [hvc] at h; cases h
  · exact h

omit [Fintype Validator] in
/-- **The tests carry over to a superset of the references**, from one cut
to another holding the superset: the leader blocks the tests read are
reached from the references, so the second cut holds them. -/
theorem ready_transfer [P.Mechanised] (hσ : cfg.σ = boundedSel)
    (hct : cfg.p.voteIsCert = false → 1 ≤ cfg.p.certThreshold)
    {x Z : Store Validator BlockId Payload} (hx : IsCut U x) (hZ : IsCut U Z)
    {R R' : Finset BlockId} {n : ℕ} (hR : R ⊆ x.ids) (hRR : R ⊆ R') (hR'Z : R' ⊆ Z.ids)
    (hreach : reachReady cfg x R n = true) (hcert : certReady cfg x R n = true) :
    reachReady cfg Z R' n = true ∧ certReady cfg Z R' n = true := by
  -- a candidate of the store `x` reached from a reference
  have hcand : ∀ k L, L ∈ candidatesIn (S := cfg.slots) x.toRecord x.view k →
      ∀ c ∈ R, ReachesFrom U.block c L →
      L ∈ candidatesIn (S := cfg.slots) Z.toRecord Z.view k ∧ L ∈ Z.ids := by
    intro k L hL c hc hcL
    obtain ⟨hLx, hLc, hLr⟩ := Finset.mem_filter.mp hL
    have hLZ : L ∈ Z.ids := hZ.down (hR'Z (hRR hc)) hcL
    refine ⟨Finset.mem_filter.mpr ⟨hLZ, ?_, ?_⟩, hLZ⟩
    · change (Z.blk L).creator = _
      rw [← hZ.creator hLZ, hx.creator hLx]; exact hLc
    · change (Z.blk L).round = _
      rw [← hZ.round hLZ, hx.round hLx]; exact hLr
  constructor
  · unfold reachReady at hreach ⊢
    simp only [Store.leaderBlocks_eq] at hreach ⊢
    refine List.all_eq_true.mpr fun m hm => ?_
    have h₁ := List.all_eq_true.mp hreach m hm
    by_cases hmn : m ≤ n
    · rw [if_pos hmn] at h₁ ⊢
      refine List.all_eq_true.mpr fun k hk => ?_
      have h₂ := List.all_eq_true.mp h₁ k hk
      obtain ⟨L, hL, c, hc, hhist⟩ := of_decide_eq_true h₂
      have hLx := (Finset.mem_filter.mp hL).1
      have hcx := hR hc
      have hrd := round_le_of_mem_historyUptoFrom x.toRecord m hcx hhist
      change (x.blk c).round ≤ m + (x.blk L).round at hrd
      have hcL : ReachesFrom U.block c L :=
        hx.reachesFrom hcx (reaches_of_mem_historyUptoFrom hhist)
      obtain ⟨hLZ, -⟩ := hcand k L hL c hc hcL
      refine decide_eq_true ⟨L, hLZ, c, hRR hc, hZ.mem_historyUptoFrom (hR'Z (hRR hc)) ?_ hcL⟩
      rw [hx.round hcx, hx.round hLx]; exact hrd
    · rw [if_neg hmn]
  · unfold certReady at hcert ⊢
    simp only [Store.leaderBlocks_eq] at hcert ⊢
    cases hvc : cfg.p.voteIsCert
    · rw [hvc, if_neg (by simp)] at hcert
      rw [if_neg (by simp)]
      by_cases hvn : cfg.p.voteOffset ≤ n
      · rw [if_pos hvn] at hcert ⊢
        refine List.all_eq_true.mpr fun k hk => ?_
        have h₂ := List.all_eq_true.mp hcert k hk
        obtain ⟨L, hL, hcount⟩ := of_decide_eq_true h₂
        have hLx := (Finset.mem_filter.mp hL).1
        -- the votes, read on the record
        obtain ⟨Vx, -, hVx⟩ := hx.extend ⟨∅, Finset.empty_subset _, fun i hi => absurd hi
          (Finset.notMem_empty _)⟩ (fun i hi => absurd hi (Finset.notMem_empty _))
        have hvax := ViewsAbove.of_store (st := x) (V := Vx) hVx (fun i hi => (hx i hi).2)
        have hvx : ∀ b ∈ R, (cfg.σ.Votes x.toRecord b L ↔
            (boundedSel : VoteSel Validator BlockId Payload P H).Votes U b L) := by
          intro b hb
          rw [hσ]
          exact hvax.votes_iff (hR hb) (Nat.zero_le _) hLx (Nat.zero_le _)
        -- some reference votes, so the leader block lies in its history
        have hpos := hct hvc
        obtain ⟨a, ha⟩ :
            (creatorsOf x.blk (R.filter fun b => cfg.σ.Votes x.toRecord b L)).Nonempty :=
          Finset.card_pos.mp (by omega)
        obtain ⟨b, hb, -⟩ := Finset.mem_image.mp ha
        obtain ⟨hbR, hbv⟩ := Finset.mem_filter.mp hb
        have hbU := (hvx b hbR).mp hbv
        obtain ⟨hLh, -, -⟩ := (boundedSel : VoteSel Validator BlockId Payload P H).sound U b _ _ L
          hbU
        have hbL : ReachesFrom U.block b L := (mem_history_iff (hx b (hR hbR)).1).mp hLh
        obtain ⟨hLZ, hLZi⟩ := hcand k L hL b hbR hbL
        obtain ⟨VZ, -, hVZ⟩ := hZ.extend ⟨∅, Finset.empty_subset _, fun i hi => absurd hi
          (Finset.notMem_empty _)⟩ (fun i hi => absurd hi (Finset.notMem_empty _))
        have hvaZ := ViewsAbove.of_store (st := Z) (V := VZ) hVZ (fun i hi => (hZ i hi).2)
        refine decide_eq_true ⟨L, hLZ, le_trans hcount (Finset.card_le_card fun a ha => ?_)⟩
        obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
        obtain ⟨hbR, hbv⟩ := Finset.mem_filter.mp hb
        have hbZ := hR'Z (hRR hbR)
        have hvZ : cfg.σ.Votes Z.toRecord b L := by
          rw [hσ]
          exact (hvaZ.votes_iff hbZ (Nat.zero_le _) hLZi (Nat.zero_le _)).mpr
            ((hvx b hbR).mp hbv)
        refine Finset.mem_image.mpr ⟨b, Finset.mem_filter.mpr ⟨hRR hbR, hvZ⟩, ?_⟩
        rw [← hZ.creator hbZ, hx.creator (hR hbR)]
      · rw [if_neg hvn]
    · rfl

omit [Fintype Validator] in
/-- A held round-`r + 1` block of another author lends its references,
when they reference no author the node leaves out. -/
theorem lent_mem_lents {st : Store Validator BlockId Payload} {r : ℕ}
    {E : Finset (Validator × BlockId × BlockId)} {c : BlockId}
    (hc : c ∈ st.ids) (hcr : (st.blk c).round = r + 1) (hcm : (st.blk c).creator ≠ cfg.me)
    (hav : ∀ i ∈ lent st c, (st.blk i).creator ∉ excluded cfg st r E) :
    lent st c ∈ lents cfg st r E :=
  List.mem_filter.mpr ⟨List.mem_map.mpr ⟨c, List.mem_filter.mpr ⟨(Finset.mem_sort _).mpr
    (Store.mem_atRound.mpr ⟨hc, hcr⟩), decide_eq_true hcm⟩, rfl⟩, decide_eq_true hav⟩

omit [Fintype Validator] in
/-- **`refsAt` passes the tests when a held block's lent references do**:
a round-`r + 1` block of the store by another author whose lent references
pass the tests, can be built on and reference no author the node leaves
out. -/
theorem refsAt_ready {st : Store Validator BlockId Payload} {r : ℕ} {o : Option BlockId}
    {E : Finset (Validator × BlockId × BlockId)}
    {c : BlockId} (hc : c ∈ st.ids) (hcr : (st.blk c).round = r + 1)
    (hcm : (st.blk c).creator ≠ cfg.me)
    (hready : reachReady cfg st (lent st c) r = true ∧ certReady cfg st (lent st c) r = true)
    (hb : buildable cfg st r (lent st c) E = true)
    (hav : ∀ i ∈ lent st c, (st.blk i).creator ∉ excluded cfg st r E) :
    reachReady cfg st (refsAt cfg st r o E) r = true ∧
      certReady cfg st (refsAt cfg st r o E) r = true := by
  unfold refsAt
  dsimp only
  split
  · rename_i h
    simp only [Bool.and_eq_true] at h
    exact h.1
  · have hs : ((lents cfg st r E).find? fun R => (reachReady cfg st R r && certReady cfg st R r) &&
        buildable cfg st r R E).isSome :=
      List.find?_isSome.mpr ⟨_, lent_mem_lents hc hcr hcm hav, by rw [hready.1, hready.2, hb]; rfl⟩
    obtain ⟨R, hR⟩ := Option.isSome_iff_exists.mp hs
    rw [hR]
    have := List.find?_some hR
    simp only [Bool.and_eq_true] at this
    exact this.1

omit [Fintype Validator] in
/-- **A peer's block lends references the node can build on**: a valid
round-`n + 1` block of the store, under a faithful payload source, with no
block on the store under the identifier of a block of the node's own above
round `n`. -/
theorem lent_buildable {Z : Store Validator BlockId Payload} (hZ : StoreValid cfg.q cfg.xp Z)
    {n : ℕ} {z : BlockId} (hzZ : z ∈ Z.ids) (hzr : (Z.blk z).round = n + 1)
    (hfa : cfg.Faithful) (hfresh : ∀ (P : Payload) R, cfg.idOf ⟨n + 1, cfg.me, R, P⟩ ∉ Z.ids)
    (E : Finset (Validator × BlockId × BlockId)) :
    lent Z z ⊆ Z.ids ∧ buildable cfg Z n (lent Z z) E = true :=
  ⟨fun j hj => Z.complete z hzZ j hj,
    lent_buildable_of E hfa hzZ hzr (hZ z hzZ) (hfresh _ _)⟩

/-! ## Rounds and build times along a trace -/

section Trace

variable {tr : Trace Validator BlockId Payload} {v : Validator}

/-- **A node's own block stays on its disk** at every later event. -/
theorem own_held {p : ℕ} {inp : Input Validator BlockId Payload} (hp : tr[p]? = some (v, inp))
    {e : BlockId × Block Validator BlockId Payload} (he : e ∈ persists (outputsAt cfg tr p))
    {E : ℕ} (hpE : p < E) :
    e.1 ∈ (stateBefore cfg tr E v).disk.ids := by
  rw [outputsAt_eq hp] at he
  have hin := (step_persist (cfg := cfg.at v) e he).1
  have hs : stateBefore cfg tr (p + 1) v =
      (Node.step (cfg.at v) (stateBefore cfg tr p v) inp).1 := by
    rw [stateBefore_succ hp, if_pos rfl]
  rw [← hs] at hin
  exact (grows_before (cfg := cfg) (tr := tr) v (show p + 1 ≤ E by omega)).1 hin

variable {time : ℕ → ℕ} (hmono : Live.TimeMono tr time)
include hmono

/-- **A node is at a round it built**, at any time after it built it. -/
theorem top_of_built {b : ℕ} {inp : Input Validator BlockId Payload}
    (hb : tr[b]? = some (v, inp)) {e : BlockId × Block Validator BlockId Payload}
    (he : e ∈ persists (outputsAt cfg tr b)) {τ : ℕ} (hbτ : time b ≤ τ) :
    (stateAt cfg tr time v τ).top.isSome ∧ e.2.round ≤ topAt cfg tr time v τ := by
  have hbl : b < tr.length := (List.getElem?_eq_some_iff.mp hb).1
  have hbE : b + 1 ≤ eventsBy tr time τ := (lt_eventsBy hmono hbl).mpr hbτ
  obtain ⟨t, ht, hrt⟩ := built_le_top hb he
  obtain ⟨h₁, h₂, -⟩ := rises_before (cfg := cfg) v hbE
  rw [ht] at h₁ h₂
  exact ⟨h₂ rfl, hrt.trans h₁⟩

/-- **A node at a round built it**, at its first event building it, by
then. -/
theorem built_of_top {τ n : ℕ} (hs : (stateAt cfg tr time v τ).top.isSome)
    (hn : n ≤ topAt cfg tr time v τ)
    (hj : ∀ k < eventsBy tr time τ, ∀ inp, tr[k]? = some (v, inp) →
      ((stateBefore cfg tr k v).recovering = true ∨ inp = .restart) →
      (stateBefore cfg tr (k + 1) v).top.getD 0 < n) :
    ∃ i inp e, tr[i]? = some (v, inp) ∧ e ∈ persists (outputsAt cfg tr i) ∧ e.2.round = n ∧
      builtAt cfg tr time v n = time i ∧ time i ≤ τ := by
  obtain ⟨b, hbE, hbv, e, he, her⟩ := built_by (eventsBy tr time τ) hs hn hj
  obtain ⟨i₀, hi₀b, hbt, hi₀v, e₀, he₀, he₀r⟩ := builtAt_first (cfg := cfg) time hbv ⟨e, he, her⟩
  obtain ⟨inp, hi₀⟩ := Converge.event_of_map hi₀v
  obtain ⟨inpb, hb⟩ := Converge.event_of_map hbv
  have hbl : b < tr.length := (List.getElem?_eq_some_iff.mp hb).1
  exact ⟨i₀, inp, e₀, hi₀, he₀, he₀r, hbt,
    (hmono i₀ b hi₀b hbl).trans ((lt_eventsBy hmono hbl).mp hbE)⟩

end Trace

section Record

variable {tr : Trace Validator BlockId Payload} {time : ℕ → ℕ}

/-- **A reliable block of the run's record was built** at its author's
first event building its round. -/
theorem event_of_mem (hinj : Converge.HashInjective cfg H tr)
    (htime : Converge.TimelyAuthentic cfg H tr) {v : Validator} (hv : v ∈ H) {c : BlockId}
    (hcU : c ∈ (globalRecord (hashInjective_of_trace hinj) (authentic_of_timely htime)).ids)
    (hcv : ((globalRecord (hashInjective_of_trace hinj) (authentic_of_timely htime)).block
      c).creator = v) :
    ∃ i inp e, tr[i]? = some (v, inp) ∧ e ∈ persists (outputsAt cfg tr i) ∧ e.1 = c ∧
      e.2.round = ((globalRecord (hashInjective_of_trace hinj)
        (authentic_of_timely htime)).block c).round ∧
      builtAt cfg tr time v ((globalRecord (hashInjective_of_trace hinj)
        (authentic_of_timely htime)).block c).round = time i := by
  have hinjR := hashInjective_of_trace hinj
  have hauthR := authentic_of_timely htime
  obtain ⟨x, hxK, rfl⟩ := exists_of_mem_knownIds (mem_globalIds.mp hcU).1
  have hcont := content_of_known hinjR hxK
  have hxc : x.2.creator = v := by
    have := hcv; simp only [globalRecord, hcont] at this; exact this
  have hxr : x.2.round = ((globalRecord hinjR hauthR).block x.1).round := by
    simp only [globalRecord, hcont]
  have hxp := mem_persists_of_known hinjR hauthR hxK (by rw [hxc]; exact hv)
  rw [hxc] at hxp
  obtain ⟨j, -, hjv, hxj⟩ := mem_persists_before (cfg := cfg) (tr := tr) v tr.length hxp
  obtain ⟨i₀, -, hbt, hi₀v, e₀, he₀, he₀r⟩ :=
    builtAt_first (cfg := cfg) time hjv ⟨x, hxj, hxr⟩
  obtain ⟨inp, hi₀⟩ := Converge.event_of_map hi₀v
  have he₀p : e₀ ∈ persists (runOf cfg tr v).2 :=
    mem_persists_iff.mpr (mem_outputs_of_event hi₀ (mem_persists_iff.mp he₀))
  have hex : e₀ = x := eq_of_persists v he₀p hxp (by rw [he₀r, hxr])
  exact ⟨i₀, inp, e₀, hi₀, he₀, by rw [hex], he₀r, hbt⟩

/-- **A reliable node's block is in the run's record**, at its round and
by its author: the disk after the event holds it, and is a cut. -/
theorem built_mem (hσ : cfg.σ = boundedSel) (hadm : cfg.Admissible) (hf : Hᶜ.card ≤ cfg.f)
    (htime : Converge.TimelyAuthentic cfg H tr) (hinj : Converge.HashInjective cfg H tr)
    {v : Validator} (hv : v ∈ H) {p : ℕ}
    {inp : Input Validator BlockId Payload} (hp : tr[p]? = some (v, inp))
    {e : BlockId × Block Validator BlockId Payload} (he : e ∈ persists (outputsAt cfg tr p)) :
    e.1 ∈ (globalRecord (hashInjective_of_trace hinj) (authentic_of_timely htime)).ids ∧
      ((globalRecord (hashInjective_of_trace hinj) (authentic_of_timely htime)).block
        e.1).round = e.2.round ∧
      ((globalRecord (hashInjective_of_trace hinj) (authentic_of_timely htime)).block
        e.1).creator = v := by
  have hinjR := hashInjective_of_trace hinj
  have hK : e ∈ knownAll cfg H tr :=
    ⟨v, hv, List.mem_append_right _
      (mem_persists_iff.mpr (mem_outputs_of_event hp (mem_persists_iff.mp he)))⟩
  have hcont := content_of_known hinjR hK
  have hgood := ((Converge.inv_before (cfg := cfg) (tr := tr) (p + 1) v).good e
    (persists_of_event hp he)).2.1
  refine ⟨?_, by simp only [globalRecord, hcont], by simp only [globalRecord, hcont]; exact hgood⟩
  have hin : e.1 ∈ (stateBefore cfg tr (p + 1) v).disk.ids := by
    rw [outputsAt_eq hp] at he
    rw [stateBefore_succ hp, if_pos rfl]
    exact (step_persist (cfg := cfg.at v) e he).1
  exact ((cut_before hσ hadm hf htime hinj (p + 1) v hv).1 e.1 hin).1

end Record

/-! ## Catch-up -/

section Spread

variable {tr : Trace Validator BlockId Payload} {D : Finset Validator} {nE : ℕ}

/-- **Under spread evidence, an honest node leaves out only authors of
`D`**, at a state it builds from. -/
theorem excluded_sub_spread (hsp : Live.Spread cfg H tr D nE) {v : Validator}
    {s x : State Validator BlockId Payload} {inp : Input Validator BlockId Payload}
    (h : BuildState (cfg.at v) U (knownAll cfg H tr) s inp x) (r : ℕ) :
    excluded (cfg.at v) x.disk r x.evidence ⊆ D :=
  h.excluded_sub
    (fun y hy e he hne => by
      obtain ⟨u, hu, hk⟩ := hy
      exact hsp.1 y (knownOf_sub hu hk) e he hne)
    (fun y hy z hz hne hc hr => by
      obtain ⟨u, hu, hk⟩ := hy
      obtain ⟨u', hu', hk'⟩ := hz
      exact hsp.2.1 y (knownOf_sub hu hk) z (knownOf_sub hu' hk') hne hc hr) r

/-- **Under spread evidence, an honest node leaves out only authors of
`D`**, at the state before an event. -/
theorem excluded_before_spread (hsp : Live.Spread cfg H tr D nE) {v : Validator} (hv : v ∈ H)
    (i r : ℕ) :
    excluded (cfg.at v) (stateBefore cfg tr i v).disk r (stateBefore cfg tr i v).evidence ⊆ D := by
  have hE := Converge.evidenceOn_before (cfg := cfg) (tr := tr) v i
  have hV := (Converge.inv_before (cfg := cfg) (tr := tr) i v).valid
  intro a hm
  rcases Finset.mem_union.mp hm with hm | hm
  · obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hm
    obtain ⟨he, hne⟩ := Finset.mem_filter.mp he
    rcases (hE.2 e he).2 with ⟨h₁, h₂, h₃, h₄, h₅⟩ | ⟨c, hc, hce⟩
    · have := hsp.2.1 _ (Converge.stored_known hv h₁) _ (Converge.stored_known hv h₂) hne
        (by simp only; rw [h₃, h₄]) h₅
      simp only at this
      rwa [h₃] at this
    · exact hsp.1 _ (Converge.stored_known hv hc) e hce hne
  · obtain ⟨c, hcR, hcm⟩ := Finset.mem_biUnion.mp hm
    by_contra hD
    exact ex_not_named (A := Dᶜ) hV
      (fun j hj e he hne hc => Finset.mem_compl.mp hc (hsp.1 _ (Converge.stored_known hv hj) e he hne))
      c (Store.mem_atRound.mp hcR).1 _ hcm (Finset.mem_compl.mpr hD)

/-- **Under spread evidence, a block an honest node builds above `nE`
references no author of `D`**: its builder convicted them before the event,
and leaves out the authors it convicted. -/
theorem refs_avoid_spread (hsp : Live.Spread cfg H tr D nE) {i : ℕ} {w : Validator}
    {inp : Input Validator BlockId Payload} {x : State Validator BlockId Payload}
    {ow : Option BlockId} {r : ℕ} (hi : tr[i]? = some (w, inp)) (hw : w ∈ H)
    (hbs : BuildState (cfg.at w) U (knownAll cfg H tr) (stateBefore cfg tr i w) inp x)
    {e : BlockId × Block Validator BlockId Payload} (he : e ∈ persists (outputsAt cfg tr i))
    (her : nE < e.2.round) (ho : ∀ j, ow = some j → (x.disk.blk j).creator = (cfg.at w).me) :
    ∀ k ∈ refsAt (cfg.at w) x.disk r ow x.evidence, (x.disk.blk k).creator ∉ D := by
  intro k hk hD
  obtain ⟨e', he', he'1, hne⟩ := hbs.ev.1 _ (hbs.det (hsp.2.2 i w inp hi hw e he her hD))
  exact refsAt_avoids ho k hk (Finset.mem_union_left _
    (Finset.mem_image.mpr ⟨e', Finset.mem_filter.mpr ⟨he', hne⟩, he'1⟩))

/-- **Under spread evidence, an honest author's block above `nE` lends
references avoiding the authors an honest node leaves out**, at the state
before an event. -/
theorem lent_avoids_before (hσ : cfg.σ = boundedSel) (hadm : cfg.Admissible)
    (hf : Hᶜ.card ≤ cfg.f) (htime : Converge.TimelyAuthentic cfg H tr)
    (hinj : Converge.HashInjective cfg H tr) (time : ℕ → ℕ) (hsp : Live.Spread cfg H tr D nE)
    {v : Validator} (hv : v ∈ H) (E : ℕ) {m : ℕ} {z : BlockId}
    (hz : z ∈ (stateBefore cfg tr E v).disk.ids)
    (hzr : ((stateBefore cfg tr E v).disk.blk z).round = m + 1)
    (hzH : ((stateBefore cfg tr E v).disk.blk z).creator ∈ H) (hmE : nE ≤ m) :
    ∀ k ∈ lent (stateBefore cfg tr E v).disk z, ((stateBefore cfg tr E v).disk.blk k).creator ∉
      excluded (cfg.at v) (stateBefore cfg tr E v).disk m (stateBefore cfg tr E v).evidence := by
  set Z := stateBefore cfg tr E v with hZ
  have hcut := (cut_before hσ hadm hf htime hinj E v hv).1
  have hzU := (hcut _ hz).1
  have hzc : ((globalRecord (hashInjective_of_trace hinj) (authentic_of_timely htime)).block
      z).creator = (Z.disk.blk z).creator := by rw [hcut.eq hz]
  have hzr' : ((globalRecord (hashInjective_of_trace hinj) (authentic_of_timely htime)).block
      z).round = m + 1 := by rw [hcut.eq hz]; exact hzr
  obtain ⟨iw, inpw, xw, oww, hiw, -, hbsw, hshw, -, ⟨-, -, -, -, hew⟩, hzrefs, hzsub, -, -, -⟩ :=
    built_block time hσ hadm hf htime hinj hzH hzU hzc hzr'
  have ho : ∀ j, oww = some j →
      (xw.disk.blk j).creator = (cfg.at (Z.disk.blk z).creator).me := fun j hj => by
    rcases hshw.2.2 with ⟨ht, hoe⟩ | ⟨-, hon, -⟩
    · obtain ⟨j', hj', -, -, hjc⟩ := hbsw.own m ht
      rw [hoe, hj'] at hj
      cases hj
      exact hjc
    · rw [hon] at hj; cases hj
  have hAD := refs_avoid_spread (r := m) hsp hiw hzH hbsw hew (by rw [hzr']; omega) ho
  intro k hk hmk
  have hk' : k ∈ refsAt (cfg.at (Z.disk.blk z).creator) xw.disk m oww xw.evidence := by
    rw [← hzrefs, hcut.eq hz]; exact hk
  have hkZ : k ∈ Z.disk.ids := Z.disk.complete z hz k hk
  have hcr : (Z.disk.blk k).creator = (xw.disk.blk k).creator := by
    rw [← hcut.eq hkZ, ← hbsw.cut.eq (hzsub hk')]
  exact hAD k hk' (hcr ▸ excluded_before_spread hsp hv E m hmk)

/-- **A store with more than `f` authors of a round holds an honest
author's block of it.** -/
theorem exists_honest_at (hf : Hᶜ.card ≤ cfg.f) {st : Store Validator BlockId Payload} {r : ℕ}
    (h : cfg.f + 1 ≤ (st.authorsAt r).card) :
    ∃ z ∈ st.ids, (st.blk z).round = r ∧ (st.blk z).creator ∈ H := by
  obtain ⟨a, ha, haH⟩ : ∃ a ∈ st.authorsAt r, a ∈ H := by
    by_contra hno
    push Not at hno
    have hsub : st.authorsAt r ⊆ Hᶜ := fun a ha => Finset.mem_compl.mpr (hno a ha)
    have := Finset.card_le_card hsub
    omega
  obtain ⟨z, hzR, hza⟩ := mem_creatorsOf.mp ha
  obtain ⟨hz, hzr⟩ := Store.mem_atRound.mp hzR
  exact ⟨z, hz, hzr, hza ▸ haH⟩

end Spread

section Catch

variable {T : Finset Validator} {tr : Trace Validator BlockId Payload} {time : ℕ → ℕ}
  {gst Δ Δₛ t₁ : ℕ}

omit [Fintype Validator] in
/-- **A valid block's references**: `q` distinct authors, none twice, read
on the store it was built on. -/
theorem refs_of_rowValid {st : Store Validator BlockId Payload} {id : BlockId}
    {b : Block Validator BlockId Payload} (hnew : id ∉ st.ids) (hrefs : b.refs ⊆ st.ids)
    (hr : 0 < b.round) (hv : rowValid cfg.q cfg.xp (Function.update st.blk id b) b) :
    cfg.q ≤ (creatorsOf st.blk b.refs).card ∧
      ∀ i ∈ b.refs, ∀ j ∈ b.refs, (st.blk i).creator = (st.blk j).creator → i = j := by
  have hne : ∀ j ∈ b.refs, Function.update st.blk id b j = st.blk j := fun j hj =>
    Function.update_of_ne (fun h : j = id => hnew (h ▸ hrefs hj)) _ _
  refine ⟨?_, fun i hi j hj hij => hv.clause.1 i hi j hj (by rw [hne i hi, hne j hj]; exact hij)⟩
  have hq := hv.quorum hr
  simp only [creators, creatorsOf] at hq ⊢
  rwa [Finset.image_congr (g := fun i => (st.blk i).creator) (fun j hj => by
    simp only; rw [hne j hj])] at hq

/-- **A block an honest node holds of an honest author was persisted by
its author** at an earlier event. -/
theorem persisted_of_stored (htime : Converge.TimelyAuthentic cfg H tr) {v w : Validator}
    (hv : v ∈ H) (hw : w ∈ H) {K : ℕ} {z : BlockId} (hz : z ∈ (stateBefore cfg tr K v).disk.ids)
    (hzc : ((stateBefore cfg tr K v).disk.blk z).creator = w) :
    ∃ j < K, ∃ inp, tr[j]? = some (w, inp) ∧
      (z, (stateBefore cfg tr K v).disk.blk z) ∈ persists (outputsAt cfg tr j) := by
  have hk := (Converge.inv_before (cfg := cfg) (tr := tr) K v).known z hz
  have hp := own_known (v := w) htime hv hw le_rfl hk hzc
  obtain ⟨j, hj, hjw, hjz⟩ := mem_persists_before (cfg := cfg) w K hp
  obtain ⟨inp, hj'⟩ := Converge.event_of_map hjw
  exact ⟨j, hj, inp, hj', hjz⟩

/-- **A quorum exceeds twice the Byzantine faults and the crash faults**:
`2f + c + 1 ≤ q` on every admissible row, since a commit's threshold
leaves room for neither. -/
theorem two_f_c_lt_q (hadm : cfg.Admissible) : 2 * cfg.f + cfg.c + 1 ≤ cfg.q := by
  obtain ⟨hcov, -, hct, hq0, hqn⟩ := hadm
  unfold Scheme.Params.Covered Scheme.Params.TwoRound Scheme.Params.ThreeRound
    Scheme.Params.TwoRoundCrash Scheme.Params.ThreeRoundCrash at hcov
  rcases hcov with ⟨-, -, hl, -, -, h⟩ | ⟨-, -, -, -, -, h⟩ | ⟨-, -, hl, hf0, -, h⟩ |
    ⟨-, -, -, -, hf0, -, h⟩ <;> omega

/-- **A quorum has `f + 1` reliable authors**: at most `f + c` validators
are outside the `n − f − c` reliable ones. -/
theorem quorum_reliable (hadm : cfg.Admissible)
    (hcT : Fintype.card Validator - cfg.f - cfg.c ≤ T.card) {A : Finset Validator}
    (hq : cfg.q ≤ A.card) : cfg.f + 1 ≤ (A.filter (· ∈ T)).card := by
  have h2f := two_f_c_lt_q hadm
  have hsub : A ⊆ A.filter (· ∈ T) ∪ Tᶜ := fun a ha => by
    by_cases haT : a ∈ T
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨ha, haT⟩)
    · exact Finset.mem_union_right _ (Finset.mem_compl.mpr haT)
  have := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  rw [Finset.card_compl] at this
  have := T.card_le_univ
  omega

/-- **A node behind a round holds an earlier honest block of it**: one of
the `f + 1` authors of round `n + 1` it holds is honest, is not the node,
and persisted the block at an earlier event. -/
theorem behind_honest (htime : Converge.TimelyAuthentic cfg H tr)
    (hinj : Converge.HashInjective cfg H tr) (hf : Hᶜ.card ≤ cfg.f) {w : Validator} (hw : w ∈ H)
    {i : ℕ} {inp : Input Validator BlockId Payload} (hi : tr[i]? = some (w, inp))
    {x y : State Validator BlockId Payload} {o : List (Output Validator BlockId Payload)}
    {e : BlockId × Block Validator BlockId Payload} {n : ℕ}
    (hx : BuildState (cfg.at w) (globalRecord (hashInjective_of_trace hinj)
      (authentic_of_timely htime)) (knownAll cfg H tr) (stateBefore cfg tr i w) inp x)
    (hb : tryBuild (cfg.at w) x = some (y, o)) (heo : e ∈ persists o)
    (he : e ∈ persists (outputsAt cfg tr i)) (her : e.2.round = n + 1)
    (hgx : Grows x.disk (stateBefore cfg tr (i + 1) w).disk)
    (hbeh : behind (cfg.at w) x.disk n) :
    ∃ w' ∈ H, w' ≠ w ∧ ∃ j < i, ∃ inp' z, tr[j]? = some (w', inp') ∧
      z ∈ persists (outputsAt cfg tr j) ∧ z.2.round = n + 1 ∧ z.1 ∈ x.disk.ids ∧
      x.disk.blk z.1 = z.2 := by
  -- an honest author of round `n + 1`
  obtain ⟨w', hw'A, hw'T⟩ : ∃ w' ∈ x.disk.authorsAt (n + 1), w' ∈ H := by
    by_contra h
    push_neg at h
    have hsub : x.disk.authorsAt (n + 1) ⊆ Hᶜ := fun a ha => Finset.mem_compl.mpr (h a ha)
    have := Finset.card_le_card hsub
    change cfg.f + 1 ≤ _ at hbeh
    omega
  obtain ⟨z, hzR, hzc⟩ := mem_creatorsOf.mp hw'A
  have hz : z ∈ x.disk.ids ∧ (x.disk.blk z).round = n + 1 := by
    rw [Store.atRound_eq] at hzR
    simpa [blocksAt, Store.toRecord] using hzR
  obtain ⟨B, hiX⟩ := hx.inv
  have hzK : (z, x.disk.blk z) ∈ knownAll cfg H tr := hiX.known z hz.1
  -- it is not the node: its round-`n + 1` block is the one it builds, not yet on disk
  have hww : w' ≠ w := by
    rintro rfl
    obtain ⟨r, id, b, hnew, -, -, hxt', hbr, -, -, -, -, -, -, -, hout⟩ := tryBuild_some hb
    rw [hout, persists_built, List.mem_singleton] at heo
    subst heo
    have hzp := mem_persists_of_known (hashInjective_of_trace hinj) (authentic_of_timely htime)
      hzK (by change (x.disk.blk z).creator ∈ H; rw [hzc]; exact hw)
    have hep : (id, b) ∈ persists (runOf cfg tr w').2 :=
      mem_persists_iff.mpr (mem_outputs_of_event hi (mem_persists_iff.mp he))
    change (z, x.disk.blk z).2.creator = w' at hzc
    rw [hzc] at hzp
    have := eq_of_persists w' hzp hep
      (by change (x.disk.blk z).round = b.round; rw [hz.2]; exact her.symm)
    exact hnew (by rw [← (Prod.mk.inj this).1]; exact hz.1)
  -- it persisted the block before the event
  have hzF := hgx.1 hz.1
  have hk := (Converge.inv_before (cfg := cfg) (tr := tr) (i + 1) w).known z hzF
  rw [hgx.blk hz.1] at hk
  have hp := own_known htime hw hw'T le_rfl hk hzc
  obtain ⟨j, hj, hjw', hjz⟩ := mem_persists_before (cfg := cfg) w' (i + 1) hp
  have hji : j ≠ i := by
    rintro rfl
    rw [hi] at hjw'
    exact hww (Option.some.inj hjw').symm
  obtain ⟨inp', hj'⟩ := Converge.event_of_map hjw'
  exact ⟨w', hw'T, hww, j, by omega, inp', (z, x.disk.blk z), hj', hjz, hz.2, hz.1, rfl⟩

/-- **A reliable block of round `m + 1` that a node holds brings a quorum
of round `m`**: its references, `q` authors, are held with it. -/
theorem quorum_of_held (hσ : cfg.σ = boundedSel) (hadm : cfg.Admissible) (hf : Hᶜ.card ≤ cfg.f)
    (htime : Converge.TimelyAuthentic cfg H tr) (hinj : Converge.HashInjective cfg H tr)
    {v w : Validator} (hv : v ∈ H) (hw : w ∈ H) {i : ℕ} {inp : Input Validator BlockId Payload}
    (hi : tr[i]? = some (w, inp)) {e : BlockId × Block Validator BlockId Payload}
    (he : e ∈ persists (outputsAt cfg tr i)) {m : ℕ} (her : e.2.round = m + 1) {E : ℕ}
    (hin : e.1 ∈ (stateBefore cfg tr E v).disk.ids)
    (hblk : (stateBefore cfg tr E v).disk.blk e.1 = e.2) :
    cfg.q ≤ (authorsIn (stateBefore cfg tr E v).disk.toRecord
      (stateBefore cfg tr E v).disk.ids m).card := by
  set Z := stateBefore cfg tr E v with hZ
  have hZcut := (cut_before hσ hadm hf htime hinj E v hv).1
  obtain ⟨x, y, out, hbs, hb, heo, -⟩ := build_witness hσ hadm hf htime hinj hw hi he (by omega)
  obtain ⟨r', id, b, hnew, hrefs, -, -, hbr, -, -, hrv, -, -, -, -, hout'⟩ := tryBuild_some hb
  rw [hout', persists_built, List.mem_singleton] at heo
  subst heo
  simp only at her hin hblk
  obtain ⟨hRq, -⟩ := refs_of_rowValid (cfg := cfg.at w) hnew hrefs (by omega) hrv
  have hRZ : ∀ j ∈ b.refs, j ∈ Z.disk.ids ∧ (Z.disk.blk j).round = m := fun j hj => by
    have hj' : j ∈ (Z.disk.blk id).refs := by rw [hblk]; exact hj
    have := Z.disk.pred id hin j hj'
    change (Z.disk.blk j).round + 1 = (Z.disk.blk id).round at this
    rw [hblk, her] at this
    exact ⟨Z.disk.complete id hin j hj', by omega⟩
  have hcre : creatorsOf Z.disk.blk b.refs = creatorsOf x.disk.blk b.refs :=
    Finset.image_congr fun j hj => by
      rw [← hZcut.creator (hRZ j hj).1, hbs.cut.creator (hrefs hj)]
  refine le_trans hRq (le_trans (le_of_eq (congrArg Finset.card hcre.symm))
    (Finset.card_le_card fun a ha => ?_))
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp ha
  exact mem_authorsIn.mpr ⟨j, (hRZ j hj).1, (hRZ j hj).2, rfl⟩

/-- **A held block brings a quorum of each round below it**: its
references, `q` authors of the round below, are held with it, and one of
them leads further down. -/
theorem quorum_below (hσ : cfg.σ = boundedSel) (hadm : cfg.Admissible) (hf : Hᶜ.card ≤ cfg.f)
    (htime : Converge.TimelyAuthentic cfg H tr) (hinj : Converge.HashInjective cfg H tr)
    {v : Validator} (hv : v ∈ H) (E : ℕ) :
    ∀ (k : ℕ) {j : BlockId}, j ∈ (stateBefore cfg tr E v).disk.ids →
      ((stateBefore cfg tr E v).disk.blk j).round = k → ∀ r < k,
      cfg.q ≤ (authorsIn (stateBefore cfg tr E v).disk.toRecord
        (stateBefore cfg tr E v).disk.ids r).card := by
  set Z := (stateBefore cfg tr E v).disk with hZ
  have hcut := (cut_before hσ hadm hf htime hinj E v hv).1
  intro k
  induction k with
  | zero => intro j _ _ r hr; omega
  | succ k ih =>
    intro j hj hjr r hr
    obtain ⟨hjU, hjb⟩ := hcut j hj
    have hq := ((globalRecord (hashInjective_of_trace hinj)
      (authentic_of_timely htime)).valid j hjU).quorum (by rw [hjb, hjr]; omega)
    -- the references are held, one round below
    have hrefs : ∀ i ∈ (Z.blk j).refs, i ∈ Z.ids ∧ (Z.blk i).round = k := fun i hi => by
      have := Z.pred j hj i hi
      change (Z.blk i).round + 1 = (Z.blk j).round at this
      exact ⟨Z.complete j hj i hi, by omega⟩
    have hcre : creators (globalRecord (hashInjective_of_trace hinj)
        (authentic_of_timely htime)).block ((globalRecord (hashInjective_of_trace hinj)
        (authentic_of_timely htime)).block j) = creatorsOf Z.blk (Z.blk j).refs := by
      unfold creators
      rw [hjb]
      exact Finset.image_congr fun i hi => by rw [(hcut i (hrefs i hi).1).2]
    rw [hcre] at hq
    by_cases hrk : r = k
    · subst hrk
      refine hq.trans (Finset.card_le_card fun a ha => ?_)
      obtain ⟨i, hi, rfl⟩ := mem_creatorsOf.mp ha
      exact mem_authorsIn.mpr ⟨i, (hrefs i hi).1, (hrefs i hi).2, rfl⟩
    · obtain ⟨i, hi⟩ : (Z.blk j).refs.Nonempty := by
        by_contra hne
        rw [Finset.not_nonempty_iff_eq_empty] at hne
        rw [hne] at hq
        have := hadm.2.2.2.1
        simp [creatorsOf] at hq
        omega
      exact ih (hrefs i hi).1 (hrefs i hi).2 r (by omega)

/-- **A reliable node has started** at any time from GST on. -/
theorem started_at (hadm : cfg.Admissible) (hfa : cfg.Faithful) (hid : Function.Injective cfg.idOf)
    (htime : Converge.TimelyAuthentic cfg H tr) (hTH : T ⊆ H)
    (hmono : Live.TimeMono tr time) (hstart : Live.StartedBy T tr time gst) {v : Validator}
    (hv : v ∈ T) {τ : ℕ} (hτ : gst ≤ τ) : (stateAt cfg tr time v τ).top.isSome := by
  obtain ⟨st, hst, htst⟩ := hstart v hv
  have hstl : st < tr.length := (List.getElem?_eq_some_iff.mp hst).1
  have hstE : st + 1 ≤ eventsBy tr time τ := (lt_eventsBy hmono hstl).mpr (by omega)
  exact (rises_before (cfg := cfg) v hstE).2.1
    (started_after hadm hfa hid htime (hTH hv) hst)

/-- **Catch-up**: past GST, once `f + 1` reliable nodes are at round `n`
or above at `τ`, every reliable node is at `n` or above at `τ + A`. Their
top blocks arrive, so the node is behind the round above its top, with a
quorum of its top round, and builds it. -/
theorem catches_up (hq : 2 ≤ cfg.q) (hσ : cfg.σ = boundedSel)
    (hadm : cfg.Admissible) (hfa : cfg.Faithful) (hf : Hᶜ.card ≤ cfg.f) (hid : Function.Injective
        cfg.idOf)
    (htime : Converge.TimelyAuthentic cfg H tr) (hinj : Converge.HashInjective cfg H tr)
    (hTH : T ⊆ H) (hmono : Live.TimeMono tr time)
    (harr : Arrival cfg T tr time gst (Δ + Δₛ) t₁) (hstart : Live.StartedBy T tr time gst)
    {S : Finset Validator} (hST : S ⊆ T) (hS : cfg.f + 1 ≤ S.card) {τ n : ℕ} (hgτ : gst ≤ τ)
    (hτ₁ : τ + (Δ + Δₛ) ≤ t₁)
    (hSn : ∀ w ∈ S, (stateAt cfg tr time w τ).top.isSome ∧ n ≤ topAt cfg tr time w τ)
    {D : Finset Validator} {nE : ℕ} (hsp : Live.Spread cfg H tr D nE)
    {v : Validator} (hv : v ∈ T) (hvE : nE ≤ topAt cfg tr time v gst) :
    n ≤ topAt cfg tr time v (τ + (Δ + Δₛ)) := by
  set E := eventsBy tr time (τ + (Δ + Δₛ)) with hE
  by_contra hlt
  obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp
    (started_at hadm hfa hid htime hTH hmono hstart hv (τ := τ + (Δ + Δₛ)) (by omega))
  change (stateBefore cfg tr E v).top = some m at hm
  have hmn : m + 1 ≤ n := by
    change ¬ n ≤ (stateBefore cfg tr E v).top.getD 0 at hlt
    rw [hm] at hlt
    simp only [Option.getD_some] at hlt
    omega
  set Z := stateBefore cfg tr E v with hZ
  have hSet : Settled (cfg.at v) Z := by
    rcases settled_before (cfg := cfg) hq v E with h | h
    · rw [hm] at h; cases h
    · exact h
  have hvS : v ∉ S := fun hvS =>
    hlt ((hSn v hvS).2.trans (rises_before (cfg := cfg) (tr := tr) v (eventsBy_mono
      (tr := tr) (time := time) (show τ ≤ τ + (Δ + Δₛ) by omega))).1)
  -- each of their top blocks arrives
  have htops : ∀ w ∈ S, ∃ j ∈ Z.disk.ids, (Z.disk.blk j).round = topAt cfg tr time w τ ∧
      (Z.disk.blk j).creator = w := fun w hw =>
    top_arrives htime hinj hTH hmono harr (hST hw) hv (ne_of_mem_of_not_mem hw hvS) hgτ
      (hSn w hw).1 le_rfl hτ₁
  -- one of them brings a quorum of round `m`
  obtain ⟨w₀, hw₀⟩ : S.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨j₀, hj₀, hj₀r, -⟩ := htops w₀ hw₀
  have hcard := quorum_below hσ hadm hf htime hinj (hTH hv) E _ hj₀ hj₀r m
    (by have := (hSn w₀ hw₀).2; omega)
  -- and they are `f + 1` authors of round `m + 1`, or one is above it
  have hbeh : behind (cfg.at v) Z.disk m := by
    change cfg.f + 1 ≤ (Z.disk.authorsAt (m + 1)).card
    rw [Store.authorsAt_eq]
    by_cases hup : ∃ w ∈ S, m + 1 < topAt cfg tr time w τ
    · obtain ⟨w, hw, hwm⟩ := hup
      obtain ⟨j, hj, hjr, -⟩ := htops w hw
      have h₁ := quorum_below hσ hadm hf htime hinj (hTH hv) E _ hj hjr (m + 1) hwm
      have h₂ := two_f_c_lt_q hadm
      exact (show cfg.f + 1 ≤ cfg.q by omega).trans h₁
    · push Not at hup
      refine hS.trans (Finset.card_le_card fun w hw => ?_)
      obtain ⟨j, hj, hjr, hjc⟩ := htops w hw
      have hwm : topAt cfg tr time w τ = m + 1 :=
        le_antisymm (hup w hw) ((hSn w hw).2.trans' hmn)
      exact mem_authorsIn.mpr ⟨j, hj, hjr.trans hwm, hjc⟩
  obtain ⟨o, hoo, hoi, hor, hoc⟩ := ownTop_before (cfg := cfg) (tr := tr) (v := v) E m hm
  -- an honest author's round-`m + 1` block it holds lends references
  have hmE : nE ≤ m := by
    have := (rises_before (cfg := cfg) (tr := tr) v (eventsBy_mono (tr := tr) (time := time)
      (show gst ≤ τ + (Δ + Δₛ) by omega))).1
    change topAt cfg tr time v gst ≤ (stateBefore cfg tr E v).top.getD 0 at this
    rw [hm] at this
    simp only [Option.getD_some] at this
    omega
  obtain ⟨z, hzZ, hzr, hzH⟩ := exists_honest_at hf (show cfg.f + 1 ≤ _ from hbeh)
  have hzm : (Z.disk.blk z).creator ≠ (cfg.at v).me := fun h => by
    have h₁ : (Z.disk.blk z).round ≤ m := own_le_top htime (hTH hv) hm hzZ h
    have h₂ : (Z.disk.blk z).round = m + 1 := hzr
    omega
  have hav := lent_avoids_before hσ hadm hf htime hinj time hsp (hTH hv) E hzZ hzr hzH hmE
  have hsome := tryBuild_isSome (cfg := cfg.at v) hm
    (harr.recovered (by omega) v hv E (eventsBy_mono (tr := tr) (time := time) (by omega))
      (eventsBy_mono (by omega)))
    (Or.inr hbeh) hcard
    (fun j hj => by rw [hoo] at hj; cases hj; exact ⟨hoi, hor, hoc⟩)
    (Or.inr ⟨_, lent_mem_lents hzZ hzr hzm hav, (lent_buildable (cfg := cfg.at v)
      (Converge.inv_before (cfg := cfg) (tr := tr) E v).valid hzZ hzr hfa
      (fresh_before hid htime (hTH hv) hm) _).2⟩)
    (fresh_before hid htime (hTH hv) hm) ((Converge.floor_before hm).trans (Nat.sub_le _ _))
  rw [hSet.build] at hsome
  cases hsome

end Catch

/-! ## Build times -/

section Built

variable {T : Finset Validator} {tr : Trace Validator BlockId Payload} {time : ℕ → ℕ}

/-- A node at a round built it by then. -/
theorem builtAt_le_of_top {v : Validator}
    (hmono : Live.TimeMono tr time) {τ n : ℕ} (hs : (stateAt cfg tr time v τ).top.isSome)
    (hn : n ≤ topAt cfg tr time v τ)
    (hj : ∀ k < eventsBy tr time τ, ∀ inp, tr[k]? = some (v, inp) →
      ((stateBefore cfg tr k v).recovering = true ∨ inp = .restart) →
      (stateBefore cfg tr (k + 1) v).top.getD 0 < n) : builtAt cfg tr time v n ≤ τ := by
  obtain ⟨i, -, -, -, -, -, hbt, hiτ⟩ := built_of_top hmono hs hn hj
  omega

end Built

end Node

end LeanDag
