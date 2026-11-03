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

omit [Fintype Validator] in
/-- **A record path is a store path**, from a block at or above `G` down to
one at or above `G`, when the store is read as the record reads it from `G`
up and keeps every block from the round of the path's end up with its
references. -/
theorem AllGood.reachesFrom_store [P.Mechanised] {G : ℕ} (hc : AllGood (CutAbove U G) st)
    {i : BlockId} (hiG : G ≤ (U.block i).round)
    (hk : ∀ a ∈ st.ids, (U.block i).round ≤ (st.blk a).round → st.kept[a]? = none) :
    ∀ {j : BlockId}, j ∈ st.ids → G ≤ (st.full j).round →
      ReachesFrom U.block j i → ReachesFrom st.blk j i := by
  intro j hj hjG h
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ReachesFrom.refl
  | @head a c hstep hrest ih =>
    have hstep : c ∈ (U.block a).refs := hstep
    obtain ⟨haU, har, -, hab⟩ := hc a hj hjG
    have hci := round_le_of_reaches (U.complete a haU c hstep) hrest
    have hcr := Validity.Mechanised.pred _ _ (U.valid a haU) c hstep
    have hGa : G < (st.full a).round := by rw [← har]; omega
    have hka : st.kept[a]? = none := hk a hj (by rw [← (st.full_fields a).1]; omega)
    have hcs : c ∈ (st.blk a).refs := by
      rw [← st.full_of_kept_none hka, ← hab hGa]; exact hstep
    have hcst := st.complete a hj c hcs
    have hcG : G ≤ (st.full c).round := by
      have := st.pred a hj c hcs
      change (st.blk c).round + 1 = (st.blk a).round at this
      rw [(st.full_fields c).1]; rw [(st.full_fields a).1] at hGa; omega
    exact Relation.ReflTransGen.head hcs (ih hcst hcG)

omit [Fintype Validator] in
/-- **A store holds a record path's short history**: a block that a block of
the store reaches in the record, at most `m` rounds below it, lies within `m`
steps of it in the store, when both lie at or above `G`, the store is read as
the record reads it from `G` up, and it keeps every block from the round of
the end up with its references. -/
theorem AllGood.mem_historyUptoFrom [P.Mechanised] {G : ℕ} (hc : AllGood (CutAbove U G) st)
    {j i : BlockId} {m : ℕ} (hiG : G ≤ (U.block i).round)
    (hk : ∀ a ∈ st.ids, (U.block i).round ≤ (st.blk a).round → st.kept[a]? = none)
    (hj : j ∈ st.ids) (hjG : G ≤ (st.full j).round)
    (hm : (U.block j).round ≤ m + (U.block i).round) (h : ReachesFrom U.block j i) :
    i ∈ historyUptoFrom st.blk m j := by
  classical
  obtain ⟨hi, hiG'⟩ := hc.down_above hiG hk le_rfl hj hjG h
  exact mem_historyUptoFrom_of_round st.toRecord.causal hj
    (by change (st.blk j).round ≤ m + (st.blk i).round
        rw [← (st.full_fields j).1, ← (st.full_fields i).1, ← (hc j hj hjG).2.1,
          ← (hc i hi hiG').2.1]; exact hm)
    (hc.reachesFrom_store hiG hk hj hjG h)

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
to another holding the superset, and to a superset of the leaders left
out: the leader blocks the tests read are reached from the references, so
the second cut holds them. -/
theorem ready_transfer [P.Mechanised] (hσ : cfg.σ = boundedSel)
    (hct : cfg.p.voteIsCert = false → 1 ≤ cfg.p.certThreshold) {G : ℕ}
    {x Z : Store Validator BlockId Payload} (hx : AllGood (CutAbove U G) x)
    (hZ : AllGood (CutAbove U G) Z) {R R' : Finset BlockId} {n : ℕ}
    (hG : G ≤ n - cfg.p.voteOffset) (hR : R ⊆ x.ids) (hRR : R ⊆ R') (hR'Z : R' ⊆ Z.ids)
    (hkx : ∀ a ∈ x.ids, n - cfg.p.voteOffset ≤ (x.blk a).round → x.kept[a]? = none)
    (hkZ : ∀ a ∈ Z.ids, n - cfg.p.voteOffset ≤ (Z.blk a).round → Z.kept[a]? = none)
    (hRn : ∀ b ∈ R, (x.blk b).round = n) (hRZ : ∀ b ∈ R, (Z.blk b).round = n)
    {X X' : Finset Validator} (hXX : X ⊆ X')
    (hreach : reachReady cfg x R n X = true) (hcert : certReady cfg x R n X = true) :
    reachReady cfg Z R' n X' = true ∧ certReady cfg Z R' n X' = true := by
  have hZG : ∀ c ∈ R, G ≤ (Z.full c).round := fun c hc => by
    rw [(Z.full_fields c).1, hRZ c hc]; omega
  -- a candidate of the store `x` reached from a reference
  have hcand : ∀ k L, L ∈ candidatesIn (S := cfg.slots) x.toRecord x.view k →
      n - cfg.p.voteOffset ≤ (x.blk L).round →
      ∀ c ∈ R, ReachesFrom U.block c L →
      L ∈ candidatesIn (S := cfg.slots) Z.toRecord Z.view k ∧ L ∈ Z.ids := by
    intro k L hL hLn c hc hcL
    obtain ⟨hLx, hLc, hLr⟩ := Finset.mem_filter.mp hL
    have hLG : G ≤ (x.blk L).round := hG.trans hLn
    have hLU : n - cfg.p.voteOffset ≤ (U.block L).round := by
      rw [hx.above_round hLx hLG]; exact hLn
    obtain ⟨hLZ, hLZG⟩ := hZ.down_above hG hkZ hLU (hR'Z (hRR hc)) (hZG c hc) hcL
    have hLZG' : G ≤ (Z.blk L).round := by rw [← (Z.full_fields L).1]; exact hLZG
    refine ⟨Finset.mem_filter.mpr ⟨hLZ, ?_, ?_⟩, hLZ⟩
    · change (Z.blk L).creator = _
      rw [← hZ.above_creator hLZ hLZG', hx.above_creator hLx hLG]; exact hLc
    · change (Z.blk L).round = _
      rw [← hZ.above_round hLZ hLZG', hx.above_round hLx hLG]; exact hLr
  constructor
  · unfold reachReady at hreach ⊢
    simp only [Store.leaderBlocks_eq] at hreach ⊢
    refine List.all_eq_true.mpr fun m hm => ?_
    have h₁ := List.all_eq_true.mp hreach m hm
    by_cases hmn : m ≤ n
    · rw [if_pos hmn] at h₁ ⊢
      refine List.all_eq_true.mpr fun k hk => ?_
      have h₂ := List.all_eq_true.mp h₁ k hk
      rcases of_decide_eq_true h₂ with hkX | ⟨L, hL, c, hc, hhist⟩
      · exact decide_eq_true (Or.inl (hXX hkX))
      have hLx := (Finset.mem_filter.mp hL).1
      have hmv : m < cfg.p.voteOffset := List.mem_range.mp hm
      have hLr' : (x.blk L).round = n - m := by
        change (x.toRecord.block L).round = _
        rw [(Finset.mem_filter.mp hL).2.2]
        exact slotRound_of_mem_slotsAt hk
      have hLG : G ≤ (x.blk L).round := by omega
      have hLr : (U.block L).round = n - m := by rw [hx.above_round hLx hLG, hLr']
      have hcx := hR hc
      have hrd := round_le_of_mem_historyUptoFrom x.toRecord m hcx hhist
      change (x.blk c).round ≤ m + (x.blk L).round at hrd
      have hcL : ReachesFrom U.block c L :=
        hx.reachesFrom hLG hcx (reaches_of_mem_historyUptoFrom hhist)
      obtain ⟨hLZ, -⟩ := hcand k L hL (by omega) c hc hcL
      refine decide_eq_true (Or.inr ⟨L, hLZ, c, hRR hc,
        hZ.mem_historyUptoFrom (by rw [hLr]; omega) (fun a ha har => hkZ a ha (by omega))
          (hR'Z (hRR hc)) (hZG c hc) ?_ hcL⟩)
      rw [hx.above_round hcx (by rw [hRn c hc]; omega), hx.above_round hLx hLG]; exact hrd
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
        rcases of_decide_eq_true h₂ with hkX | ⟨L, hL, hcount⟩
        · exact decide_eq_true (Or.inl (hXX hkX))
        have hLx := (Finset.mem_filter.mp hL).1
        -- the votes, read on the record
        have hLr : (x.blk L).round = n - cfg.p.voteOffset := by
          change (x.toRecord.block L).round = _
          rw [(Finset.mem_filter.mp hL).2.2]
          exact slotRound_of_mem_slotsAt hk
        have hvax := hx.viewsAbove (R := n - cfg.p.voteOffset) hG hkx
        have hvx : ∀ b ∈ R, (cfg.σ.Votes x.toRecord b L ↔
            (boundedSel : VoteSel Validator BlockId Payload P H).Votes U b L) := by
          intro b hb
          rw [hσ]
          exact hvax.votes_iff (hR hb) (by change _ ≤ (x.blk b).round; rw [hRn b hb]; omega)
            hLx (by change _ ≤ (x.blk L).round; rw [hLr])
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
        have hbL : ReachesFrom U.block b L :=
          (mem_history_iff (hx.above_mem (hR hbR) (by rw [hRn b hbR]; omega))).mp hLh
        obtain ⟨hLZ, hLZi⟩ := hcand k L hL (by rw [hLr]) b hbR hbL
        have hvaZ := hZ.viewsAbove (R := n - cfg.p.voteOffset) hG hkZ
        refine decide_eq_true (Or.inr ⟨L, hLZ, le_trans hcount
          (Finset.card_le_card fun a ha => ?_)⟩)
        obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
        obtain ⟨hbR, hbv⟩ := Finset.mem_filter.mp hb
        have hbZ := hR'Z (hRR hbR)
        have hvZ : cfg.σ.Votes Z.toRecord b L := by
          rw [hσ]
          exact (hvaZ.votes_iff hbZ
            (by change _ ≤ (Z.blk b).round; rw [hRZ b hbR]; omega)
            hLZi (by
              change _ ≤ (Z.toRecord.block L).round
              rw [(Finset.mem_filter.mp hLZ).2.2, slotRound_of_mem_slotsAt hk])).mpr
            ((hvx b hbR).mp hbv)
        refine Finset.mem_image.mpr ⟨b, Finset.mem_filter.mpr ⟨hRR hbR, hvZ⟩, ?_⟩
        rw [← hZ.above_creator hbZ (by rw [hRZ b hbR]; omega),
          hx.above_creator (hR hbR) (by rw [hRn b hbR]; omega)]
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
    (hready : reachReady cfg st (lent st c) r (excluded cfg st r E) = true ∧
      certReady cfg st (lent st c) r (excluded cfg st r E) = true)
    (hb : buildable cfg st r (lent st c) E = true)
    (hav : ∀ i ∈ lent st c, (st.blk i).creator ∉ excluded cfg st r E) :
    reachReady cfg st (refsAt cfg st r o E) r (excluded cfg st r E) = true ∧
      certReady cfg st (refsAt cfg st r o E) r (excluded cfg st r E) = true := by
  unfold refsAt
  dsimp only
  split
  · rename_i h
    simp only [Bool.and_eq_true] at h
    exact h.1
  · have hs : ((lents cfg st r E).find? fun R => (reachReady cfg st R r (excluded cfg st r E) &&
        certReady cfg st R r (excluded cfg st r E)) && buildable cfg st r R E).isSome :=
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
theorem lent_buildable {Z : Store Validator BlockId Payload} {n : ℕ}
    (hZ : UpperValid cfg.q cfg.xp (n + 1) Z) {z : BlockId} (hzZ : z ∈ Z.ids)
    (hzr : (Z.blk z).round = n + 1)
    (hkz : Z.kept[z]? = none)
    (hfa : cfg.Faithful) (hfresh : ∀ (P : Payload) R, cfg.idOf ⟨n + 1, cfg.me, R, P⟩ ∉ Z.ids)
    (E : Finset (Validator × BlockId × BlockId))
    (hbk : ∀ j ∈ Z.ids, (Z.blk j).round = n → cfg.xp.ex (Z.blk j).payload ⊆ named E) :
    lent Z z ⊆ Z.ids ∧ buildable cfg Z n (lent Z z) E = true := by
  have hv := (hZ z hzZ (by rw [hzr])).2
  rw [Z.full_of_kept_none hkz] at hv
  refine ⟨fun j hj => Z.complete z hzZ j hj, lent_buildable_of E hfa hbk hzZ hzr
    (rowValid_congr (fun j _ => ?_) hv) (hfresh _ _)⟩
  have := Z.full_fields j
  exact ⟨this.1, this.2.1, this.2.2⟩

/-! ## Rounds and build times along a trace -/

section Trace

variable {tr : Trace Validator BlockId Payload} {v : Validator}

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
theorem built_of_top {τ n : ℕ}
    (hs : (stateAt cfg tr time v τ).top.isSome)
    (hn : n ≤ topAt cfg tr time v τ)
    (hj : ∀ k < eventsBy tr time τ, ∀ inp, tr[k]? = some (v, inp) →
      Skips (cfg.at v) (stateBefore cfg tr k v) inp (stateBefore cfg tr (k + 1) v) →
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

/-- **A reliable node's block is in a base's record**, at its round and by
its author, when it lies at the base's round or above and stays on the
node's disk after the event: that disk is read as the record reads it. -/
theorem built_mem {R : BlockRecord Validator BlockId Payload (ValidAt cfg.q Clause.none) H}
    {B E₀ E₁ : ℕ} (hbase : Base cfg H tr R B E₀ E₁) {v : Validator} (hv : v ∈ H) {p : ℕ}
    {inp : Input Validator BlockId Payload} (hp : tr[p]? = some (v, inp))
    {e : BlockId × Block Validator BlockId Payload} (he : e ∈ persists (outputsAt cfg tr p))
    (hp₁ : p + 1 ≤ E₁) (hB : B ≤ e.2.round)
    (hkeep : cfg.drops = false ∨ (stateBefore cfg tr (p + 1) v).floor ≤ e.2.round) :
    e.1 ∈ R.ids ∧ (R.block e.1).round = e.2.round ∧ (R.block e.1).creator = v := by
  have hgood := ((Converge.inv_before (cfg := cfg) (tr := tr) (p + 1) v).good e
    (persists_of_event hp he)).2.1
  obtain ⟨hin, hfull⟩ := Converge.persist_stored hp he (Nat.lt_succ_self p) hkeep
  have hr : B ≤ ((stateBefore cfg tr (p + 1) v).disk.full e.1).round := by rw [hfull]; exact hB
  obtain ⟨hU, hround, hcr, -⟩ := (hbase.disk v hv (p + 1) hp₁).1 e.1 hin hr
  exact ⟨hU, by rw [hround, hfull], by rw [hcr, hfull]; exact hgood⟩

end Record

/-! ## Catch-up -/

section Lend

/-- **A borrower leaves out every author the lender left out**: the lender
left out only authors its evidence names, its block carries that evidence
against each, since it references none of them, and the borrower holds
the block, so holds the evidence. -/
theorem excluded_lent {K : Set (BlockId × Block Validator BlockId Payload)} {G : ℕ}
    (hfa : cfg.Faithful) {w h : Validator}
    {s s' xw x : State Validator BlockId Payload} {inp inp' : Input Validator BlockId Payload}
    (hbsw : BuildState (cfg.at w) U G K s inp xw) (hbs : BuildState (cfg.at h) U G K s' inp' x)
    {n : ℕ} (hn : cfg.drops = false ∨ xw.floor ≤ n) {ow : Option BlockId}
    (ho : ∀ j, ow = some j → (xw.disk.blk j).creator = (cfg.at w).me)
    {z : BlockId} (hz : z ∈ x.disk.ids) (hzG : G < (x.disk.blk z).round)
    (hzpay : (U.block z).payload =
      payloadFor (cfg.at w) xw.disk n (refsAt (cfg.at w) xw.disk n ow xw.evidence) xw.evidence) :
    excluded (cfg.at w) xw.disk n xw.evidence ⊆ excluded (cfg.at h) x.disk n x.evidence := by
  intro a ha
  obtain ⟨e, hef, rfl⟩ := Finset.mem_image.mp (hbsw.excluded_sub_named hfa hn ha)
  obtain ⟨he, hne⟩ := Finset.mem_filter.mp hef
  -- the lent block references no block of the author, so carries the evidence
  have hnot : e.1 ∉ creatorsOf xw.disk.blk (refsAt (cfg.at w) xw.disk n ow xw.evidence) :=
    fun hm => by
      obtain ⟨k, hk, hkc⟩ := mem_creatorsOf.mp hm
      exact refsAt_avoids ho k hk (by rw [hkc]; exact ha)
  have hez : e ∈ cfg.xp.ev (x.disk.blk z).payload := by
    have hzG' : G < (x.disk.full z).round := by rw [(x.disk.full_fields z).1]; exact hzG
    rw [← (x.disk.full_fields z).2.2, ← (hbs.cut z hz hzG'.le).2.2.2 hzG', hzpay]
    unfold payloadFor
    erw [(hfa _ _ _).1]
    exact Finset.mem_filter.mpr ⟨he, hnot⟩
  exact Finset.mem_union_left _ (Finset.mem_image.mpr
    ⟨e, Finset.mem_filter.mpr ⟨hbs.holds hfa z hz e hez hne, hne⟩, rfl⟩)

end Lend

section Spread

variable {tr : Trace Validator BlockId Payload} {D : Finset Validator} {nE : ℕ}

/-- **Under spread evidence, an honest node leaves out only authors of
`D`**, at a state it builds from. -/
theorem excluded_sub_spread (hsp : Live.Spread cfg H tr D nE) {v : Validator}
    {s x : State Validator BlockId Payload} {inp : Input Validator BlockId Payload}
    {G : ℕ} (h : BuildState (cfg.at v) U G (knownAll cfg H tr) s inp x) {r : ℕ}
    (hr : cfg.drops = false ∨ cfg.Faithful ∧ x.floor ≤ r) :
    excluded (cfg.at v) x.disk r x.evidence ⊆ D :=
  h.excluded_sub
    (fun y hy e he hne => by
      obtain ⟨u, hu, hk⟩ := hy
      exact hsp.1 y (knownOf_sub hu hk) e he hne)
    (fun y hy z hz hne hc hr => by
      obtain ⟨u, hu, hk⟩ := hy
      obtain ⟨u', hu', hk'⟩ := hz
      exact hsp.2.1 y (knownOf_sub hu hk) z (knownOf_sub hu' hk') hne hc hr) hr

/-- **Under spread evidence, an honest node leaves out only authors of
`D`**, at the state before an event: at a round at or above its floor under
a faithful payload source, when it drops. -/
theorem excluded_before_spread (hsp : Live.Spread cfg H tr D nE) {v : Validator} (hv : v ∈ H)
    (i r : ℕ) (hr : cfg.drops = false ∨ cfg.Faithful ∧ (stateBefore cfg tr i v).floor ≤ r) :
    excluded (cfg.at v) (stateBefore cfg tr i v).disk r (stateBefore cfg tr i v).evidence ⊆ D := by
  set Z := stateBefore cfg tr i v with hZ
  have hi := Converge.inv_before (cfg := cfg) (tr := tr) i v
  -- the authors its evidence names are of `D`
  have hE : named Z.evidence ⊆ D := by
    intro a ha
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨hne, ⟨y, hy, z, hz, hy1, hz1, hyc, hzc, hrd⟩ | ⟨y, hy, hye⟩⟩ :=
      hi.evidence.2 e (Finset.mem_filter.mp he).1
    · rw [← hyc]
      exact hsp.2.1 y (Converge.knownBefore_sub hv i hy) z (Converge.knownBefore_sub hv i hz)
        (by rw [hy1, hz1]; exact hne) (hyc.trans hzc.symm) hrd
    · exact hsp.1 y (Converge.knownBefore_sub hv i hy) e hye hne
  intro a hm
  rcases Finset.mem_union.mp hm with hm | hm
  · exact hE hm
  · obtain ⟨c, hcR, hcm⟩ := Finset.mem_biUnion.mp hm
    obtain ⟨hcd, hcr⟩ := Store.mem_atRound.mp hcR
    rcases hr with hd | ⟨hf, hF⟩
    · by_contra hD
      exact ex_not_named (A := Dᶜ) (hi.valid hd)
        (fun j hj e he hne hc => Finset.mem_compl.mp hc (hsp.1 _ (Converge.stored_known hv hj) e
          (by simp only; rw [(Z.disk.full_fields j).2.2]; exact he) hne))
        c hcd _ hcm (Finset.mem_compl.mpr hD)
    · exact hE ((Converge.kept_before hf v i).exposed hcd
        (hi.above c hcd (by rw [hcr]; exact hF)).2 hcm)

/-- **Under spread evidence, an honest node that builds above `nE` leaves
out every author of `D`**. -/
theorem spread_sub_excluded (hsp : Live.Spread cfg H tr D nE) {i : ℕ} {w : Validator}
    {inp : Input Validator BlockId Payload} {x : State Validator BlockId Payload}
    (hi : tr[i]? = some (w, inp)) (hw : w ∈ H)
    {G : ℕ} (hbs : BuildState (cfg.at w) U G (knownAll cfg H tr) (stateBefore cfg tr i w) inp x)
    {e : BlockId × Block Validator BlockId Payload} (he : e ∈ persists (outputsAt cfg tr i))
    (her : nE < e.2.round) (r : ℕ) {st : Store Validator BlockId Payload} :
    D ⊆ excluded (cfg.at w) st r x.evidence :=
    fun a ha => by
  obtain ⟨Bs, hiX⟩ := hbs.inv
  obtain ⟨e', he', he'1⟩ := hiX.evidence.1 _ (hbs.det (hsp.2.2 i w inp hi hw e he her ha))
  have hne := (hiX.evidence.2 e' he').1
  exact Finset.mem_union_left _
    (Finset.mem_image.mpr ⟨e', Finset.mem_filter.mpr ⟨he', hne⟩, he'1⟩)

/-- **Under spread evidence, a block an honest node builds above `nE`
references no author of `D`**: its builder convicted them before the event,
and leaves out the authors it convicted. -/
theorem refs_avoid_spread (hsp : Live.Spread cfg H tr D nE) {i : ℕ} {w : Validator}
    {inp : Input Validator BlockId Payload} {x : State Validator BlockId Payload}
    {ow : Option BlockId} {r : ℕ} (hi : tr[i]? = some (w, inp)) (hw : w ∈ H) {G : ℕ}
    (hbs : BuildState (cfg.at w) U G (knownAll cfg H tr) (stateBefore cfg tr i w) inp x)
    {e : BlockId × Block Validator BlockId Payload} (he : e ∈ persists (outputsAt cfg tr i))
    (her : nE < e.2.round) (ho : ∀ j, ow = some j → (x.disk.blk j).creator = (cfg.at w).me) :
    ∀ k ∈ refsAt (cfg.at w) x.disk r ow x.evidence, (x.disk.blk k).creator ∉ D := by
  intro k hk hD
  exact refsAt_avoids ho k hk (spread_sub_excluded hsp hi hw hbs he her r hD)

/-- **Under spread evidence, a block an honest node builds above `nE`
references no block of an author of `D`, read in a record that reads its
disk from `G` up**, when the block lies above `G`, and above `G + 1` at a
node that drops: it builds in memory on references avoiding the authors it
convicted, at a round at or above its floor. -/
theorem built_avoids_spread (hsp : Live.Spread cfg H tr D nE) {i : ℕ} {w : Validator}
    {inp : Input Validator BlockId Payload} {x y : State Validator BlockId Payload}
    {o : List (Output Validator BlockId Payload)} (hi : tr[i]? = some (w, inp)) (hw : w ∈ H)
    {G : ℕ} (hbs : BuildState (cfg.at w) U G (knownAll cfg H tr) (stateBefore cfg tr i w) inp x)
    (hb : tryBuild (cfg.at w) x = some (y, o)) {e : BlockId × Block Validator BlockId Payload}
    (heo : e ∈ persists o) (he : e ∈ persists (outputsAt cfg tr i)) (her : nE < e.2.round)
    (hG : G + 1 ≤ e.2.round) (hGd : cfg.drops = true → G + 2 ≤ e.2.round) :
    ∀ k ∈ e.2.refs, (U.block k).creator ∉ D := by
  obtain ⟨r, ow, -, hle, hsh, -, -, hout⟩ := tryBuild_exit hb
  rw [hout, persists_built, List.mem_singleton] at heo
  subst heo
  change _ ≤ r + 1 at hG
  change cfg.drops = true → _ ≤ r + 1 at hGd
  have hF : x.floor ≤ r := by
    obtain ⟨Bs, hiX⟩ := hbs.inv
    cases hd : cfg.drops
    · exact hiX.floor.trans ((floorOf_le_top (cfg := cfg.at w) hd _).trans
        ((Nat.sub_le _ _).trans hle))
    · have h₁ := hiX.floor
      unfold floorOf at h₁
      rw [if_pos (show (cfg.at w).drops = true from hd)] at h₁
      have := hbs.slot hd
      have := hGd hd
      omega
  change ∀ k ∈ refsAt (cfg.at w) x.memory r ow x.evidence, _
  -- the node's own block of round `r`, if it builds on it, is in memory
  have hown : ∀ j, ow = some j → j ∈ x.memory.ids ∧ (x.memory.blk j).creator = (cfg.at w).me :=
    fun j hj => by
      rcases hsh with ⟨ht, hoe⟩ | ⟨-, hon, -⟩
      · obtain ⟨j', hj', hjd, hjr, hjc⟩ := hbs.own r ht
        rw [hoe, hj', Option.some.injEq] at hj
        subst hj
        have hjm := x.mirrors.mem_of hjd (by rw [hjr]; omega)
        exact ⟨hjm, by rw [x.mirrors.creator hjm]; exact hjc⟩
      · rw [hon] at hj; cases hj
  intro k hk hD
  have hkx := refsAt_avoids (fun j hj => (hown j hj).2) k hk
  have hkm : k ∈ x.memory.ids ∧ (x.memory.blk k).round = r := by
    rcases mem_refsAt_of hk with hk | hk
    · exact Store.mem_atRound.mp hk
    · obtain ⟨hkm, -⟩ := hown k hk
      rcases hsh with ⟨ht, hoe⟩ | ⟨-, hon, -⟩
      · obtain ⟨j', hj', -, hjr, -⟩ := hbs.own r ht
        rw [hoe, hj', Option.some.injEq] at hk
        subst hk
        exact ⟨hkm, by rw [x.mirrors.round hkm]; exact hjr⟩
      · rw [hon] at hk; cases hk
  have hkd := x.mirrors.sub hkm.1
  have hkr : G ≤ (x.disk.blk k).round := by rw [← x.mirrors.round hkm.1, hkm.2]; omega
  apply hkx
  rw [x.mirrors.creator hkm.1, ← hbs.cut.above_creator hkd hkr]
  exact spread_sub_excluded hsp hi hw hbs he her r hD

/-- **Under spread evidence, an honest author's block above `nE` lends
references avoiding the authors an honest node leaves out**, at the state
before an event (`built_avoids_spread`). -/
theorem lent_avoids_before (htime : Converge.TimelyAuthentic cfg H tr)
    {R : BlockRecord Validator BlockId Payload (ValidAt cfg.q Clause.none) H} {B E₀ E₁ : ℕ}
    (hbase : Base cfg H tr R B E₀ E₁) (hsp : Live.Spread cfg H tr D nE)
    {v : Validator} (hv : v ∈ H) {E : ℕ} (hE : E ≤ E₁) {m : ℕ} {z : BlockId}
    (hz : z ∈ (stateBefore cfg tr E v).disk.ids)
    (hzr : ((stateBefore cfg tr E v).disk.blk z).round = m + 1)
    (hzH : ((stateBefore cfg tr E v).disk.blk z).creator ∈ H) (hmE : nE ≤ m) (hmB : B ≤ m)
    (hrV : cfg.drops = true → B + 1 ≤ m)
    (hr : cfg.drops = false ∨ cfg.Faithful ∧ (stateBefore cfg tr E v).floor ≤ m) :
    ∀ k ∈ lent (stateBefore cfg tr E v).disk z, ((stateBefore cfg tr E v).disk.blk k).creator ∉
      excluded (cfg.at v) (stateBefore cfg tr E v).disk m (stateBefore cfg tr E v).evidence := by
  set Z := stateBefore cfg tr E v with hZ
  have hcut := (hbase.disk v hv E hE).1
  have hzf : (Z.disk.full z).round = m + 1 := by rw [(Z.disk.full_fields z).1]; exact hzr
  -- its author built it before the event, on references avoiding `D`
  have hzk := (Converge.inv_before (cfg := cfg) (tr := tr) E v).known z hz
  obtain ⟨j, hjE, hjw, hjz⟩ := mem_persists_before (cfg := cfg) (tr := tr) _ E
    (own_known htime hv hzH le_rfl hzk (Z.disk.full_fields z).2.1)
  obtain ⟨inpw, hjw'⟩ := Converge.event_of_map hjw
  obtain ⟨xw, yw, ow, hbsw, hbw, heow, -⟩ :=
    build_witness hbase hzH hjw' (by omega) hjz (by change (Z.disk.full z).round ≠ 0; omega)
  have hAD := built_avoids_spread hsp hjw' hzH hbsw hbw heow hjz
    (by change nE < (Z.disk.full z).round; omega) (by change _ ≤ (Z.disk.full z).round; omega)
    (fun hd => by have := hrV hd; change _ ≤ (Z.disk.full z).round; omega)
  intro k hk hmk
  have hkZ : k ∈ Z.disk.ids := Z.disk.complete z hz k hk
  -- the reference lies at round `m`, read alike by the record
  have hkm : (Z.disk.blk k).round = m := by
    have := Z.disk.pred z hz k hk
    change (Z.disk.blk k).round + 1 = (Z.disk.blk z).round at this
    omega
  have hcr : (R.block k).creator = (Z.disk.blk k).creator :=
    hcut.above_creator hkZ (by rw [hkm]; exact hmB)
  exact hAD k (Z.disk.refs_sub_full z hk) (hcr ▸ excluded_before_spread hsp hv E m hr hmk)

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
      (z, (stateBefore cfg tr K v).disk.full z) ∈ persists (outputsAt cfg tr j) := by
  have hk := (Converge.inv_before (cfg := cfg) (tr := tr) K v).known z hz
  have hp := own_known (v := w) htime hv hw le_rfl hk
    (by simp only; rw [((stateBefore cfg tr K v).disk.full_fields z).2.1]; exact hzc)
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
    {R : BlockRecord Validator BlockId Payload (ValidAt cfg.q Clause.none) H} {G : ℕ}
    (hx : BuildState (cfg.at w) R G (knownAll cfg H tr) (stateBefore cfg tr i w) inp x)
    (hb : tryBuild (cfg.at w) x = some (y, o)) (heo : e ∈ persists o)
    (he : e ∈ persists (outputsAt cfg tr i)) (her : e.2.round = n + 1)
    (hgx : DiskRises (cfg.at w) x (stateBefore cfg tr (i + 1) w))
    (hkeep : cfg.drops = false ∨ (stateBefore cfg tr (i + 1) w).floor ≤ n + 1)
    (hbeh : behind (cfg.at w) x.disk n) :
    ∃ w' ∈ H, w' ≠ w ∧ ∃ j < i, ∃ inp' z, tr[j]? = some (w', inp') ∧
      z ∈ persists (outputsAt cfg tr j) ∧ z.2.round = n + 1 ∧ z.1 ∈ x.disk.ids ∧
      x.disk.full z.1 = z.2 := by
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
  have hzK : (z, x.disk.full z) ∈ knownAll cfg H tr := hiX.known z hz.1
  have hfz := x.disk.full_fields z
  -- it is not the node: its round-`n + 1` block is the one it builds, not yet on disk
  have hww : w' ≠ w := by
    rintro rfl
    obtain ⟨r, id, b, hnew, -, -, hxt', hbr, -, -, -, -, -, -, -, hout⟩ := tryBuild_some hb
    rw [hout, persists_built, List.mem_singleton] at heo
    subst heo
    have hzp := mem_persists_of_known (hashInjective_of_trace hinj) (authentic_of_timely htime)
      hzK (by change (x.disk.full z).creator ∈ H; rw [hfz.2.1, hzc]; exact hw)
    have hep : (id, b) ∈ persists (runOf cfg tr w').2 :=
      mem_persists_iff.mpr (mem_outputs_of_event hi (mem_persists_iff.mp he))
    have hzc' : (z, x.disk.full z).2.creator = w' := by simp only; rw [hfz.2.1]; exact hzc
    rw [hzc'] at hzp
    have := eq_of_persists w' hzp hep
      (by change (x.disk.full z).round = b.round; rw [hfz.1, hz.2]; exact her.symm)
    exact hnew (by rw [← (Prod.mk.inj this).1]; exact hz.1)
  -- it persisted the block before the event
  obtain ⟨hzF, hzfull⟩ := hgx.2 z hz.1 (by rw [hz.2]; exact hkeep)
  have hk := (Converge.inv_before (cfg := cfg) (tr := tr) (i + 1) w).known z hzF
  rw [hzfull] at hk
  have hp := own_known htime hw hw'T le_rfl hk (by simp only; rw [hfz.2.1]; exact hzc)
  obtain ⟨j, hj, hjw', hjz⟩ := mem_persists_before (cfg := cfg) w' (i + 1) hp
  have hji : j ≠ i := by
    rintro rfl
    rw [hi] at hjw'
    exact hww (Option.some.inj hjw').symm
  obtain ⟨inp', hj'⟩ := Converge.event_of_map hjw'
  exact ⟨w', hw'T, hww, j, by omega, inp', (z, x.disk.full z), hj', hjz,
    by simp only; rw [hfz.1]; exact hz.2, hz.1, rfl⟩

/-- **A held block brings a quorum of each round below it**, down to the
round above a base's: the disk is valid there, so the block's references,
`q` authors of the round below, are held with it, and one of them leads
further down. -/
theorem quorum_below {R : BlockRecord Validator BlockId Payload (ValidAt cfg.q Clause.none) H}
    {B E₀ E₁ : ℕ} (hbase : Base cfg H tr R B E₀ E₁) (hadm : cfg.Admissible) {v : Validator}
    (hv : v ∈ H) {E : ℕ} (hE : E ≤ E₁) :
    ∀ (k : ℕ) {j : BlockId}, j ∈ (stateBefore cfg tr E v).disk.ids →
      ((stateBefore cfg tr E v).disk.blk j).round = k → ∀ r < k, B ≤ r →
      cfg.q ≤ (authorsIn (stateBefore cfg tr E v).disk.toRecord
        (stateBefore cfg tr E v).disk.ids r).card := by
  set Z := (stateBefore cfg tr E v).disk with hZ
  have hup := (hbase.disk v hv E hE).2.1
  intro k
  induction k with
  | zero => intro j _ _ r hr; omega
  | succ k ih =>
    intro j hj hjr r hr hBr
    obtain ⟨hsub, hval⟩ := hup j hj (by rw [hjr]; omega)
    have hq := hval.quorum (by rw [(Z.full_fields j).1, hjr]; omega)
    -- the references are held, one round below
    have hrefs : ∀ i ∈ (Z.full j).refs, i ∈ Z.ids ∧ (Z.blk i).round = k := fun i hi => by
      have h₂ := hval.predecessor i hi
      rw [(Z.full_fields i).1, (Z.full_fields j).1, hjr] at h₂
      exact ⟨hsub hi, by omega⟩
    have hcre : creators Z.full (Z.full j) = creatorsOf Z.blk (Z.full j).refs :=
      Finset.image_congr fun i _ => (Z.full_fields i).2.1
    rw [hcre] at hq
    by_cases hrk : r = k
    · subst hrk
      refine hq.trans (Finset.card_le_card fun a ha => ?_)
      obtain ⟨i, hi, rfl⟩ := mem_creatorsOf.mp ha
      exact mem_authorsIn.mpr ⟨i, (hrefs i hi).1, (hrefs i hi).2, rfl⟩
    · obtain ⟨i, hi⟩ : (Z.full j).refs.Nonempty := by
        by_contra hne
        rw [Finset.not_nonempty_iff_eq_empty] at hne
        rw [hne] at hq
        have := hadm.2.2.2.1
        simp [creatorsOf] at hq
        omega
      exact ih (hrefs i hi).1 (hrefs i hi).2 r (by omega) hBr

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
theorem catches_up (hq : 2 ≤ cfg.q)
    (hadm : cfg.Admissible) (hfa : cfg.Faithful) (hf : Hᶜ.card ≤ cfg.f) (hid : Function.Injective
        cfg.idOf)
    (htime : Converge.TimelyAuthentic cfg H tr) (hinj : Converge.HashInjective cfg H tr)
    {R : BlockRecord Validator BlockId Payload (ValidAt cfg.q Clause.none) H} {B E₀ E₁ : ℕ}
    (hbase : Base cfg H tr R B E₀ E₁)
    (hTH : T ⊆ H) (hmono : Live.TimeMono tr time)
    (harr : Arrival cfg T tr time gst (Δ + Δₛ) t₁) (hstart : Live.StartedBy T tr time gst)
    {S : Finset Validator} (hST : S ⊆ T) (hS : cfg.f + 1 ≤ S.card) {τ n : ℕ} (hgτ : gst ≤ τ)
    (hτ₁ : τ + (Δ + Δₛ) ≤ t₁) (hE₀ : E₀ ≤ eventsBy tr time (τ + (Δ + Δₛ)))
    (hE₁ : eventsBy tr time (τ + (Δ + Δₛ)) ≤ E₁)
    (hSn : ∀ w ∈ S, (stateAt cfg tr time w τ).top.isSome ∧ n ≤ topAt cfg tr time w τ)
    {D : Finset Validator} {nE : ℕ} (hsp : Live.Spread cfg H tr D nE)
    {v : Validator} (hv : v ∈ T) (hvE : nE ≤ topAt cfg tr time v gst)
    (hvB : B ≤ topAt cfg tr time v gst)
    (hvV : cfg.drops = true → B + 1 ≤ topAt cfg tr time v gst) :
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
  -- `v` is at its round at GST or above, so above the base
  have hmg : topAt cfg tr time v gst ≤ m := by
    have := (rises_before (cfg := cfg) (tr := tr) v (eventsBy_mono (tr := tr) (time := time)
      (show gst ≤ τ + (Δ + Δₛ) by omega))).1
    change topAt cfg tr time v gst ≤ (stateBefore cfg tr E v).top.getD 0 at this
    rw [hm] at this
    simpa using this
  have hmB : B ≤ m := hvB.trans hmg
  have hmV : cfg.drops = true → B + 1 ≤ m := fun hd => (hvV hd).trans hmg
  have hFm : Z.floor ≤ m := by
    cases hd : cfg.drops
    · exact (Converge.floor_before (cfg := cfg) (tr := tr) hd hm).trans (Nat.sub_le _ _)
    · have := (hbase.window v (hTH hv) E hE₀ hE₁).2.1
      rw [hm] at this; exact this
  have hcard := quorum_below hbase hadm (hTH hv) hE₁ _ hj₀ hj₀r m
    (by have := (hSn w₀ hw₀).2; omega) hmB
  -- and they are `f + 1` authors of round `m + 1`, or one is above it
  have hbeh : behind (cfg.at v) Z.disk m := by
    change cfg.f + 1 ≤ (Z.disk.authorsAt (m + 1)).card
    rw [Store.authorsAt_eq]
    by_cases hup : ∃ w ∈ S, m + 1 < topAt cfg tr time w τ
    · obtain ⟨w, hw, hwm⟩ := hup
      obtain ⟨j, hj, hjr, -⟩ := htops w hw
      have h₁ := quorum_below hbase hadm (hTH hv) hE₁ _ hj hjr (m + 1) hwm (by omega)
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
  have hav := lent_avoids_before htime hbase hsp (hTH hv) hE₁ hzZ hzr hzH hmE hmB
    hmV (by cases hd : cfg.drops; exact Or.inl rfl; exact Or.inr ⟨hfa, hFm⟩)
  have hsome := tryBuild_isSome (cfg := cfg.at v) hm
    (harr.recovered (by omega) v hv E (eventsBy_mono (tr := tr) (time := time) (by omega))
      (eventsBy_mono (by omega)))
    (Or.inr hbeh) hcard
    (fun j hj => by rw [hoo] at hj; cases hj; exact ⟨hoi, hor, hoc⟩)
    (Or.inr ⟨_, lent_mem_lents hzZ hzr hzm hav, (lent_buildable (cfg := cfg.at v)
      (fun j hj hjr => hbase.valid (hTH hv) hE₁ hj (by
        cases hd : cfg.drops; exact Or.inl rfl; exact Or.inr (by omega))) hzZ hzr (by
        by_contra hk
        have h₁ := Z.low z hk
        have h₃ : (Z.disk.blk z).round = m + 1 := hzr
        omega) hfa
      (fresh_before hid htime (hTH hv) hm) _
      (fun j hj hjr => (Converge.kept_before hfa v E).exposed hj
        (hbase.valid (hTH hv) hE₁ hj (by
          cases hd : cfg.drops; exact Or.inl rfl; exact Or.inr (by have := hmV hd; omega))).2)).2⟩)
    (fresh_before hid htime (hTH hv) hm) hFm
  rw [hSet.build] at hsome
  cases hsome

end Catch

/-! ## Build times -/

section Built

variable {T : Finset Validator} {tr : Trace Validator BlockId Payload} {time : ℕ → ℕ}

/-- A node at a round built it by then. -/
theorem builtAt_le_of_top {v : Validator}
    (hmono : Live.TimeMono tr time) {τ n : ℕ}
    (hs : (stateAt cfg tr time v τ).top.isSome)
    (hn : n ≤ topAt cfg tr time v τ)
    (hj : ∀ k < eventsBy tr time τ, ∀ inp, tr[k]? = some (v, inp) →
      Skips (cfg.at v) (stateBefore cfg tr k v) inp (stateBefore cfg tr (k + 1) v) →
      (stateBefore cfg tr (k + 1) v).top.getD 0 < n) : builtAt cfg tr time v n ≤ τ := by
  obtain ⟨i, -, -, -, -, -, hbt, hiτ⟩ := built_of_top hmono hs hn hj
  omega

end Built

end Node

end LeanDag
