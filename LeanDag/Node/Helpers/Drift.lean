import LeanDag.Node.Helpers.Arrive
/-!
# Copied references and the drift of build times

`docs/validator.md` §13.3. A node at round `n` holding a peer's round-`n + 1`
block `z` passes the reach and certificate tests with the references `z`
lends it when the peer's references passed them (`ready_transfer`,
`refsAt_ready`, `lent_buildable`): the leader blocks the tests read are
reached from `z`'s references, so the node holds them and reads the same
votes. Past GST a reliable node at round `n` within `A = Δ + Δₛ` of a peer
that built round `n + 1` is above `n` by then (`catches_up`), so the
reliable nodes build every round within `A` of each other (`drift`).
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
/-- **A cut holds a record path's short history**: a block that a stored
block reaches in the record, at most `m` rounds below it, lies within `m`
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
  -- a candidate of the peer's store reached from a reference
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
/-- **`refsAt` passes the tests when a held block's lent references do**:
a stored round-`r + 1` block of another author whose lent references pass
the tests and can be built on. -/
theorem refsAt_ready {st : Store Validator BlockId Payload} {r : ℕ} {o : Option BlockId}
    {c : BlockId} (hc : c ∈ st.ids) (hcr : (st.blk c).round = r + 1)
    (hcm : (st.blk c).creator ≠ cfg.me)
    (hready : reachReady cfg st (lent cfg st c o) r = true ∧
      certReady cfg st (lent cfg st c o) r = true)
    (hb : buildable cfg st r (lent cfg st c o) = true) :
    reachReady cfg st (refsAt cfg st r o) r = true ∧
      certReady cfg st (refsAt cfg st r o) r = true := by
  unfold refsAt
  dsimp only
  split
  · rename_i h
    simpa only [Bool.and_eq_true] using h
  · set L := (((blocksAt st.toRecord (r + 1)).sort (· ≤ ·)).filter fun c =>
        decide ((st.blk c).creator ≠ cfg.me)).map (lent cfg st · o) with hL
    have hmem : lent cfg st c o ∈ L :=
      List.mem_map.mpr ⟨c, List.mem_filter.mpr ⟨(Finset.mem_sort _).mpr
        (Finset.mem_filter.mpr ⟨hc, hcr⟩), decide_eq_true hcm⟩, rfl⟩
    have hs : (L.find? fun R => (reachReady cfg st R r && certReady cfg st R r) &&
        buildable cfg st r R).isSome :=
      List.find?_isSome.mpr ⟨_, hmem, by rw [hready.1, hready.2, hb]; rfl⟩
    obtain ⟨R, hR⟩ := Option.isSome_iff_exists.mp hs
    rw [hR]
    have := List.find?_some hR
    simp only [Bool.and_eq_true] at this
    exact this.1

omit [Fintype Validator] in
/-- **A peer's block lends references the node can build on**: a stored
round-`n + 1` block of another author, whose references hold `q` distinct
authors one round below, lends them with the node's own round-`n` block
put in for its own, and they include the block's references. -/
theorem lent_buildable {x Z : Store Validator BlockId Payload} (hx : IsCut U x) (hZ : IsCut U Z)
    {R : Finset BlockId} {n : ℕ} {z o : BlockId} (hR : R ⊆ x.ids)
    (hRq : cfg.q ≤ (creatorsOf x.blk R).card)
    (hRd : ∀ i ∈ R, ∀ j ∈ R, (x.blk i).creator = (x.blk j).creator → i = j)
    (hzZ : z ∈ Z.ids) (hzr : (Z.blk z).round = n + 1) (hzR : (Z.blk z).refs = R)
    (hoZ : o ∈ Z.ids) (hor : (Z.blk o).round = n) (hoc : (Z.blk o).creator = cfg.me)
    (hme : cfg.me ∈ H)
    (hfresh : ∀ R, cfg.idOf ⟨n + 1, cfg.me, R, cfg.payload (n + 1)⟩ ∉ Z.ids) :
    R ⊆ lent cfg Z z (some o) ∧ lent cfg Z z (some o) ⊆ Z.ids ∧
      buildable cfg Z n (lent cfg Z z (some o)) = true := by
  have hRZ : R ⊆ Z.ids := fun j hj => Z.complete z hzZ j (by rw [← hzR] at hj; exact hj)
  have hcre : ∀ j ∈ R, (Z.blk j).creator = (x.blk j).creator := fun j hj => by
    rw [← hZ.creator (hRZ hj), hx.creator (hR hj)]
  have hsub : R ⊆ lent cfg Z z (some o) := by
    intro j hj
    by_cases hjm : (Z.blk j).creator = cfg.me
    · have hjo : j = o := U.eq_of_creator_eq (hZ j (hRZ hj)).1 (hZ o hoZ).1 hme
        (by rw [hZ.creator (hRZ hj)]; exact hjm) (by rw [hZ.creator hoZ]; exact hoc)
        (by rw [hZ.round (hRZ hj), hZ.round hoZ, hor]
            have := Z.pred z hzZ j (by rw [← hzR] at hj; exact hj)
            change (Z.blk j).round + 1 = (Z.blk z).round at this
            omega)
      exact Finset.mem_union_right _ (by rw [hjo]; simp)
    · have hjz : j ∈ (Z.blk z).refs := by rw [hzR]; exact hj
      exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hjz, hjm⟩)
  -- the lent references: `z`'s other than the node's, and its own block
  have hlent : ∀ j ∈ lent cfg Z z (some o),
      (j ∈ (Z.blk z).refs ∧ (Z.blk j).creator ≠ cfg.me) ∨ j = o := by
    intro j hj
    rcases Finset.mem_union.mp hj with h | h
    · exact Or.inl (Finset.mem_filter.mp h)
    · exact Or.inr (by simpa using h)
  have hlZ : lent cfg Z z (some o) ⊆ Z.ids := fun j hj => by
    rcases hlent j hj with ⟨h, -⟩ | rfl
    · exact Z.complete z hzZ j h
    · exact hoZ
  have hlr : ∀ j ∈ lent cfg Z z (some o), (Z.blk j).round = n := fun j hj => by
    rcases hlent j hj with ⟨h, -⟩ | rfl
    · have := Z.pred z hzZ j h
      change (Z.blk j).round + 1 = (Z.blk z).round at this
      omega
    · exact hor
  refine ⟨hsub, hlZ, ?_⟩
  set b : Block Validator BlockId Payload := ⟨n + 1, cfg.me, lent cfg Z z (some o),
    cfg.payload (n + 1)⟩ with hb
  have hnin : ∀ j ∈ lent cfg Z z (some o), j ≠ cfg.idOf b :=
    fun j hj h => hfresh _ (h ▸ hlZ hj)
  unfold buildable
  refine decide_eq_true ⟨hfresh _, hlZ, fun j hj => by rw [hlr j hj],
    ⟨fun j hj => ?_, fun _ => ?_, fun i hi j hj hij => ?_⟩⟩
  · rw [Function.update_of_ne (hnin j hj), hlr j hj]
  · simp only [creators, creatorsOf]
    rw [Finset.image_congr (g := fun i => (Z.blk i).creator)
      (fun j hj => by simp only; rw [Function.update_of_ne (hnin j hj)])]
    refine le_trans hRq (le_trans (le_of_eq ?_) (Finset.card_le_card
      (Finset.image_subset_image hsub)))
    exact congrArg Finset.card (Finset.image_congr fun j hj => (hcre j hj).symm)
  · rw [Function.update_of_ne (hnin i hi), Function.update_of_ne (hnin j hj)] at hij
    rcases hlent i hi with ⟨hi₁, hi₂⟩ | rfl <;> rcases hlent j hj with ⟨hj₁, hj₂⟩ | rfl
    · rw [hzR] at hi₁ hj₁
      exact hRd i hi₁ j hj₁ (by rw [← hcre i hi₁, ← hcre j hj₁]; exact hij)
    · exact absurd (hij.trans hoc) hi₂
    · exact absurd (hij.symm.trans hoc) hj₂
    · rfl

/-! ## Rounds and build times along a trace -/

section Trace

variable {tr : Trace Validator BlockId Payload} {v : Validator}

/-- **A node's own block stays stored** at every later event. -/
theorem own_held {p : ℕ} {inp : Input Validator BlockId Payload} (hp : tr[p]? = some (v, inp))
    {e : BlockId × Block Validator BlockId Payload} (he : e ∈ persists (outputsAt cfg tr p))
    {E : ℕ} (hpE : p < E) :
    e.1 ∈ (stateBefore cfg tr E v).store.ids := by
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
    (hn : n ≤ topAt cfg tr time v τ) :
    ∃ i inp e, tr[i]? = some (v, inp) ∧ e ∈ persists (outputsAt cfg tr i) ∧ e.2.round = n ∧
      builtAt cfg tr time v n = time i ∧ time i ≤ τ := by
  obtain ⟨b, hbE, hbv, e, he, her⟩ := built_by (eventsBy tr time τ) hs hn
  obtain ⟨i₀, hi₀b, hbt, hi₀v, e₀, he₀, he₀r⟩ := builtAt_first (cfg := cfg) time hbv ⟨e, he, her⟩
  obtain ⟨inp, hi₀⟩ := Converge.event_of_map hi₀v
  obtain ⟨inpb, hb⟩ := Converge.event_of_map hbv
  have hbl : b < tr.length := (List.getElem?_eq_some_iff.mp hb).1
  exact ⟨i₀, inp, e₀, hi₀, he₀, he₀r, hbt,
    (hmono i₀ b hi₀b hbl).trans ((lt_eventsBy hmono hbl).mp hbE)⟩

/-- **Build times do not decrease with the round.** -/
theorem builtAt_le_succ {τ n : ℕ} (hs : (stateAt cfg tr time v τ).top.isSome)
    (hn : n + 1 ≤ topAt cfg tr time v τ) :
    builtAt cfg tr time v n ≤ builtAt cfg tr time v (n + 1) := by
  obtain ⟨i, _inp, e, hi, he, her, hbt, -⟩ := built_of_top hmono hs hn
  obtain ⟨t, ht, hrt⟩ := built_le_top hi he
  obtain ⟨b, hb, hbv, e', he', her'⟩ := built_by (i + 1) (by rw [ht]; rfl)
    (show n ≤ _ by rw [ht]; simp only [Option.getD_some]; omega)
  obtain ⟨i₀, hi₀b, hbt₀, -⟩ := builtAt_first (cfg := cfg) time hbv ⟨e', he', her'⟩
  rw [hbt, hbt₀]
  exact hmono i₀ i (by omega) (List.getElem?_eq_some_iff.mp hi).1

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
by its author: the store after the event holds it, and is a cut. -/
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
  have hin : e.1 ∈ (stateBefore cfg tr (p + 1) v).store.ids := by
    rw [outputsAt_eq hp] at he
    rw [stateBefore_succ hp, if_pos rfl]
    exact (step_persist (cfg := cfg.at v) e he).1
  exact ((cut_before hσ hadm hf htime hinj (p + 1) v hv).1 e.1 hin).1

end Record

/-! ## Catch-up -/

section Catch

variable {T : Finset Validator} {tr : Trace Validator BlockId Payload} {time : ℕ → ℕ}
  {gst Δ Δₛ t₁ : ℕ}

omit [Fintype Validator] in
/-- **A valid block's references**: `q` distinct authors, none twice, read
on the store it was built on. -/
theorem refs_of_rowValid {st : Store Validator BlockId Payload} {id : BlockId}
    {b : Block Validator BlockId Payload} (hnew : id ∉ st.ids) (hrefs : b.refs ⊆ st.ids)
    (hr : 0 < b.round) (hv : rowValid cfg.q (Function.update st.blk id b) b) :
    cfg.q ≤ (creatorsOf st.blk b.refs).card ∧
      ∀ i ∈ b.refs, ∀ j ∈ b.refs, (st.blk i).creator = (st.blk j).creator → i = j := by
  have hne : ∀ j ∈ b.refs, Function.update st.blk id b j = st.blk j := fun j hj =>
    Function.update_of_ne (fun h : j = id => hnew (h ▸ hrefs hj)) _ _
  refine ⟨?_, fun i hi j hj hij => hv.clause i hi j hj (by rw [hne i hi, hne j hj]; exact hij)⟩
  have hq := hv.quorum hr
  simp only [creators, creatorsOf] at hq ⊢
  rwa [Finset.image_congr (g := fun i => (st.blk i).creator) (fun j hj => by
    simp only; rw [hne j hj])] at hq

/-- **Catch-up**: past GST, a reliable node `u` at round `n` or above `A =
Δ + Δₛ` after a reliable peer built a round-`n + 1` block, having built
round `n` at most `A` after the peer, is above `n` then. It holds the
peer's block, and with it a quorum of round `n`; if the peer built on the
tests, `u` passes them with the references the block lends; if on the
round's timer, `u`'s has fired too. -/
theorem catches_up (hq : 2 ≤ cfg.q) (hσ : cfg.σ = boundedSel)
    (hadm : cfg.Admissible) (hf : Hᶜ.card ≤ cfg.f) (hid : Function.Injective cfg.idOf)
    (htime : Converge.TimelyAuthentic cfg H tr) (hinj : Converge.HashInjective cfg H tr)
    (hTH : T ⊆ H) (hmono : Live.TimeMono tr time)
    (hdel : Live.DeliveredWithin cfg T tr time gst Δ t₁)
    (htimer : Live.TimersOnTime cfg T tr time t₁)
    (hsync : Live.SyncedWithin cfg H T tr time gst Δₛ t₁)
    {u w : Validator} (hu : u ∈ T) (hw : w ∈ T) (huw : u ≠ w) {n i : ℕ}
    {inp : Input Validator BlockId Payload} (hi : tr[i]? = some (w, inp))
    {e : BlockId × Block Validator BlockId Payload} (he : e ∈ persists (outputsAt cfg tr i))
    (her : e.2.round = n + 1) (hgi : gst ≤ time i)
    (hus : (stateAt cfg tr time u (time i + (Δ + Δₛ))).top.isSome)
    (hun : n ≤ topAt cfg tr time u (time i + (Δ + Δₛ)))
    (hbu : builtAt cfg tr time u n ≤ builtAt cfg tr time w n + (Δ + Δₛ))
    (ht₁ : time i + (Δ + Δₛ) ≤ t₁) :
    n + 1 ≤ topAt cfg tr time u (time i + (Δ + Δₛ)) := by
  have hil : i < tr.length := (List.getElem?_eq_some_iff.mp hi).1
  set τ := time i + (Δ + Δₛ) with hτ
  set E := eventsBy tr time τ with hE
  by_contra hlt
  -- `u` is at round `n`, settled
  have hZt : (stateBefore cfg tr E u).top = some n := by
    obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp hus
    change (stateBefore cfg tr E u).top = some t at ht
    change n ≤ (stateBefore cfg tr E u).top.getD 0 at hun
    change ¬ n + 1 ≤ (stateBefore cfg tr E u).top.getD 0 at hlt
    rw [ht] at hun hlt ⊢
    simp only [Option.getD_some] at hun hlt
    rw [show t = n by omega]
  have hiE : i < E := (lt_eventsBy hmono hil).mpr (by omega)
  set Z := stateBefore cfg tr E u with hZ
  have hSet : Settled (cfg.at u) Z := by
    rcases settled_before (cfg := cfg) hq u E with h | h
    · rw [hZt] at h; cases h
    · exact h
  have hZcut := (cut_before hσ hadm hf htime hinj E u (hTH hu)).1
  obtain ⟨o, hoo, hoi, hor, hoc⟩ := ownTop_before (cfg := cfg) (tr := tr) (v := u) E n hZt
  -- the peer's build
  obtain ⟨x, y, out, hbs, hb, heo⟩ := build_witness hσ hadm hf htime hinj (hTH hw) hi he
    (by omega)
  obtain ⟨r, hxt, -, hexit, hout⟩ := tryBuild_exit hb
  obtain ⟨r', id, b, hnew, hrefs, hpred, hxt', hbr, -, -, hrv, -, -, -, -, hout'⟩ :=
    tryBuild_some hb
  rw [hxt] at hxt'
  cases hxt'
  have hAB := congrArg persists (hout.symm.trans hout')
  rw [persists_built, persists_built, List.singleton_inj] at hAB
  rw [hout', persists_built, List.mem_singleton] at heo
  subst heo
  have hrn : r = n := by simp only at her; omega
  subst hrn
  have hbR : b.refs = refsAt (cfg.at w) x.store r x.own := by
    have := congrArg (fun e => e.2.refs) hAB
    simp only at this
    exact this.symm
  set R := refsAt (cfg.at w) x.store r x.own with hRdef
  have hRx : R ⊆ x.store.ids := hbR ▸ hrefs
  obtain ⟨hRq, hRd⟩ := refs_of_rowValid (cfg := cfg.at w) hnew hrefs (by omega) hrv
  rw [hbR] at hRq hRd
  -- the peer's block arrives
  obtain ⟨hzZ, hzr, hzc, hzb⟩ := block_arrives hσ hadm hf htime hinj hTH hmono hdel hsync
    hw hu (Ne.symm huw) hi he (s := time i) le_rfl (τ := τ)
    (by rw [max_eq_left hgi]; omega) ht₁ hZt (le_of_eq hbr)
  change (id, b).1 ∈ Z.store.ids at hzZ
  change (Z.store.blk (id, b).1).round = (id, b).2.round at hzr
  change (Z.store.blk (id, b).1).creator = w at hzc
  change Z.store.blk (id, b).1 = (id, b).2 at hzb
  simp only at hzZ hzr hzc hzb her
  have hZR : (Z.store.blk id).refs = R := by rw [hzb, hbR]
  -- a quorum of round `r`
  have hRZ : ∀ j ∈ R, j ∈ Z.store.ids ∧ (Z.store.blk j).round = r := fun j hj => by
    have hj' : j ∈ (Z.store.blk id).refs := by rw [hZR]; exact hj
    have := Z.store.pred id hzZ j hj'
    change (Z.store.blk j).round + 1 = (Z.store.blk id).round at this
    exact ⟨Z.store.complete id hzZ j hj', by omega⟩
  have hcre : creatorsOf Z.store.blk R = creatorsOf x.store.blk R :=
    Finset.image_congr fun j hj => by
      rw [← hZcut.creator (hRZ j hj).1, hbs.cut.creator (hRx hj)]
  have hcard : cfg.q ≤ (authorsIn Z.store.toRecord Z.store.ids r).card := by
    refine le_trans hRq (le_trans (le_of_eq (congrArg Finset.card hcre.symm))
      (Finset.card_le_card fun a ha => ?_))
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp ha
    exact mem_authorsIn.mpr ⟨j, (hRZ j hj).1, (hRZ j hj).2, rfl⟩
  have hfresh := fresh_before hid htime (hTH hu) hZt
  -- the timer has fired, or the lent references pass the tests
  have hgo : r ∈ Z.fired ∨
      (reachReady (cfg.at u) Z.store (refsAt (cfg.at u) Z.store r Z.own) r = true ∧
        certReady (cfg.at u) Z.store (refsAt (cfg.at u) Z.store r Z.own) r = true) := by
    rcases hexit with ⟨hre, hce⟩ | ⟨hfx, -⟩
    · right
      obtain ⟨hRR, hlZ, hlb⟩ := lent_buildable (cfg := cfg.at u) hbs.cut hZcut hRx hRq hRd
        hzZ (hzr.trans hbr) hZR hoi hor hoc (hTH hu) hfresh
      have hready := ready_transfer (cfg := cfg.at u) hσ (fun h => certThreshold_pos hadm h)
        hbs.cut hZcut hRx hRR hlZ hre hce
      rw [hoo]
      exact refsAt_ready (cfg := cfg.at u) hzZ (hzr.trans hbr) (by rw [hzc]; exact Ne.symm huw)
        hready hlb
    · left
      obtain ⟨j, hj, hjt⟩ : ∃ j ≤ i, tr[j]? = some (w, Input.timer r) := by
        rcases hbs.fired _ hfx with h | h
        · obtain ⟨j, hj, hjt⟩ := fired_before (cfg := cfg) (tr := tr) (v := w) i _ h
          exact ⟨j, hj.le, hjt⟩
        · exact ⟨i, le_rfl, by rw [hi, h]⟩
      have hwt := timer_after_built time hmono htimer hw hil hj hjt
      obtain ⟨bu, inpu, eu, hbu', heu, heur, hbut, -⟩ := built_of_top hmono hus hun
      have hset := timer_of_persist hbu' heu
      rw [heur] at hset
      obtain ⟨f, -, hfe, htf⟩ := htimer.1 bu u inpu hbu' hu r (cfg.timeout r) hset (by omega)
      have hfl : f < tr.length := (List.getElem?_eq_some_iff.mp hfe).1
      have hfE : f < E := (lt_eventsBy hmono hfl).mpr (by omega)
      exact fired_stays hfe E hfE
  have hsome := tryBuild_isSome (cfg := cfg.at u) hZt hgo hcard
    (fun j hj => by rw [hoo] at hj; cases hj; exact ⟨hoi, hor, hoc⟩) hfresh
  rw [hSet.build] at hsome
  cases hsome

end Catch

/-! ## The drift of build times -/

section Drift

variable {T : Finset Validator} {tr : Trace Validator BlockId Payload} {time : ℕ → ℕ}
  {gst Δ Δₛ t₁ : ℕ}

/-- **A reliable node has started** at any time from GST on. -/
theorem started_at (hadm : cfg.Admissible) (hid : Function.Injective cfg.idOf)
    (htime : Converge.TimelyAuthentic cfg H tr) (hTH : T ⊆ H)
    (hmono : Live.TimeMono tr time) (hstart : Live.StartedBy T tr time gst) {v : Validator}
    (hv : v ∈ T) {τ : ℕ} (hτ : gst ≤ τ) : (stateAt cfg tr time v τ).top.isSome := by
  obtain ⟨st, hst, htst⟩ := hstart v hv
  have hstl : st < tr.length := (List.getElem?_eq_some_iff.mp hst).1
  have hstE : st + 1 ≤ eventsBy tr time τ := (lt_eventsBy hmono hstl).mpr (by omega)
  exact (rises_before (cfg := cfg) v hstE).2.1
    (started_after hadm hid htime (hTH hv) hst)

/-- A node at a round built it by then. -/
theorem builtAt_le_of_top {v : Validator}
    (hmono : Live.TimeMono tr time) {τ n : ℕ} (hs : (stateAt cfg tr time v τ).top.isSome)
    (hn : n ≤ topAt cfg tr time v τ) : builtAt cfg tr time v n ≤ τ := by
  obtain ⟨i, -, -, -, -, -, hbt, hiτ⟩ := built_of_top hmono hs hn
  omega

/-- **Drift stays within `A = Δ + Δₛ`**: past GST, if the reliable nodes
built round `n₀` within `A` of each other, they build every round from
`n₀` up to one they all reach by `t` within `A` of each other
(`catches_up`). -/
theorem drift (hq : 2 ≤ cfg.q) (hσ : cfg.σ = boundedSel)
    (hadm : cfg.Admissible) (hf : Hᶜ.card ≤ cfg.f) (hid : Function.Injective cfg.idOf)
    (htime : Converge.TimelyAuthentic cfg H tr) (hinj : Converge.HashInjective cfg H tr)
    (hTH : T ⊆ H) (hmono : Live.TimeMono tr time)
    (hdel : Live.DeliveredWithin cfg T tr time gst Δ t₁)
    (htimer : Live.TimersOnTime cfg T tr time t₁)
    (hsync : Live.SyncedWithin cfg H T tr time gst Δₛ t₁) (hstart : Live.StartedBy T tr time gst)
    {n₀ s : ℕ} (hgs : gst ≤ s)
    (h₀ : ∀ v ∈ T, s ≤ builtAt cfg tr time v n₀ ∧ builtAt cfg tr time v n₀ ≤ s + (Δ + Δₛ))
    {t N : ℕ} (hst : ∀ v ∈ T, (stateAt cfg tr time v t).top.isSome)
    (hN : ∀ v ∈ T, N ≤ topAt cfg tr time v t) (ht₁ : t + (Δ + Δₛ) ≤ t₁) :
    ∀ n, n₀ ≤ n → n ≤ N → ∀ u ∈ T, ∀ w ∈ T, s ≤ builtAt cfg tr time u n ∧
      builtAt cfg tr time u n ≤ builtAt cfg tr time w n + (Δ + Δₛ) := by
  intro n hn₀ hnN
  induction n, hn₀ using Nat.le_induction with
  | base =>
    intro u hu w hw
    exact ⟨(h₀ u hu).1, (h₀ u hu).2.trans (by have := (h₀ w hw).1; omega)⟩
  | succ n hn₀ ih =>
    have ih := ih (by omega)
    intro u hu w hw
    have hgu : s ≤ builtAt cfg tr time u (n + 1) :=
      (ih u hu u hu).1.trans (builtAt_le_succ hmono (hst u hu) ((hN u hu).trans' hnN))
    refine ⟨hgu, ?_⟩
    by_cases huw : u = w
    · subst huw; omega
    -- the peer's first build of round `n + 1`
    obtain ⟨i, inp, e, hi, he, her, hbt, hit⟩ :=
      built_of_top hmono (hst w hw) ((hN w hw).trans' hnN)
    have hgw : s ≤ builtAt cfg tr time w (n + 1) :=
      (ih w hw w hw).1.trans (builtAt_le_succ hmono (hst w hw) ((hN w hw).trans' hnN))
    have hwn := builtAt_le_succ hmono (hst w hw) ((hN w hw).trans' hnN)
    have hus := started_at hadm hid htime hTH hmono hstart hu
      (τ := time i + (Δ + Δₛ)) (by omega)
    -- `u` built round `n` by then
    obtain ⟨bu, _inpu, eu, hbu, heu, heur, hbut, -⟩ :=
      built_of_top hmono (hst u hu) ((hN u hu).trans' (by omega : n ≤ N))
    have hun := (top_of_built hmono hbu heu (τ := time i + (Δ + Δₛ))
      (by have := (ih u hu w hw).2; omega)).2
    rw [heur] at hun
    have hup := catches_up hq hσ hadm hf hid htime hinj hTH hmono hdel htimer hsync
      hu hw huw hi he her (by omega) hus hun (ih u hu w hw).2 (by omega)
    have := builtAt_le_of_top hmono hus hup
    omega

end Drift

end Node

end LeanDag
