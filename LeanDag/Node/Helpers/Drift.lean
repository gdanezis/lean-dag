import LeanDag.Node.Helpers.Arrive
/-!
# Copied references and the drift of build times

`docs/validator.md` §13.3. A node at round `n` holding a peer's round-`n + 1`
block `z` passes the reach and certificate tests with the references `z`
lends it, when the peer's passed them and its horizon lies `Λ` or more
below `n`, with `voteOffset ≤ Λ` (`lent_ready`): the leader blocks the
tests read lie at or above its horizon, so it holds them and their paths
from `z`'s references, and reads the same votes.
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
/-- **A record path from a cut, at or above its horizon, is a store path.** -/
theorem IsCut.reachesFrom_store [P.Mechanised] (hc : IsCut U st) {i : BlockId}
    (hr : st.base ≤ (U.block i).round) :
    ∀ {j : BlockId}, j ∈ st.ids → ReachesFrom U.block j i → ReachesFrom st.blk j i := by
  intro j hj h
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ReachesFrom.refl
  | @head a c hstep hrest ih =>
    have hstep : c ∈ (U.block a).refs := hstep
    have haU := (hc a hj).1
    have hac := U.causal.refs_round a haU c hstep
    have hxc := U.causal.round_le_of_reaches (U.causal.complete a haU c hstep) hrest
    have hlt : st.base < (st.blk a).round := by rw [← hc.round hj]; omega
    have hcs : c ∈ (st.blk a).refs := by rw [← hc.eq_of_lt hj hlt]; exact hstep
    exact Relation.ReflTransGen.head hcs (ih (st.complete a hj c hcs))

omit [Fintype Validator] in
/-- **A cut holds a record path's short history**: a block that a stored
block reaches in the record, at or above the horizon and at most `m`
rounds below it, lies within `m` steps of it in the store. -/
theorem IsCut.mem_historyUptoFrom [P.Mechanised] (hc : IsCut U st) {j i : BlockId} {m : ℕ}
    (hj : j ∈ st.ids) (hr : st.base ≤ (U.block i).round)
    (hm : (U.block j).round ≤ m + (U.block i).round) (h : ReachesFrom U.block j i) :
    i ∈ historyUptoFrom st.blk m j := by
  have hi : i ∈ st.ids := hc.down hr hj h
  exact mem_historyUptoFrom_of_round st.toRecord.causal hj
    (by change (st.blk j).round ≤ m + (st.blk i).round
        rw [← hc.round hj, ← hc.round hi]; exact hm)
    (hc.reachesFrom_store hr hj h)

end Cut

omit [Fintype Validator] in
/-- The slots proposed at round `r` have slot round `r`. -/
theorem slotRound_of_mem_slotsAt {k r : ℕ} (hk : k ∈ cfg.slotsAt r) :
    cfg.slots.slotRound k = r := by
  unfold Config.slotsAt at hk
  split at hk
  · rename_i hr
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hk
    have hi := List.mem_range.mp hi
    change cfg.per * ((cfg.m * (r / cfg.per) + i) / cfg.m) = r
    rw [Nat.mul_add_div cfg.m_pos, Nat.div_eq_of_lt hi, Nat.add_zero]
    exact Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hr)
  · simp at hk

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
to another whose horizon lies `Λ` or more below the references' round,
with `voteOffset ≤ Λ`: the leader blocks the tests read lie at or above
that horizon. -/
theorem ready_transfer [P.Mechanised] (hσ : cfg.σ = boundedSel) (hvo : cfg.p.voteOffset ≤ cfg.lag)
    (hct : cfg.p.voteIsCert = false → 1 ≤ cfg.p.certThreshold)
    {x Z : Store Validator BlockId Payload} (hx : IsCut U x) (hZ : IsCut U Z)
    {R R' : Finset BlockId} {n : ℕ} (hR : R ⊆ x.ids) (hRR : R ⊆ R') (hR'Z : R' ⊆ Z.ids)
    (hRn : ∀ j ∈ R, (x.blk j).round = n) (hZb : Z.base ≤ n - cfg.lag)
    (hreach : reachReady cfg x R n = true) (hcert : certReady cfg x R n = true) :
    reachReady cfg Z R' n = true ∧ certReady cfg Z R' n = true := by
  -- a candidate of the peer's store at or above `Z`'s horizon reached from a reference
  have hcand : ∀ k L, L ∈ candidatesIn (S := cfg.slots) x.toRecord x.view k →
      Z.base ≤ (U.block L).round → ∀ c ∈ R, ReachesFrom U.block c L →
      L ∈ candidatesIn (S := cfg.slots) Z.toRecord Z.view k ∧ L ∈ Z.ids := by
    intro k L hL hLb c hc hcL
    obtain ⟨hLx, hLc, hLr⟩ := Finset.mem_filter.mp hL
    have hLZ : L ∈ Z.ids := hZ.down hLb (hR'Z (hRR hc)) hcL
    refine ⟨Finset.mem_filter.mpr ⟨hLZ, ?_, ?_⟩, hLZ⟩
    · change (Z.blk L).creator = _
      rw [← hZ.creator hLZ, hx.creator hLx]; exact hLc
    · change (Z.blk L).round = _
      rw [← hZ.round hLZ, hx.round hLx]; exact hLr
  constructor
  · unfold reachReady at hreach ⊢
    refine List.all_eq_true.mpr fun m hm => ?_
    have h₁ := List.all_eq_true.mp hreach m hm
    have hm' := List.mem_range.mp hm
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
      have hLb : Z.base ≤ (U.block L).round := by
        rw [hx.round hLx]; have := hRn c hc; omega
      obtain ⟨hLZ, -⟩ := hcand k L hL hLb c hc hcL
      refine decide_eq_true ⟨L, hLZ, c, hRR hc, hZ.mem_historyUptoFrom (hR'Z (hRR hc)) hLb ?_ hcL⟩
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
          exact hvax.votes_iff (hR hb) (x.above b (hR hb)) hLx (x.above L hLx)
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
        have hLr : (U.block L).round = n - cfg.p.voteOffset := by
          rw [hx.round hLx]
          exact (Finset.mem_filter.mp hL).2.2.trans (slotRound_of_mem_slotsAt hk)
        have hLb : Z.base ≤ (U.block L).round := by rw [hLr]; omega
        obtain ⟨hLZ, hLZi⟩ := hcand k L hL hLb b hbR hbL
        obtain ⟨VZ, -, hVZ⟩ := hZ.extend ⟨∅, Finset.empty_subset _, fun i hi => absurd hi
          (Finset.notMem_empty _)⟩ (fun i hi => absurd hi (Finset.notMem_empty _))
        have hvaZ := ViewsAbove.of_store (st := Z) (V := VZ) hVZ (fun i hi => (hZ i hi).2)
        refine decide_eq_true ⟨L, hLZ, le_trans hcount (Finset.card_le_card fun a ha => ?_)⟩
        obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
        obtain ⟨hbR, hbv⟩ := Finset.mem_filter.mp hb
        have hbZ := hR'Z (hRR hbR)
        have hvZ : cfg.σ.Votes Z.toRecord b L := by
          rw [hσ]
          exact (hvaZ.votes_iff hbZ (Z.above b hbZ) hLZi (Z.above L hLZi)).mpr
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
    {X : Finset Validator} {c : BlockId} (hc : c ∈ st.ids) (hcr : (st.blk c).round = r + 1)
    (hcm : (st.blk c).creator ≠ cfg.me)
    (hready : reachReady cfg st (lent cfg st c o X) r = true ∧
      certReady cfg st (lent cfg st c o X) r = true)
    (hb : buildable cfg st r (lent cfg st c o X) = true) :
    reachReady cfg st (refsAt cfg st r o X) r = true ∧
      certReady cfg st (refsAt cfg st r o X) r = true := by
  unfold refsAt
  dsimp only
  split
  · rename_i h
    simpa only [Bool.and_eq_true] using h
  · set L := (((blocksAt st.toRecord (r + 1)).sort (· ≤ ·)).filter fun c =>
        decide ((st.blk c).creator ≠ cfg.me)).map (lent cfg st · o X) with hL
    have hmem : lent cfg st c o X ∈ L :=
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
round-`n + 1` block of another author outside `X`, whose references hold
`q` distinct authors one round below, lends them with the node's own
round-`n` block put in for its own, and they include the block's
references. -/
theorem lent_buildable {x Z : Store Validator BlockId Payload} (hx : IsCut U x) (hZ : IsCut U Z)
    {R : Finset BlockId} {n : ℕ} {z o : BlockId} {X : Finset Validator} (hR : R ⊆ x.ids)
    (hRq : cfg.q ≤ (creatorsOf x.blk R).card)
    (hRd : ∀ i ∈ R, ∀ j ∈ R, (x.blk i).creator = (x.blk j).creator → i = j)
    (hzZ : z ∈ Z.ids) (hzr : (Z.blk z).round = n + 1) (hzR : (Z.blk z).refs = R)
    (hzX : (Z.blk z).creator ∉ X) (hoZ : o ∈ Z.ids) (hor : (Z.blk o).round = n) (hoc : (Z.blk o).creator = cfg.me)
    (hme : cfg.me ∈ H)
    (hfresh : ∀ R, cfg.idOf ⟨n + 1, cfg.me, R, cfg.payload (n + 1)⟩ ∉ Z.ids) :
    R ⊆ lent cfg Z z (some o) X ∧ lent cfg Z z (some o) X ⊆ Z.ids ∧
      buildable cfg Z n (lent cfg Z z (some o) X) = true := by
  have hRZ : R ⊆ Z.ids := fun j hj => Z.complete z hzZ j (by rw [← hzR] at hj; exact hj)
  have hcre : ∀ j ∈ R, (Z.blk j).creator = (x.blk j).creator := fun j hj => by
    rw [← hZ.creator (hRZ hj), hx.creator (hR hj)]
  have hsub : R ⊆ lent cfg Z z (some o) X := by
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
      exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hjz, hjm,
        usable_of_ref hzZ (Z.pred z hzZ j hjz).symm hzX hjz⟩)
  -- the lent references: `z`'s other than the node's, and its own block
  have hlent : ∀ j ∈ lent cfg Z z (some o) X,
      (j ∈ (Z.blk z).refs ∧ (Z.blk j).creator ≠ cfg.me) ∨ j = o := by
    intro j hj
    rcases Finset.mem_union.mp hj with h | h
    · exact Or.inl ⟨(Finset.mem_filter.mp h).1, (Finset.mem_filter.mp h).2.1⟩
    · exact Or.inr (by simpa using h)
  have hlZ : lent cfg Z z (some o) X ⊆ Z.ids := fun j hj => by
    rcases hlent j hj with ⟨h, -⟩ | rfl
    · exact Z.complete z hzZ j h
    · exact hoZ
  have hlr : ∀ j ∈ lent cfg Z z (some o) X, (Z.blk j).round = n := fun j hj => by
    rcases hlent j hj with ⟨h, -⟩ | rfl
    · have := Z.pred z hzZ j h
      change (Z.blk j).round + 1 = (Z.blk z).round at this
      omega
    · exact hor
  refine ⟨hsub, hlZ, ?_⟩
  set b : Block Validator BlockId Payload := ⟨n + 1, cfg.me, lent cfg Z z (some o) X,
    cfg.payload (n + 1)⟩ with hb
  have hnin : ∀ j ∈ lent cfg Z z (some o) X, j ≠ cfg.idOf b :=
    fun j hj h => hfresh _ (h ▸ hlZ hj)
  have hZb : Z.base ≤ n := by have := Z.above o hoZ; change Z.base ≤ (Z.blk o).round at this; omega
  unfold buildable
  refine decide_eq_true ⟨hfresh _, by show Z.base ≤ n + 1; omega, fun _ => hlZ,
    fun _ j hj => by rw [hlr j hj], ⟨fun j hj => ?_, fun _ => ?_,
      fun i hi j hj hij => ?_⟩⟩
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

variable {tr : Trace Validator BlockId Payload} {v : Validator} (hl : cfg.limit = none)
  (hnv : ∀ i : ℕ, tr[i]? ≠ some (v, Input.restart))
include hl hnv

/-- **A node's own block stays stored** while its horizon lies at or below
the block's round. -/
theorem own_held {p : ℕ} {inp : Input Validator BlockId Payload} (hp : tr[p]? = some (v, inp))
    {e : BlockId × Block Validator BlockId Payload} (he : e ∈ persists (outputsAt cfg tr p))
    {E : ℕ} (hpE : p < E) (hb : (stateBefore cfg tr E v).store.base ≤ e.2.round) :
    e.1 ∈ (stateBefore cfg tr E v).store.ids := by
  have hk : KeepsBuilt (Node.step (cfg.at v) (stateBefore cfg tr p v) inp).2
      (Node.step (cfg.at v) (stateBefore cfg tr p v) inp).1 :=
    step_keeps_built hl (fired_before (cfg := cfg) hl hnv p).1 (fun h => hnv p (by rw [hp, h]))
  rw [outputsAt_eq hp] at he
  have hs : stateBefore cfg tr (p + 1) v =
      (Node.step (cfg.at v) (stateBefore cfg tr p v) inp).1 := by
    rw [stateBefore_succ hp, if_pos rfl]
  rw [← hs] at hk
  have hbE := (grows_before (cfg := cfg) (tr := tr) v (show p + 1 ≤ E by omega)).1
  rcases hk e he with ⟨hin, hr⟩ | hlt
  · exact (retains_before (cfg := cfg) hl hnv (show p + 1 ≤ E by omega) e.1 hin
      (by rw [hr]; exact hb)).1
  · omega

/-- **The horizon lies `Λ` or more below the top.** -/
theorem base_le_top_sub (E : ℕ) {t : ℕ} (ht : (stateBefore cfg tr E v).top = some t) :
    (stateBefore cfg tr E v).store.base ≤ t - cfg.lag := by
  rcases Nat.eq_zero_or_pos (stateBefore cfg tr E v).store.base with h0 | hpos
  · rw [h0]; exact Nat.zero_le _
  · obtain ⟨r, hrE, -, -, -, c, -, hcb⟩ := last_rise hl hnv E hpos
    have h₁ := (rises_before (cfg := cfg) hl hnv (show r + 1 ≤ E by omega)).1
    rw [ht] at h₁
    simp only [Option.getD_some] at h₁
    have := min_le_right (cfg.per * (c.height / cfg.m)) ((stateBefore cfg tr (r + 1) v).top.getD 0)
    omega

variable {time : ℕ → ℕ} (hmono : Live.TimeMono tr time)
include hmono

/-- **A node is at a round it built**, at any time after it built it. -/
theorem top_of_built {b : ℕ} {inp : Input Validator BlockId Payload}
    (hb : tr[b]? = some (v, inp)) {e : BlockId × Block Validator BlockId Payload}
    (he : e ∈ persists (outputsAt cfg tr b)) {τ : ℕ} (hbτ : time b ≤ τ) :
    (stateAt cfg tr time v τ).top.isSome ∧ e.2.round ≤ topAt cfg tr time v τ := by
  have hbl : b < tr.length := (List.getElem?_eq_some_iff.mp hb).1
  have hbE : b + 1 ≤ eventsBy tr time τ := (lt_eventsBy hmono hbl).mpr hbτ
  obtain ⟨t, ht, hrt⟩ := built_le_top hl hb he
  obtain ⟨h₁, h₂, -, -⟩ := rises_before (cfg := cfg) hl hnv hbE
  rw [ht] at h₁ h₂
  exact ⟨h₂ rfl, hrt.trans h₁⟩

/-- **A node at a round built it**, at its first event building it, by
then. -/
theorem built_of_top {τ n : ℕ} (hs : (stateAt cfg tr time v τ).top.isSome)
    (hn : n ≤ topAt cfg tr time v τ) :
    ∃ i inp e, tr[i]? = some (v, inp) ∧ e ∈ persists (outputsAt cfg tr i) ∧ e.2.round = n ∧
      builtAt cfg tr time v n = time i ∧ time i ≤ τ := by
  obtain ⟨b, hbE, hbv, e, he, her⟩ := built_by hl hnv (eventsBy tr time τ) hs hn
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
  obtain ⟨i, _inp, e, hi, he, her, hbt, -⟩ := built_of_top hl hnv hmono hs hn
  obtain ⟨t, ht, hrt⟩ := built_le_top hl hi he
  obtain ⟨b, hb, hbv, e', he', her'⟩ := built_by hl hnv (i + 1) (by rw [ht]; rfl)
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
    have := hcv; simp only [globalRecord, globalBlock_creator, hcont] at this; exact this
  have hxr : x.2.round = ((globalRecord hinjR hauthR).block x.1).round := by
    simp only [globalRecord, globalBlock_round, hcont]
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
by its author. -/
theorem built_mem (hl : cfg.limit = none) (hσ : cfg.σ = boundedSel) (hadm : cfg.Admissible) (hf : Hᶜ.card ≤ cfg.f)
    (htime : Converge.TimelyAuthentic cfg H tr) (hoff : Boot.TimelyOffers cfg H tr)
    (hcert : Boot.TimelyCerts cfg H tr) (hinj : Converge.HashInjective cfg H tr)
    (hchain : Boot.ChainInjective cfg H tr) {v : Validator} (hv : v ∈ H)
    (hnv : ∀ i : ℕ, tr[i]? ≠ some (v, Input.restart)) {p : ℕ}
    {inp : Input Validator BlockId Payload} (hp : tr[p]? = some (v, inp))
    {e : BlockId × Block Validator BlockId Payload} (he : e ∈ persists (outputsAt cfg tr p)) :
    e.1 ∈ (globalRecord (hashInjective_of_trace hinj) (authentic_of_timely htime)).ids ∧
      ((globalRecord (hashInjective_of_trace hinj) (authentic_of_timely htime)).block
        e.1).round = e.2.round ∧
      ((globalRecord (hashInjective_of_trace hinj) (authentic_of_timely htime)).block
        e.1).creator = v := by
  have hinjR := hashInjective_of_trace hinj
  have hauthR := authentic_of_timely htime
  have hK : e ∈ knownAll cfg H tr :=
    ⟨v, hv, List.mem_append_right _
      (mem_persists_iff.mpr (mem_outputs_of_event hp (mem_persists_iff.mp he)))⟩
  have hcont := content_of_known hinjR hK
  have hgood := ((Converge.inv_before (cfg := cfg) (tr := tr) (p + 1) v).good e
    (persists_of_event hp he)).2.1
  refine ⟨?_, by simp only [globalRecord, globalBlock_round, hcont],
    by simp only [globalRecord, globalBlock_creator, hcont]; exact hgood⟩
  by_cases h0 : e.2.round = 0
  · exact mem_globalIds.mpr ⟨mem_knownIds hK, by rw [hcont, h0]; trivial⟩
  obtain ⟨x, y, o, hbs, hb, heo⟩ := build_witness hl hσ hadm hf htime hoff hcert hinj hchain hv
    hnv hp he h0
  have hg := ground (cfg := cfg) hinjR hauthR hadm.2.2.2.1
  obtain ⟨r, id, b, hnew, hab, hrefs, hpred, -, -, -, -, -, hst, -, -, -, hout⟩ := tryBuild_some hb
  rw [hout, persists_built, List.mem_singleton] at heo
  have hy := BuildState.tryBuild (cfg := cfg.at v) hg hbs hb (fun e' he' => by
    rw [hout, persists_built, List.mem_singleton] at he'
    rw [he', ← heo]; exact hK)
  have hcy : e.1 ∈ y.store.ids := by rw [heo, hst]; exact Finset.mem_insert_self _ _
  exact (hy.cut e.1 hcy).1

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
3Δ + Δₛ` after a reliable peer built a round-`n + 1` block, having built
round `n` at most `A` after the peer, is above `n` then. It holds the
peer's block, and with it a quorum of round `n`; if the peer built on the
tests, `u` passes them with the references the block lends; if on the
round's timer, `u`'s has fired too. -/
theorem catches_up (hq : 2 ≤ cfg.q) (hl : cfg.limit = none) (hσ : cfg.σ = boundedSel)
    (hadm : cfg.Admissible) (hf : Hᶜ.card ≤ cfg.f) (hid : Function.Injective cfg.idOf)
    (htime : Converge.TimelyAuthentic cfg H tr) (hoff : Boot.TimelyOffers cfg H tr)
    (hcert : Boot.TimelyCerts cfg H tr) (hinj : Converge.HashInjective cfg H tr)
    (hchain : Boot.ChainInjective cfg H tr) (hTH : T ⊆ H) (hnr : Converge.NoRestart T tr)
    (hmono : Live.TimeMono tr time) (hdel : Live.DeliveredWithin cfg T tr time gst Δ t₁)
    (htimer : Live.TimersOnTime cfg T tr time t₁)
    (hsync : Live.SyncedWithin cfg H T tr time gst Δₛ t₁) (hvo : cfg.p.voteOffset ≤ cfg.lag)
    (hcmp : ∀ u ∈ T, ∀ v ∈ T, ∀ i j, (stateBefore cfg tr i u).decided.reverse <+:
      (stateBefore cfg tr j v).decided.reverse ∨
        (stateBefore cfg tr j v).decided.reverse <+: (stateBefore cfg tr i u).decided.reverse)
    {u w : Validator} (hu : u ∈ T) (hw : w ∈ T) (huw : u ≠ w) {n i : ℕ}
    {inp : Input Validator BlockId Payload} (hi : tr[i]? = some (w, inp))
    {e : BlockId × Block Validator BlockId Payload} (he : e ∈ persists (outputsAt cfg tr i))
    (her : e.2.round = n + 1) (hgi : gst ≤ time i)
    (hus : (stateAt cfg tr time u (time i + (3 * Δ + Δₛ))).top.isSome)
    (hun : n ≤ topAt cfg tr time u (time i + (3 * Δ + Δₛ)))
    (hbu : builtAt cfg tr time u n ≤ builtAt cfg tr time w n + (3 * Δ + Δₛ))
    (ht₁ : time i + (3 * Δ + Δₛ) ≤ t₁) {X : Finset Validator}
    (hex : ∀ v ∈ T, ∀ k, time i ≤ time k → (stateBefore cfg tr (k + 1) v).exposed = X) :
    n + 1 ≤ topAt cfg tr time u (time i + (3 * Δ + Δₛ)) := by
  have hnu : ∀ k : ℕ, tr[k]? ≠ some (u, Input.restart) := fun k => hnr k u hu
  have hnw : ∀ k : ℕ, tr[k]? ≠ some (w, Input.restart) := fun k => hnr k w hw
  have hil : i < tr.length := (List.getElem?_eq_some_iff.mp hi).1
  set τ := time i + (3 * Δ + Δₛ) with hτ
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
  -- the exposed authors: `X` at both nodes
  have hiE : i < E := (lt_eventsBy hmono hil).mpr (by omega)
  have hZX : (stateBefore cfg tr E u).exposed = X := by
    obtain ⟨k, hk⟩ : ∃ k, E = k + 1 := ⟨E - 1, by omega⟩
    have hkl : k < tr.length := by have := eventsBy_le_length (tr := tr) (time := time) τ; omega
    rw [hk]
    exact hex u hu k (hmono i k (by omega) hkl)
  set Z := stateBefore cfg tr E u with hZ
  have hSet : Settled (cfg.at u) Z := by
    rcases settled_before (cfg := cfg) hl hq hnu E with h | h
    · rw [hZt] at h; cases h
    · exact h
  have hZcut := (cut_before hσ hadm hf htime hoff hcert hinj hchain E u (hTH hu)).1
  have hZb : Z.store.base ≤ n - cfg.lag := base_le_top_sub hl hnu E hZt
  obtain ⟨o, hoo, hoi, hor, hoc⟩ := ownTop_before (cfg := cfg) hl hnu E n hZt
  -- the peer's build
  obtain ⟨x, y, out, hbs, hb, heo⟩ := build_witness hl hσ hadm hf htime hoff hcert hinj hchain
    (hTH hw) hnw hi he (by omega)
  obtain ⟨r, hxt, -, hexit, hout⟩ := tryBuild_exit hb
  obtain ⟨r', id, b, hnew, -, hrefs, hpred, hxt', hbr, -, -, hrv, -, -, -, -, hout'⟩ :=
    tryBuild_some hb
  rw [hxt] at hxt'
  cases hxt'
  have hAB := congrArg persists (hout.symm.trans hout')
  rw [persists_built, persists_built, List.singleton_inj] at hAB
  rw [hout', persists_built, List.mem_singleton] at heo
  subst heo
  have hrn : r = n := by simp only at her; omega
  subst hrn
  have hbR : b.refs = refsAt (cfg.at w) x.store r x.own x.exposed := by
    have := congrArg (fun e => e.2.refs) hAB
    simp only at this
    exact this.symm
  have hxX : x.exposed = X := by
    rw [hbs.exposed]
    have := hex w hw i le_rfl
    rwa [stateBefore_succ hi, if_pos rfl] at this
  set R := refsAt (cfg.at w) x.store r x.own x.exposed with hRdef
  have hxb : x.store.base < b.round := by have := hbs.held.le_top r hxt; omega
  have hRx : R ⊆ x.store.ids := hbR ▸ hrefs hxb
  have hRn : ∀ j ∈ R, (x.store.blk j).round = r := fun j hj => by
    have := hpred hxb j (hbR ▸ hj); omega
  obtain ⟨hRq, hRd⟩ := refs_of_rowValid (cfg := cfg.at w) hnew (hrefs hxb) (by omega) hrv
  rw [hbR] at hRq hRd
  -- the peer's block arrives
  obtain ⟨hzZ, hzr, hzc, hzb⟩ := block_arrives hl hq hσ hadm hf htime hoff hcert hinj hchain hTH
    hnr hmono hdel hsync hcmp hw hu (Ne.symm huw) hi he (s := time i) le_rfl (τ := τ)
    (by rw [max_eq_left hgi]; omega) ht₁ hZt (le_of_eq hbr)
    (by change Z.store.base ≤ b.round; omega)
  change (id, b).1 ∈ Z.store.ids at hzZ
  change (Z.store.blk (id, b).1).round = (id, b).2.round at hzr
  change (Z.store.blk (id, b).1).creator = w at hzc
  change Z.store.blk (id, b).1 = atBase Z.store.base (id, b).2 at hzb
  simp only at hzZ hzr hzc hzb her
  have hZR : (Z.store.blk id).refs = R := by
    rw [hzb, atBase_of_lt (show Z.store.base < b.round by omega), hbR]
  -- a quorum of round `r`
  have hRZ : ∀ j ∈ R, j ∈ Z.store.ids ∧ (Z.store.blk j).round = r := fun j hj => by
    have hj' : j ∈ (Z.store.blk id).refs := by rw [hZR]; exact hj
    have := Z.store.pred id hzZ j hj'
    change (Z.store.blk j).round + 1 = (Z.store.blk id).round at this
    exact ⟨Z.store.complete id hzZ j hj', by omega⟩
  have hcre : creatorsOf Z.store.blk R = creatorsOf x.store.blk R :=
    Finset.image_congr fun j hj => by
      change (Z.store.blk j).creator = (x.store.blk j).creator
      rw [← hZcut.creator (hRZ j hj).1, hbs.cut.creator (hRx hj)]
  -- the peer is not exposed at `u`, so `u` may reference what its block references
  have hzX : (Z.store.blk id).creator ∉ Z.exposed := by
    rw [hzc]; exact honest_not_exposed hinj htime (hTH hu) E (hTH hw)
  have hcard : cfg.q ≤ (usableAuthors Z.store Z.exposed r).card := by
    refine le_trans hRq (le_trans (le_of_eq (congrArg Finset.card hcre.symm))
      (Finset.card_le_card fun a ha => ?_))
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp ha
    have hj' : j ∈ (Z.store.blk id).refs := by rw [hZR]; exact hj
    exact mem_usableAuthors.mpr ⟨j, (hRZ j hj).1, (hRZ j hj).2,
      usable_of_ref hzZ (Z.store.pred id hzZ j hj').symm hzX hj', rfl⟩
  have hfresh := fresh_before hl hid htime (hTH hu) hZt
  -- the timer has fired, or the lent references pass the tests
  have hgo : r ∈ Z.fired ∨
      (reachReady (cfg.at u) Z.store (refsAt (cfg.at u) Z.store r Z.own Z.exposed) r = true ∧
        certReady (cfg.at u) Z.store (refsAt (cfg.at u) Z.store r Z.own Z.exposed) r = true) := by
    rcases hexit with ⟨hre, hce⟩ | ⟨hfx, -⟩
    · right
      obtain ⟨hRR, hlZ, hlb⟩ := lent_buildable (cfg := cfg.at u) hbs.cut hZcut hRx hRq hRd
        hzZ (hzr.trans hbr) hZR hzX hoi hor hoc (hTH hu) hfresh
      have hready := ready_transfer (cfg := cfg.at u) hσ hvo (fun h => certThreshold_pos hadm h)
        hbs.cut hZcut hRx hRR hlZ hRn hZb hre hce
      rw [hoo]
      exact refsAt_ready (cfg := cfg.at u) hzZ (hzr.trans hbr) (by rw [hzc]; exact Ne.symm huw)
        hready hlb
    · left
      obtain ⟨j, hj, hjt⟩ : ∃ j ≤ i, tr[j]? = some (w, Input.timer r) := by
        rcases hbs.fired _ hfx with h | h
        · obtain ⟨j, hj, hjt⟩ := (fired_before (cfg := cfg) hl hnw i).2 _ h
          exact ⟨j, hj.le, hjt⟩
        · exact ⟨i, le_rfl, by rw [hi, h]⟩
      have hwt := timer_after_built time hl hmono htimer hw hnw hil hj hjt
      obtain ⟨bu, inpu, eu, hbu', heu, heur, hbut, -⟩ := built_of_top hl hnu hmono hus hun
      have hset := timer_of_persist hl hnu hbu' heu
      rw [heur] at hset
      obtain ⟨f, -, hfe, htf⟩ := htimer.1 bu u inpu hbu' hu r (cfg.timeout r) hset (by omega)
      have hfl : f < tr.length := (List.getElem?_eq_some_iff.mp hfe).1
      have hfE : f < E := (lt_eventsBy hmono hfl).mpr (by omega)
      exact fired_stays hl hnu hfe E hfE (by rw [hZt]; simp)
  have hsome := tryBuild_isSome (cfg := cfg.at u) hZt hgo hcard
    (fun j hj => by rw [hoo] at hj; cases hj; exact ⟨hoi, hor, hoc⟩) (by omega) hfresh
  rw [hSet.build] at hsome
  cases hsome

end Catch

/-! ## The drift of build times -/

section Drift

variable {T : Finset Validator} {tr : Trace Validator BlockId Payload} {time : ℕ → ℕ}
  {gst Δ Δₛ t₁ : ℕ}

/-- **A reliable node has started** at any time from GST on. -/
theorem started_at (hl : cfg.limit = none) (hadm : cfg.Admissible) (hid : Function.Injective cfg.idOf)
    (htime : Converge.TimelyAuthentic cfg H tr) (hTH : T ⊆ H) (hnr : Converge.NoRestart T tr)
    (hmono : Live.TimeMono tr time) (hstart : Live.StartedBy T tr time gst) {v : Validator}
    (hv : v ∈ T) {τ : ℕ} (hτ : gst ≤ τ) : (stateAt cfg tr time v τ).top.isSome := by
  obtain ⟨st, hst, htst⟩ := hstart v hv
  have hstl : st < tr.length := (List.getElem?_eq_some_iff.mp hst).1
  have hstE : st + 1 ≤ eventsBy tr time τ := (lt_eventsBy hmono hstl).mpr (by omega)
  exact (rises_before (cfg := cfg) hl (fun k => hnr k v hv) hstE).2.1
    (started_after hl hadm hid htime (hTH hv) hst)

/-- A node at a round built it by then. -/
theorem builtAt_le_of_top (hl : cfg.limit = none) {v : Validator} (hnv : ∀ i : ℕ, tr[i]? ≠ some (v, Input.restart))
    (hmono : Live.TimeMono tr time) {τ n : ℕ} (hs : (stateAt cfg tr time v τ).top.isSome)
    (hn : n ≤ topAt cfg tr time v τ) : builtAt cfg tr time v n ≤ τ := by
  obtain ⟨i, -, -, -, -, -, hbt, hiτ⟩ := built_of_top hl hnv hmono hs hn
  omega

/-- **Drift stays within `A = 3Δ + Δₛ`**: past GST, if the reliable nodes
built round `n₀` within `A` of each other, they build every round from
`n₀` up to one they all reach by `t` within `A` of each other
(`catches_up`). -/
theorem drift (hq : 2 ≤ cfg.q) (hl : cfg.limit = none) (hσ : cfg.σ = boundedSel)
    (hadm : cfg.Admissible) (hf : Hᶜ.card ≤ cfg.f) (hid : Function.Injective cfg.idOf)
    (htime : Converge.TimelyAuthentic cfg H tr) (hoff : Boot.TimelyOffers cfg H tr)
    (hcert : Boot.TimelyCerts cfg H tr) (hinj : Converge.HashInjective cfg H tr)
    (hchain : Boot.ChainInjective cfg H tr) (hTH : T ⊆ H) (hnr : Converge.NoRestart T tr)
    (hmono : Live.TimeMono tr time) (hdel : Live.DeliveredWithin cfg T tr time gst Δ t₁)
    (htimer : Live.TimersOnTime cfg T tr time t₁)
    (hsync : Live.SyncedWithin cfg H T tr time gst Δₛ t₁) (hstart : Live.StartedBy T tr time gst)
    (hvo : cfg.p.voteOffset ≤ cfg.lag)
    (hcmp : ∀ u ∈ T, ∀ v ∈ T, ∀ i j, (stateBefore cfg tr i u).decided.reverse <+:
      (stateBefore cfg tr j v).decided.reverse ∨
        (stateBefore cfg tr j v).decided.reverse <+: (stateBefore cfg tr i u).decided.reverse)
    {n₀ s : ℕ} (hgs : gst ≤ s)
    (h₀ : ∀ v ∈ T, s ≤ builtAt cfg tr time v n₀ ∧ builtAt cfg tr time v n₀ ≤ s + (3 * Δ + Δₛ))
    {t N : ℕ} (hst : ∀ v ∈ T, (stateAt cfg tr time v t).top.isSome)
    (hN : ∀ v ∈ T, N ≤ topAt cfg tr time v t) (ht₁ : t + (3 * Δ + Δₛ) ≤ t₁) {X : Finset Validator}
    (hex : ∀ v ∈ T, ∀ k, s ≤ time k → (stateBefore cfg tr (k + 1) v).exposed = X) :
    ∀ n, n₀ ≤ n → n ≤ N → ∀ u ∈ T, ∀ w ∈ T, s ≤ builtAt cfg tr time u n ∧
      builtAt cfg tr time u n ≤ builtAt cfg tr time w n + (3 * Δ + Δₛ) := by
  intro n hn₀ hnN
  induction n, hn₀ using Nat.le_induction with
  | base =>
    intro u hu w hw
    exact ⟨(h₀ u hu).1, (h₀ u hu).2.trans (by have := (h₀ w hw).1; omega)⟩
  | succ n hn₀ ih =>
    have ih := ih (by omega)
    intro u hu w hw
    have hnu : ∀ k : ℕ, tr[k]? ≠ some (u, Input.restart) := fun k => hnr k u hu
    have hnw : ∀ k : ℕ, tr[k]? ≠ some (w, Input.restart) := fun k => hnr k w hw
    have hgu : s ≤ builtAt cfg tr time u (n + 1) :=
      (ih u hu u hu).1.trans (builtAt_le_succ hl hnu hmono (hst u hu) ((hN u hu).trans' hnN))
    refine ⟨hgu, ?_⟩
    by_cases huw : u = w
    · subst huw; omega
    -- the peer's first build of round `n + 1`
    obtain ⟨i, inp, e, hi, he, her, hbt, hit⟩ :=
      built_of_top hl hnw hmono (hst w hw) ((hN w hw).trans' hnN)
    have hgw : s ≤ builtAt cfg tr time w (n + 1) :=
      (ih w hw w hw).1.trans (builtAt_le_succ hl hnw hmono (hst w hw) ((hN w hw).trans' hnN))
    have hwn := builtAt_le_succ hl hnw hmono (hst w hw) ((hN w hw).trans' hnN)
    have hus := started_at hl hadm hid htime hTH hnr hmono hstart hu
      (τ := time i + (3 * Δ + Δₛ)) (by omega)
    -- `u` built round `n` by then
    obtain ⟨bu, _inpu, eu, hbu, heu, heur, hbut, -⟩ :=
      built_of_top hl hnu hmono (hst u hu) ((hN u hu).trans' (by omega : n ≤ N))
    have hun := (top_of_built hl hnu hmono hbu heu (τ := time i + (3 * Δ + Δₛ))
      (by have := (ih u hu w hw).2; omega)).2
    rw [heur] at hun
    have hup := catches_up hq hl hσ hadm hf hid htime hoff hcert hinj hchain hTH hnr hmono hdel
      htimer hsync hvo hcmp hu hw huw hi he her (by omega) hus hun (ih u hu w hw).2 (by omega)
      fun v hv k hk => hex v hv k (by omega)
    have := builtAt_le_of_top hl hnu hmono hus hup
    omega

end Drift

end Node

end LeanDag
