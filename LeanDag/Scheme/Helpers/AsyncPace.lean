import LeanDag.Scheme.Model.AsyncPace
import LeanDag.Scheme.Helpers.AsyncCoin
/-!
# The family, paced asynchronously: local commit

Eventual delivery is enough for every argument here, because what has to
be delivered is finite. Finitely many blocks, each eventually held, are
held together from some time on (`exists_time`), since holdings only grow.
So a reliable set of `q` validators reaches every round below the horizon
(`reached`): the round-`n` blocks of the reliable set are eventually held,
which is `q` authors, and the progress rule moves past round `n`. Every
reliable block of the record is then held by every reliable validator from
some time on (`delivered`).

On such a view a safe leader's slot commits directly (`decided_of_safe`):
every reliable decision-round block certifies the safe block
(`isCert_of_safe`), and the view holds them all. The window and run
results follow on one view, at the delivery time. A uniform coin names a
leader whose slot so commits with probability at least the safe set's
density (`coin_eventuallyCommits`).
-/

namespace LeanDag

namespace Scheme

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [LinearOrder BlockId] {Payload : Type}
variable {P : Validity Validator BlockId Payload} {honest : Finset Validator}
variable {U : BlockRecord Validator BlockId Payload P honest} {T : Finset Validator} {N qp : ℕ}

namespace AsyncPace

variable (ap : AsyncPace qp U T N)

omit [Fintype Validator] in
/-- **Finitely many eventual holdings are eventually held together.** -/
theorem exists_time (X : Finset (BlockId × Validator))
    (h : ∀ x ∈ X, ∃ t, x.1 ∈ ap.holds x.2 t) : ∃ t, ∀ x ∈ X, x.1 ∈ ap.holds x.2 t := by
  classical
  induction X using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert a X _ ih =>
    obtain ⟨t₁, h₁⟩ := h a (Finset.mem_insert_self _ _)
    obtain ⟨t₂, h₂⟩ := ih fun x hx => h x (Finset.mem_insert_of_mem hx)
    refine ⟨max t₁ t₂, fun x hx => ?_⟩
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact ap.holds_mono _ _ _ (le_max_left _ _) h₁
    · exact ap.holds_mono _ _ _ (le_max_right _ _) (h₂ x hx)

omit [Fintype Validator] [LinearOrder BlockId] in
/-- **A reliable block reaches every reliable validator**, at some time. -/
theorem eventually_held {v : Validator} (hv : v ∈ T) {b : BlockId} (hb : b ∈ U.ids)
    (hbT : (U.block b).creator ∈ T) : ∃ t, b ∈ ap.holds v t := by
  obtain ⟨t, ht⟩ := ap.holds_own _ hbT b hb rfl
  obtain ⟨d, hd⟩ := ap.converges v hv _ hbT t
  exact ⟨t + d, hd ht⟩

omit [Fintype Validator] in
/-- **Every reliable block is held by every reliable validator** from some
time on. -/
theorem delivered : ∃ t, ∀ t', t ≤ t' → ∀ v ∈ T, ∀ b ∈ U.ids,
    (U.block b).creator ∈ T → b ∈ ap.holds v t' := by
  classical
  obtain ⟨t, ht⟩ := ap.exists_time ((U.ids.filter fun b => (U.block b).creator ∈ T) ×ˢ T)
    fun x hx => by
      obtain ⟨hb, hv⟩ := Finset.mem_product.mp hx
      obtain ⟨hbU, hbT⟩ := Finset.mem_filter.mp hb
      exact ap.eventually_held hv hbU hbT
  exact ⟨t, fun t' htt' v hv b hb hbT => ap.holds_mono v _ _ htt'
    (ht (b, v) (Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨hb, hbT⟩, hv⟩))⟩

omit [Fintype Validator] in
/-- **Every reliable validator reaches every round below the horizon**, when
the reliable set is `qp` strong. -/
theorem reached (hq : qp ≤ T.card) : ∀ n ≤ N, ∀ v ∈ T, n ≤ ap.top v := by
  obtain ⟨t, ht⟩ := ap.delivered
  intro n
  induction n with
  | zero => intro _ v _; omega
  | succ n ih =>
      intro hn v hv
      refine Nat.succ_le_of_lt (ap.advancesAt v hv n (by omega) t
        (le_trans hq (Finset.card_le_card fun w hw => ?_)))
      obtain ⟨b, hb, hbc, hbr⟩ := ap.built_of_le_top w hw n (ih (by omega) w hw)
      exact mem_authorsIn.mpr ⟨b, ht t le_rfl v hv b hb (hbc ▸ hw), hbr, hbc⟩

omit [Fintype Validator] in
include ap in
/-- **Production**: every round below the horizon has a block by every
reliable validator. -/
theorem populated (hq : qp ≤ T.card) : ∀ n ≤ N, PopulatedOn U T n :=
  fun n hn v hv => ap.built_of_le_top v hv n (ap.reached hq n hn v hv)

end AsyncPace

section Commit

variable [P.Mechanised] {q : ℕ} [P.Quorate q] {p : Params}
variable (σ : VoteSel Validator BlockId Payload P honest) [S : Slots Validator]

/-- **A safe leader's slot commits on a view holding the reliable
decision-round blocks**, when they meet the commit threshold. -/
theorem decided_of_safe_of_holds {k : ℕ} (hw : 2 ≤ p.waveLength)
    (hcv : p.voteIsCert = false → 3 ≤ p.waveLength ∧ p.certThreshold ≤ q)
    (hcm : p.commitThreshold ≤ T.card)
    (hpop : PopulatedOn U T (S.slotRound k + (p.waveLength - 1)))
    (hk : S.leader k ∈ safe p U k) {V : U.View}
    (hV : ∀ b ∈ U.ids, (U.block b).creator ∈ T → b ∈ V.ids) :
    ∃ L, IsLeaderBlock U k L ∧ (schemeAnchored p σ).Decided U V k (some L) := by
  obtain ⟨hLh, L, hL, hLr, hLc, hsafe⟩ := mem_safeAt.mp hk
  exact ⟨L, ⟨hL, hLr, hLc⟩, AnchoredRule.Decided.directCommit ⟨hL, hLr, hLc⟩
    (commit_of_certified hcm hpop fun C hC hCT hCr =>
      ⟨isCert_of_safe σ hw hcv hL hLr (hLc ▸ hLh) hsafe hC hCr, hV C hC hCT⟩)⟩

namespace AsyncPace

variable (ap : AsyncPace qp U T N)

/-- **A safe leader's slot commits on every reliable validator's own
view**, from some time on. -/
theorem decided_of_safe {k : ℕ} (hw : 2 ≤ p.waveLength)
    (hcv : p.voteIsCert = false → 3 ≤ p.waveLength ∧ p.certThreshold ≤ q)
    (hcm : p.commitThreshold ≤ T.card) (hq : qp ≤ T.card)
    (hN : S.slotRound k + (p.waveLength - 1) ≤ N) (hk : S.leader k ∈ safe p U k) :
    ap.EventuallyCommits p σ k := by
  obtain ⟨t, ht⟩ := ap.delivered
  obtain ⟨hLh, L, hL, hLr, hLc, hsafe⟩ := mem_safeAt.mp hk
  refine ⟨L, ⟨hL, hLr, hLc⟩, t, fun t' htt' v hv => ?_⟩
  obtain ⟨L', hL', hdec⟩ := decided_of_safe_of_holds σ hw hcv hcm (ap.populated hq _ hN) hk
    (V := ap.viewAt hv t') fun b hb hbT => ht t' htt' v hv b hb hbT
  rwa [U.eq_of_creator_eq hL'.1 hL hLh hL'.2.2 hLc (hL'.2.1.trans hLr.symm)] at hdec

/-- **Every window commits on every reliable validator's own view** under
the safe single-hit clause, from some time on. -/
theorem commitsWithin {c : ℕ} (hw : 2 ≤ p.waveLength)
    (hcv : p.voteIsCert = false → 3 ≤ p.waveLength ∧ p.certThreshold ≤ q)
    (hcm : p.commitThreshold ≤ T.card) (hq : qp ≤ T.card) (hU : SafeWithin p σ U c N) :
    ∃ t, ∀ t', t ≤ t' → ∀ v (hv : v ∈ T), ∀ k,
      (schemeAnchored p σ).decisionRound (k + c) ≤ N →
      ∃ k', k ≤ k' ∧ k' < k + c ∧ ∃ L, IsLeaderBlock U k' L ∧
        (schemeAnchored p σ).Decided U (ap.viewAt hv t') k' (some L) := by
  obtain ⟨t, ht⟩ := ap.delivered
  refine ⟨t, fun t' htt' v hv k hk => ?_⟩
  obtain ⟨k', h1, h2, hs⟩ := hU k hk
  have hmono := S.mono (show k' ≤ k + c by omega)
  have hdec : (schemeAnchored p σ).decisionRound (k + c) =
      S.slotRound (k + c) + (p.waveLength - 1) := rfl
  exact ⟨k', h1, h2, decided_of_safe_of_holds σ hw hcv hcm (ap.populated hq _ (by omega)) hs
    fun b hb hbT => ht t' htt' v hv b hb hbT⟩

/-- **Every slot below a safe run is decided on every reliable validator's
own view**, when a run of `d` slots spans eligibility, from some time on. -/
theorem allDecidedBelow {c d : ℕ} (hd : 0 < d) (hw : 2 ≤ p.waveLength)
    (hcv : p.voteIsCert = false → 3 ≤ p.waveLength ∧ p.certThreshold ≤ q)
    (hcm : p.commitThreshold ≤ T.card) (hq : qp ≤ T.card)
    (hspan : (schemeAnchored p σ).SpansEligible (S := S) d) (hU : SafeRunWithin p σ U c d N) :
    ∃ t, ∀ t', t ≤ t' → ∀ v (hv : v ∈ T), ∀ k,
      (schemeAnchored p σ).decisionRound (k + c + d - 1) ≤ N →
      ∃ b, k ≤ b ∧ ∀ i, i < b → ∃ w, (schemeAnchored p σ).Decided U (ap.viewAt hv t') i w := by
  obtain ⟨t, ht⟩ := ap.delivered
  refine ⟨t, fun t' htt' v hv k hk => ?_⟩
  obtain ⟨k', hk', hk'c, hrun⟩ := hU k hk
  have hdec : (schemeAnchored p σ).decisionRound (k + c + d - 1) =
      S.slotRound (k + c + d - 1) + (p.waveLength - 1) := rfl
  refine ⟨k', hk', AnchoredRule.decided_below_of_run
    (fun _ h => AnchoredRule.exists_least_of_lt (fun _ _ => Iff.rfl) h) hd hspan
    (Led := fun j => S.leader j ∈ safe p U j) hrun fun j _ h2 hj => ?_⟩
  have hmono := S.mono (show j ≤ k + c + d - 1 by omega)
  obtain ⟨L, -, hL⟩ := decided_of_safe_of_holds σ hw hcv hcm (ap.populated hq _ (by omega)) hj
    (V := ap.viewAt hv t') fun b hb hbT => ht t' htt' v hv b hb hbT
  exact ⟨L, hL⟩

omit S in
open scoped ENNReal in
/-- **The coin names a leader whose slot eventually commits** on every
reliable validator's own view, with probability at least `1/n` at one
buffer round and `(q − f)/n` at two or more, at a row ready for the count
and a reliable set at least `q` strong. The coin's outcome `v` is the
schedule `elect v`, which makes `v` the leader of slot `k` at round `r`. -/
theorem coin_eventuallyCommits [Nonempty Validator] {f b r k : ℕ} (ap : AsyncPace q U T N)
    (hf : honestᶜ.card ≤ f) (hp : p.AsyncReady (Fintype.card Validator) f q b)
    (hq : q ≤ T.card) (elect : Validator → Slots Validator)
    (helect : ∀ v, (elect v).leader k = v ∧ (elect v).slotRound k = r)
    (hN : r + (p.waveLength - 1) ≤ N) :
    (1 ≤ b → (1 : ℝ≥0∞) / Fintype.card Validator ≤
      (PMF.uniformOfFintype Validator).toOuterMeasure
        {v | ap.EventuallyCommits (S := elect v) p σ k}) ∧
    (2 ≤ b → ((q - f : ℕ) : ℝ≥0∞) / Fintype.card Validator ≤
      (PMF.uniformOfFintype Validator).toOuterMeasure
        {v | ap.EventuallyCommits (S := elect v) p σ k}) := by
  obtain ⟨hq2, hvo, hw, hcv, hcm⟩ := hp
  have hvw : p.voteOffset ≤ p.waveLength - 1 := by unfold Params.voteOffset; split <;> omega
  have hT : T.Nonempty := Finset.card_pos.mp (lt_of_lt_of_le (Validity.Quorate.pos P) hq)
  have hsub : (↑(safeAt p U r) : Set Validator) ⊆
      {v | ap.EventuallyCommits (S := elect v) p σ k} := fun v hv => by
    obtain ⟨hl, hr⟩ := helect v
    refine ap.decided_of_safe (S := elect v) σ hw hcv (le_trans hcm hq) hq (by omega) ?_
    change (elect v).leader k ∈ safeAt p U ((elect v).slotRound k)
    rw [hl, hr]; exact hv
  have hmono := (PMF.uniformOfFintype Validator).toOuterMeasure.mono hsub
  refine ⟨fun hb => le_trans ?_ hmono, fun hb => le_trans ?_ hmono⟩
  · obtain ⟨v, hv⟩ := safeAt_nonempty (p := p) hf hq2 (by omega) hT
      (ap.populated hq (r + 2) (by omega))
    exact_mod_cast floor_le_coin (G := safeAt p U r) (c := 1) (Finset.card_pos.mpr ⟨v, hv⟩)
  · exact floor_le_coin (by
      have := le_card_safeAt (p := p) hf hq2 (by omega) hT (ap.populated hq (r + 3) (by omega))
      omega)

end AsyncPace

end Commit

end Scheme

end LeanDag
