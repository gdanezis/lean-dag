import LeanDag.Scheme.Helpers.Deliver
import LeanDag.Scheme.Helpers.AsyncLive
import LeanDag.Scheme.Helpers.Support
import LeanDag.Scheme.Loop.Proof
/-!
# Validity — lemmas

* `reaches_own`: on records whose blocks reference their author's
  previous block, an honest author's block reaches each of its earlier
  blocks.
* `reaches_of_onTime`: when every reliable block of round `r + 1` reaches
  `x` and the quorum and the reliable set together exceed `n`, every block
  from round `r + 2` on reaches `x`.
* `decided_of_certified`: a leader block certified by every reliable
  decision-round block commits on a view holding the reliable blocks.
* `mem_deliverSeq_of_decided`: on a view where every slot up to `k` is
  decided and `k` commits a leader reaching an honest block `b`, the
  delivered sequence holds `b` once the scan reaches far enough.
* `eventually_committed_of_good_block`: a block of safe coins commits its
  first slot and decides every slot below it, on every reliable
  validator's own view from some time on.
-/

namespace LeanDag

namespace Scheme

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [LinearOrder BlockId] {Payload : Type}
variable {P : Validity Validator BlockId Payload} {honest : Finset Validator}
variable [P.Mechanised] {U : BlockRecord Validator BlockId Payload P honest}

omit [Fintype Validator] [LinearOrder BlockId] in
/-- **An honest author's block reaches its earlier blocks**, on records
whose blocks reference their author's previous block. -/
theorem reaches_own (hP : ∀ blk b, P blk b → Clause.selfParent blk b) {b c : BlockId}
    (hb : b ∈ U.ids) (hc : c ∈ U.ids) (hbh : (U.block b).creator ∈ honest)
    (hcc : (U.block c).creator = (U.block b).creator)
    (hle : (U.block b).round ≤ (U.block c).round) : Reaches U c b := by
  obtain ⟨d, hd⟩ : ∃ d, (U.block c).round = (U.block b).round + d :=
    ⟨_, (Nat.add_sub_cancel' hle).symm⟩
  induction d generalizing c with
  | zero =>
    have : b = c := U.no_equivocation b hb c hc hbh hcc.symm (by omega)
    subst this
    exact Reaches.refl
  | succ d ih =>
    obtain ⟨i, hi, hic⟩ := hP U.block (U.block c) (U.valid c hc) (by omega)
    have hiU := U.complete c hc i hi
    have hir := Validity.Mechanised.pred U.block (U.block c) (U.valid c hc) i hi
    exact (Reaches.single hi).trans (ih hiU (hic.trans hcc) (by omega) (by omega))

omit [LinearOrder BlockId] in
/-- **A block that every reliable block of round `r + 1` reaches is reached
by every block from round `r + 2` on**, when the quorum and the reliable
set together exceed the committee. -/
theorem reaches_of_onTime {q : ℕ} [P.Quorate q] {T : Finset Validator}
    (hqT : Fintype.card Validator < q + T.card) {x : BlockId} {r : ℕ}
    (hon : ∀ c ∈ U.ids, (U.block c).creator ∈ T → (U.block c).round = r + 1 → Reaches U c x) :
    ∀ c ∈ U.ids, r + 2 ≤ (U.block c).round → Reaches U c x := by
  suffices h : ∀ n, ∀ c ∈ U.ids, (U.block c).round = r + 2 + n → Reaches U c x by
    intro c hc hr
    exact h _ c hc (Nat.add_sub_cancel' hr).symm
  intro n
  induction n with
  | zero => ?_
  | succ n ih => ?_
  all_goals
    intro c hc hcr
    have hquo := Validity.Quorate.quorum U.block (U.block c) (U.valid c hc) (by omega)
    obtain ⟨i, hi, hiT⟩ : ∃ i ∈ (U.block c).refs, (U.block i).creator ∈ T := by
      by_contra hno
      push Not at hno
      have hsub : creators U.block (U.block c) ⊆ Tᶜ := by
        intro v hv
        obtain ⟨i, hi, rfl⟩ := mem_creatorsOf.mp hv
        exact Finset.mem_compl.mpr (hno i hi)
      have := Finset.card_le_card hsub
      rw [Finset.card_compl] at this
      have := Finset.card_le_univ T
      omega
    have hiU := U.complete c hc i hi
    have hir := Validity.Mechanised.pred U.block (U.block c) (U.valid c hc) i hi
    refine (Reaches.single hi).trans ?_
  · exact hon i hiU hiT (by omega)
  · exact ih i hiU (by omega)

omit [LinearOrder BlockId] in
/-- **Under the weak-reference rule, a block every reliable validator holds
by time `t` is reached by every block from round `t + 2` on**, when the
quorum and the reliable set together exceed the committee and a reliable
block of round `r` is built at time `r` or later: such a block references a
reliable block of round `t + 1` or later, built after `t`, which reaches
the held block. -/
theorem reachesW_of_weakRule {q : ℕ} [P.Quorate q] {T : Finset Validator}
    (hqT : Fintype.card Validator < q + T.card) {wk : BlockId → Finset BlockId}
    {holds : Validator → ℕ → Finset BlockId} {built : Validator → ℕ → ℕ}
    (hwr : WeakRule U wk T holds built) (hmono : ∀ v, ∀ s t, s ≤ t → holds v s ⊆ holds v t)
    (hbuilt : ∀ v ∈ T, ∀ c ∈ U.ids, (U.block c).creator = v →
      (U.block c).round ≤ built v (U.block c).round)
    {m : BlockId} {t : ℕ} (hmr : (U.block m).round ≤ t) (hheld : ∀ v ∈ T, m ∈ holds v t) :
    ∀ c ∈ U.ids, t + 2 ≤ (U.block c).round → ReachesW U wk c m := by
  intro c hc hcr
  have hquo := Validity.Quorate.quorum U.block (U.block c) (U.valid c hc) (by omega)
  obtain ⟨i, hi, hiT⟩ : ∃ i ∈ (U.block c).refs, (U.block i).creator ∈ T := by
    by_contra hno
    push Not at hno
    have hsub : creators U.block (U.block c) ⊆ Tᶜ := by
      intro v hv
      obtain ⟨i, hi, rfl⟩ := mem_creatorsOf.mp hv
      exact Finset.mem_compl.mpr (hno i hi)
    have := Finset.card_le_card hsub
    rw [Finset.card_compl] at this
    have := Finset.card_le_univ T
    omega
  have hiU := U.complete c hc i hi
  have hir := Validity.Mechanised.pred U.block (U.block c) (U.valid c hc) i hi
  have hb := hbuilt _ hiT i hiU rfl
  have hmi : m ∈ holds (U.block i).creator (built (U.block i).creator (U.block i).round) :=
    hmono _ t _ (by omega) (hheld _ hiT)
  exact Relation.ReflTransGen.head (Or.inl hi) (hwr _ hiT i hiU rfl m hmi (by omega))

variable {q : ℕ} [P.Quorate q] {p : Params} (σ : VoteSel Validator BlockId Payload P honest)

/-- **A leader block every reliable decision-round block certifies commits**
on a view holding the reliable blocks, when they meet the commit
threshold. -/
theorem decided_of_certified [S : Slots Validator] {T : Finset Validator} {k : ℕ} {L : BlockId}
    (hcm : p.commitThreshold ≤ T.card)
    (hpop : PopulatedOn U T (S.slotRound k + (p.waveLength - 1))) (hL : IsLeaderBlock U k L)
    (hcert : ∀ C ∈ U.ids, (U.block C).creator ∈ T →
      (U.block C).round = S.slotRound k + (p.waveLength - 1) → IsCert p σ U C L)
    {V : U.View} (hV : ∀ b ∈ U.ids, (U.block b).creator ∈ T → b ∈ V.ids) :
    (schemeAnchored p σ).Decided U V k (some L) :=
  AnchoredRule.Decided.directCommit hL
    (commit_of_certified hcm hpop fun C hC hCT hCr => ⟨hcert C hC hCT hCr, hV C hC hCT⟩)

/-- **A decided prefix up to a commit reaching an honest block delivers
it**, once the scan reaches far enough, at the rows the inequalities
cover. -/
theorem mem_deliverSeq_of_decided [S : Slots Validator] {f : ℕ} (ht : p.Tolerates honest f q)
    {V : U.View} {k : ℕ} {L b : BlockId}
    (hall : ∀ m ≤ k, ∃ v, (schemeAnchored p σ).Decided U V m v)
    (hk : (schemeAnchored p σ).Decided U V k (some L)) (hb : b ∈ U.ids)
    {wk : BlockId → Finset BlockId} (hr : ReachesW U wk L b)
    (hh : (U.block b).creator ∈ honest) :
    ∃ N₀, ∀ N, N₀ ≤ N → b ∈ deliverSeq p σ U wk V N := by
  obtain ⟨N₀, hN₀⟩ := Loop.outputComplete Validator BlockId Payload P q honest f p σ U V 0 k ht
    (Nat.zero_le _) fun m _ hm => hall m hm
  exact ⟨N₀, fun N hN => mem_deliverOf_of (hN₀ N hN (some L) hk) rfl hb hr hh⟩

/-- **A block of safe coins commits its first slot and decides every slot
below it**, on every reliable validator's own view from some time on. -/
theorem eventually_committed_of_good_block {T : Finset Validator} {N qp : ℕ}
    (ap : AsyncPace qp U T N) (S₀ : Slots Validator) (hS : StrictMono S₀.slotRound)
    {s₀ d M : ℕ} (dflt : Validator) (g : Fin M → Fin d → Validator) (hc : p.CertFits q)
    (hcm : p.commitThreshold ≤ T.card) (hq : qp ≤ T.card) (hd : 0 < d)
    (hspan : (schemeAnchored p σ).SpansEligible (S := S₀) d)
    (hN : S₀.slotRound (s₀ + M * d) + (p.waveLength - 1) ≤ N) (j : Fin M)
    (hgood : ∀ i : Fin d, g j i ∈ safeAt p U (S₀.slotRound (s₀ + j * d + i))) :
    ∃ L, IsLeaderBlock (S := coinSlots S₀ hS (Steelhead.coinOfBlocksFrom s₀ g dflt)) U
        (s₀ + j * d) L ∧
      ap.Eventually fun V =>
        (schemeAnchored p σ).Decided (S := coinSlots S₀ hS (Steelhead.coinOfBlocksFrom s₀ g dflt))
          U V (s₀ + j * d) (some L) ∧
        ∀ s ≤ s₀ + j * d, ∃ v,
          (schemeAnchored p σ).Decided (S := coinSlots S₀ hS (Steelhead.coinOfBlocksFrom s₀ g dflt))
            U V s v := by
  letI S' := coinSlots S₀ hS (Steelhead.coinOfBlocksFrom s₀ g dflt)
  have hjM := j.isLt
  have hled : ∀ i, i < d → S'.leader (s₀ + j * d + i) ∈ safe p U (s₀ + j * d + i) := by
    intro i hi
    change Steelhead.coinOfBlocksFrom s₀ g dflt (s₀ + j * d + i) ∈
      safeAt p U (S₀.slotRound (s₀ + j * d + i))
    have := Steelhead.coinOfBlocksFrom_read (b := s₀) hd g dflt j ⟨i, hi⟩
    rw [this]; exact hgood ⟨i, hi⟩
  have hrange : ∀ j', j' ≤ s₀ + j * d + d - 1 →
      S₀.slotRound j' + (p.waveLength - 1) ≤ N := by
    intro j' hj'
    have : (j : ℕ) * d + d ≤ M * d := by
      have := Nat.mul_le_mul_right d (show (j : ℕ) + 1 ≤ M by omega)
      rw [Nat.add_mul, one_mul] at this; exact this
    have hmono := S₀.mono (show j' ≤ s₀ + M * d by omega)
    omega
  obtain ⟨t, ht⟩ := ap.delivered
  have hfirst := hled 0 hd
  rw [Nat.add_zero] at hfirst
  obtain ⟨hLh, L, hL, hLr, hLc, hsafe⟩ := mem_safeAt.mp hfirst
  refine ⟨L, ⟨hL, hLr, hLc⟩, t, fun t' htt' v hv => ⟨?_, fun s hs => ?_⟩⟩
  · obtain ⟨L', hL', hdec⟩ := decided_of_safe_of_holds (S := S') σ hc.1 hc.2 hcm
      (ap.populated hq _ (hrange _ (by omega))) hfirst
      (V := ap.viewAt hv t') fun b hb hbT => ht t' htt' v hv b hb hbT
    rwa [U.eq_of_creator_eq hL'.1 hL hLh hL'.2.2 hLc (hL'.2.1.trans hLr.symm)] at hdec
  · have hcommit : ∀ j', s₀ + j * d ≤ j' → j' ≤ s₀ + j * d + d - 1 →
        S'.leader j' ∈ safe p U j' →
          ∃ L, (schemeAnchored p σ).Decided U (ap.viewAt hv t') j' (some L) :=
      fun j' _ h2 hj' => by
        obtain ⟨L, -, hL⟩ := decided_of_safe_of_holds (S := S') σ hc.1 hc.2 hcm
          (ap.populated hq _ (hrange _ h2)) hj'
          (V := ap.viewAt hv t') fun b hb hbT => ht t' htt' v hv b hb hbT
        exact ⟨L, hL⟩
    rcases Nat.lt_or_ge s (s₀ + j * d) with hlt | hge
    · exact AnchoredRule.decided_below_of_run (S := S')
        (fun _ h => AnchoredRule.exists_least_of_lt (fun _ _ => Iff.rfl) h) hd hspan
        (b := s₀ + j * d) (Led := fun s => S'.leader s ∈ safe p U s) hled hcommit s hlt
    · have : s = s₀ + j * d := le_antisymm hs hge
      subst this
      obtain ⟨L, hL⟩ := hcommit _ le_rfl (by omega) hfirst
      exact ⟨_, hL⟩

end Scheme

end LeanDag
