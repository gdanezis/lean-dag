import LeanDag.KPartialDag.Model.Live
import LeanDag.KPartialDag.Helpers.Node
/-!
# Liveness — helpers

`docs/kpartial.md` §6. Synchrony implies responsiveness, a responsive slot
commits, and a committed run decides every slot below it
(`nodeDecided_of_run`).
-/

namespace LeanDag

namespace KPartialDag

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator] [F : Faults Validator]
variable [Cr : Crashes Validator]
variable {BlockId : Type*} [LinearOrder BlockId] {Payload : Type*}
variable {U : KRecord Validator BlockId Payload} {K : ℕ} {H : Finset BlockId}
variable {T : Finset Validator} {R : ℕ}

/-- **After synchrony, a block of `T` carries votes from all of `T`** for a
block of `T` two rounds below, once the round between is populated. -/
theorem carriesVotes_of_synchronisedOn (hcard : quorumCard Validator ≤ T.card) {N : ℕ}
    (hs : SynchronisedTo U T R N) {r : ℕ} (hRr : R ≤ r) (hrN : r + 2 ≤ N)
    (hpop : PopulatedOn U T (r + 1))
    {L C : BlockId} (hL : L ∈ U.ids) (hLr : (U.block L).round = r)
    (hLc : (U.block L).creator ∈ T) (hC : C ∈ U.ids) (hCr : (U.block C).round = r + 2)
    (hCc : (U.block C).creator ∈ T) :
    CarriesVotes U (IsVote U) (quorumCard Validator) C L := by
  refine le_trans hcard (Finset.card_le_card ?_)
  intro v hv
  obtain ⟨b, hb, hbc, hbr⟩ := hpop v hv
  have hbT : (U.block b).creator ∈ T := by rw [hbc]; exact hv
  exact mem_creatorsOf.mpr ⟨b, mem_carriedVotes.mpr
    ⟨hs (r + 1) (by omega) (by omega) C hC (by omega) hCc b hb hbr hbT,
      hs r hRr (by omega) b hb hbr hbT L hL hLr hLc⟩,
    hbc⟩

omit [LinearOrder BlockId] in
/-- `WithRefs` grows with its rounds. -/
theorem withRefs_mono {lo hi lo' hi' : ℕ} (hlo : lo' ≤ lo) (hhi : hi ≤ hi') :
    WithRefs U T lo hi ⊆ WithRefs U T lo' hi' := by
  rintro z ⟨c, hc, hcT, h1, h2, hz⟩
  exact ⟨c, hc, hcT, by omega, by omega, hz⟩

variable [S : Slots Validator]

/-- **After synchrony, a slot led by `T` responds among `T`**: the blocks of
`T` one round above it reference its leader's block, and those two rounds
above carry votes from all of `T`. -/
theorem responds_of_synchronisedOn (hcard : quorumCard Validator ≤ T.card) {N : ℕ}
    (hs : SynchronisedTo U T R N) {k : ℕ} (hR : R ≤ S.slotRound k)
    (hN : S.slotRound k + 2 ≤ N) (hlead : S.leader k ∈ T)
    (hpop : ∀ r, S.slotRound k ≤ r → r ≤ S.slotRound k + 2 → PopulatedOn U T r) :
    Responds U T k := by
  obtain ⟨L, hL, hLc, hLr⟩ := hpop _ le_rfl (by omega) (S.leader k) hlead
  have hLT : (U.block L).creator ∈ T := by rw [hLc]; exact hlead
  exact ⟨hpop _ (by omega) le_rfl, L, ⟨hL, hLr, hLc⟩, fun C hC hCT hCr =>
    carriesVotes_of_synchronisedOn hcard hs hR hN (hpop _ (by omega) (by omega)) hL hLr hLT hC
      hCr hCT, hpop _ (by omega) (by omega), fun b hb hbT hbr =>
    hs (S.slotRound k) hR (by omega) b hb hbr hbT L hL hLr hLT⟩

/-- **Synchrony implies responsiveness.** -/
theorem respondsFrom_of_syncFrom {N : ℕ} (h : SyncFrom U T R N) : RespondsFrom U T R N :=
  ⟨h.1, fun _ hR hN hlead => responds_of_synchronisedOn h.1 h.2.1 hR hN hlead
    fun r h1 h2 => h.2.2 r (le_trans hR h1) (by omega)⟩

/-- **A responsive slot commits** at a live row: a node holding the blocks of
`T` one and two rounds above the slot, with their references, commits it
directly, on the votes of `T` when votes are certificates and on the
certificates of `T` otherwise. -/
theorem nodeDecided_of_responds {p : Scheme.Params} (hrow : Row Validator p)
    (hlive : LiveRow Validator p) (hcard : quorumCard Validator ≤ T.card) {k : ℕ}
    (hresp : Responds U T k)
    (hH : WithRefs U T (S.slotRound k + 1) (S.slotRound k + 2) ⊆ ↑H) :
    ∃ L, IsLeaderBlock U k L ∧ NodeDecided p U K H k (some L) := by
  obtain ⟨hpop, L, hL, hvotes, hpop₁, hvote⟩ := hresp
  obtain ⟨hw2, hw3⟩ := row_wave hrow
  refine ⟨L, hL, NodeDecided.directCommit hL ?_⟩
  refine hlive.1.trans (le_trans hcard (Finset.card_le_card ?_))
  intro v hv
  have hheld : ∀ C ∈ U.ids, (U.block C).creator ∈ T → S.slotRound k + 1 ≤ (U.block C).round →
      (U.block C).round ≤ S.slotRound k + 2 → C ∈ H ∧ ∀ j ∈ (U.block C).refs, j ∈ H :=
    fun C hC hCT h1 h2 => ⟨hH ⟨C, hC, hCT, h1, h2, Or.inl rfl⟩,
      fun j hj => hH ⟨C, hC, hCT, h1, h2, Or.inr hj⟩⟩
  cases hv' : p.voteIsCert
  · obtain ⟨C, hC, hCc, hCr⟩ := hpop v hv
    have hCT : (U.block C).creator ∈ T := by rw [hCc]; exact hv
    have hcert : C ∈ certsFor p U L (S.slotRound k) := by
      unfold certsFor
      rw [if_neg (by simp [hv']), hw3 hv']
      exact mem_certificatesAt.mpr ⟨hC, hCr, hlive.2.trans (hvotes C hC hCT hCr)⟩
    obtain ⟨h1, h2⟩ := hheld C hC hCT (by omega) (by omega)
    exact mem_creatorsOf.mpr ⟨C, Finset.mem_filter.mpr ⟨hcert, h1, h2⟩, hCc⟩
  · obtain ⟨b, hb, hbc, hbr⟩ := hpop₁ v hv
    have hbT : (U.block b).creator ∈ T := by rw [hbc]; exact hv
    have hcert : b ∈ certsFor p U L (S.slotRound k) := by
      unfold certsFor
      rw [if_pos hv', hw2 hv']
      exact mem_votesFor.mpr ⟨hb, hbr, hvote b hb hbT hbr⟩
    obtain ⟨h1, h2⟩ := hheld b hb hbT (by omega) (by omega)
    exact mem_creatorsOf.mpr ⟨b, Finset.mem_filter.mpr ⟨hcert, h1, h2⟩, hbc⟩

/-- **A committed block is voted for** at a row, for a node holding blocks of
the record. -/
theorem NodeDecided.voted {p : Scheme.Params} (hrow : Row Validator p) (hH : H ⊆ U.ids) {j : ℕ}
    {A : BlockId} (h : NodeDecided p U K H j (some A)) : IsLeaderBlock U j A ∧ Voted U A := by
  cases h with
  | directCommit hL hc =>
    refine ⟨hL, voted_of_certs hrow (X := heldWithRefs U H (certsFor p U A (S.slotRound j)))
      (by rw [hL.2.1]; exact Finset.filter_subset _ _) ?_⟩
    exact (row_arith hrow hc le_rfl).1
  | indirectCommit _ _ _ _ _ hL hlink _ =>
    obtain ⟨X, hX, -, hXn⟩ := linkedIn_avail hH hlink
    exact ⟨hL, voted_of_certs hrow (by rw [hL.2.1]; exact hX) hXn⟩

/-- **Below a committed run, every slot is decided**: a node holding the
available sub-DAG below every voted leader block up to slot `n`, which has
committed every slot from `b` to `n`, decides every slot below `b` that `n`
may anchor, committing the least linked candidate. -/
theorem nodeDecided_below {p : Scheme.Params} (hrow : Row Validator p) (hH : H ⊆ U.ids)
    {b n : ℕ} (hbn : b ≤ n) (hspan : ∀ i, i < b → EligibleAt (S := S) (p.waveLength - 1) i n)
    (hav : AvailBelow U K n ⊆ ↑H)
    (hrun : ∀ j, b ≤ j → j ≤ n → ∃ A, NodeDecided p U K H j (some A)) :
    ∀ i, i < b → ∃ v, NodeDecided p U K H i v := by
  classical
  have key : ∀ d i, i < b → b - i ≤ d → ∃ v, NodeDecided p U K H i v := by
    intro d
    induction d with
    | zero => intro i hi hd; omega
    | succ d ih =>
      intro i hi hd
      -- the nearest eligible committed slot above `i`
      have hex : ∃ j, EligibleAt (S := S) (p.waveLength - 1) i j ∧ j ≤ n ∧
          ∃ A, NodeDecided p U K H j (some A) :=
        ⟨n, hspan i hi, le_rfl, hrun n hbn le_rfl⟩
      obtain ⟨helig, hjn, A, hA⟩ := Nat.find_spec hex
      have hij : i < Nat.find hex := lt_of_eligibleAt helig
      have hmid : ∀ m, i < m → m < Nat.find hex → EligibleAt (S := S) (p.waveLength - 1) i m →
          NodeDecided p U K H m none := by
        intro m him hmj hem
        have hnot : ¬ ∃ A', NodeDecided p U K H m (some A') :=
          fun hc => Nat.find_min hex hmj ⟨hem, by omega, hc⟩
        by_cases hmb : b ≤ m
        · exact absurd (hrun m hmb (by omega)) hnot
        · obtain ⟨v, hv⟩ := ih m (by omega) (by omega)
          cases v with
          | none => exact hv
          | some A' => exact absurd ⟨A', hv⟩ hnot
      obtain ⟨hAL, hAv⟩ := hA.voted hrow hH
      have hf : FetchedIn U K H A (S.slotRound i + 1) :=
        fetchedIn_of_subset hAL.1 (by rw [hAL.2.1]; have := eligibleAt_iff.mp helig; omega)
          fun z hz _ => hav ⟨Nat.find hex, A, hjn, hAL, hAv, hz⟩
      -- the least linked candidate
      set cands := U.ids.filter fun L => IsLeaderBlock U i L ∧ LinkedIn p U K H A L (S.slotRound i)
      by_cases hc : cands.Nonempty
      · obtain ⟨hLi, hL, hlink⟩ := Finset.mem_filter.mp (cands.min'_mem hc)
        refine ⟨some (cands.min' hc), NodeDecided.indirectCommit hij helig hA hmid hf hL hlink
          fun L' hL' hlt hl' => ?_⟩
        exact absurd (cands.min'_le L' (Finset.mem_filter.mpr ⟨hL'.1, hL', hl'⟩)) (not_le.mpr hlt)
      · exact ⟨none, NodeDecided.indirectSkip hij helig hA hmid hf
          fun L hL hl => hc ⟨L, Finset.mem_filter.mpr ⟨hL.1, hL, hl⟩⟩⟩
  exact fun i hi => key (b - i) i hi le_rfl

/-- **A responsive run decides every slot up to its end** at a live row: a
node holding the blocks of `T` over the run with their references and the
available sub-DAG below every voted leader block up to the run's end
decides every slot up to the run's end. -/
theorem nodeDecided_of_run {p : Scheme.Params} (hrow : Row Validator p)
    (hlive : LiveRow Validator p) (hcard : quorumCard Validator ≤ T.card) (hH : H ⊆ U.ids)
    {b c : ℕ} (hc : 0 < c)
    (hspan : ∀ b i, i < b → EligibleAt (S := S) (p.waveLength - 1) i (b + c - 1))
    (hresp : ∀ j, b ≤ j → j ≤ b + c - 1 → Responds U T j)
    (hheld : WithRefs U T (S.slotRound b) (S.slotRound (b + c - 1) + 2) ∪
      AvailBelow U K (b + c - 1) ⊆ ↑H) :
    ∀ i, i < b + c → ∃ v, NodeDecided p U K H i v := by
  have hcommit : ∀ j, b ≤ j → j ≤ b + c - 1 → ∃ A, NodeDecided p U K H j (some A) := by
    intro j h1 h2
    have hb : S.slotRound b ≤ S.slotRound j := S.mono h1
    have hj : S.slotRound j ≤ S.slotRound (b + c - 1) := S.mono h2
    obtain ⟨L, -, hL⟩ := nodeDecided_of_responds (K := K) hrow hlive hcard (hresp j h1 h2)
      (fun z hz => hheld (Set.mem_union_left _ (withRefs_mono (by omega) (by omega) hz)))
    exact ⟨L, hL⟩
  intro i hi
  by_cases hib : i < b
  · exact nodeDecided_below hrow hH (by omega) (fun i hi => hspan b i hi)
      (fun z hz => hheld (Set.mem_union_right _ hz)) hcommit i hib
  · obtain ⟨A, hA⟩ := hcommit i (by omega) (by omega)
    exact ⟨some A, hA⟩

/-- **A run led by `T` after `R` responds**, on a record responsive among `T`
from `R` to the run's end. -/
theorem responds_of_run {b c : ℕ} (hc : 0 < c) (hR : R ≤ S.slotRound b)
    (hrun : ∀ i, i < c → S.leader (b + i) ∈ T)
    (h : RespondsFrom U T R (S.slotRound (b + c - 1) + 2)) :
    ∀ j, b ≤ j → j ≤ b + c - 1 → Responds U T j := by
  intro j h1 h2
  refine h.2 j (le_trans hR (S.mono h1)) (by have := S.mono h2; omega) ?_
  have := hrun (j - b) (by omega)
  rwa [Nat.add_sub_cancel' h1] at this

end KPartialDag

end LeanDag
