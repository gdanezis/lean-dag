import LeanDag.KPartialDag.Model.Live
import LeanDag.KPartialDag.Helpers.Node
/-!
# Liveness — helpers

`docs/kpartial.md` §6. After synchrony, a block of `T` two rounds above a
block of `T` carries votes for it from all of `T` (`carriesVotes_of_synchronisedOn`), so
a node holding the blocks of `T` at that round with their references commits
a leader in `T` directly (`nodeDecided_of_leader_mem`). A committed block has a
certificate (`NodeDecided.certified`), so a node holding the available
sub-DAG below every certified leader block has fetched the sub-DAG below
each anchor it uses, and its indirect test returns a verdict either way.
Below a committed run, the nearest committed anchor of each slot gives the
slot a verdict, by induction downward (`nodeDecided_below`). A run led by `T`
commits, so every slot up to its end is decided (`nodeDecided_of_run`). The
blocks a node needs are held by correct nodes (`delivered`).
-/

namespace LeanDag

namespace KPartialDag

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator] [F : Faults Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {U : KRecord Validator BlockId Payload} {K : ℕ} {H : Finset BlockId}
variable {T : Finset Validator} {R : ℕ}

/-- **After synchrony, a block of `T` carries votes from all of `T`** for a
block of `T` two rounds below, once the round between is populated. -/
theorem carriesVotes_of_synchronisedOn (hcard : quorumCard Validator ≤ T.card)
    (hs : SynchronisedOn U T R) {r : ℕ} (hRr : R ≤ r) (hpop : PopulatedOn U T (r + 1))
    {L C : BlockId} (hL : L ∈ U.ids) (hLr : (U.block L).round = r)
    (hLc : (U.block L).creator ∈ T) (hC : C ∈ U.ids) (hCr : (U.block C).round = r + 2)
    (hCc : (U.block C).creator ∈ T) :
    CarriesVotes U (IsVote U) (quorumCard Validator) C L := by
  refine le_trans hcard (Finset.card_le_card ?_)
  intro v hv
  obtain ⟨b, hb, hbc, hbr⟩ := hpop v hv
  have hbT : (U.block b).creator ∈ T := by rw [hbc]; exact hv
  exact mem_creatorsOf.mpr ⟨b, mem_carriedVotes.mpr
    ⟨hs (r + 1) (by omega) C hC (by omega) hCc b hb hbr hbT, hs r hRr b hb hbr hbT L hL hLr hLc⟩,
    hbc⟩

omit [DecidableEq BlockId] in
/-- `WithRefs` grows with its rounds. -/
theorem withRefs_mono {lo hi lo' hi' : ℕ} (hlo : lo' ≤ lo) (hhi : hi ≤ hi') :
    WithRefs U T lo hi ⊆ WithRefs U T lo' hi' := by
  rintro z ⟨c, hc, hcT, h1, h2, hz⟩
  exact ⟨c, hc, hcT, by omega, by omega, hz⟩

/-- The available sub-DAG below a block of the record lies in the record. -/
theorem avail_subset_ids {A z : BlockId} (hA : A ∈ U.ids) (hz : z ∈ Avail U K A) :
    z ∈ U.ids := by
  obtain ⟨y, hy, hzy⟩ := hz
  exact historyUpto_subset_ids K (hy.mem hA) hzy

variable [S : Slots Validator]

/-- **A leader in `T` commits**: after synchrony, a node holding the blocks of
`T` two rounds above the slot, with their references, commits it
directly. -/
theorem nodeDecided_of_leader_mem (hcard : quorumCard Validator ≤ T.card)
    (hs : SynchronisedOn U T R) {k : ℕ} (hR : R ≤ S.slotRound k) (hlead : S.leader k ∈ T)
    (hpop : ∀ r, S.slotRound k ≤ r → r ≤ S.slotRound k + 2 → PopulatedOn U T r)
    (hH : WithRefs U T (S.slotRound k + 2) (S.slotRound k + 2) ⊆ ↑H) :
    ∃ L, IsLeaderBlock U k L ∧ NodeDecided U K H k (some L) := by
  obtain ⟨L, hL, hLc, hLr⟩ := hpop _ le_rfl (by omega) (S.leader k) hlead
  have hLT : (U.block L).creator ∈ T := by rw [hLc]; exact hlead
  refine ⟨L, ⟨hL, hLr, hLc⟩, NodeDecided.directCommit ⟨hL, hLr, hLc⟩ ?_⟩
  refine le_trans hcard (Finset.card_le_card ?_)
  intro v hv
  obtain ⟨C, hC, hCc, hCr⟩ := hpop _ (by omega) le_rfl v hv
  have hCT : (U.block C).creator ∈ T := by rw [hCc]; exact hv
  have hcert : C ∈ certificatesAt U (IsVote U) (quorumCard Validator) L (S.slotRound k + 2) :=
    mem_certificatesAt.mpr ⟨hC, hCr, carriesVotes_of_synchronisedOn hcard hs hR
      (hpop _ (by omega) (by omega)) hL hLr hLT hC hCr hCT⟩
  refine mem_creatorsOf.mpr ⟨C, Finset.mem_filter.mpr ⟨hcert, ?_, fun j hj => ?_⟩, hCc⟩
  · exact hH ⟨C, hC, hCT, le_of_eq hCr.symm, le_of_eq hCr, Or.inl rfl⟩
  · exact hH ⟨C, hC, hCT, le_of_eq hCr.symm, le_of_eq hCr, Or.inr hj⟩

/-- **A committed block has a certificate**, for a node holding blocks of the
record. -/
theorem NodeDecided.certified (hH : H ⊆ U.ids) {j : ℕ} {A : BlockId}
    (h : NodeDecided U K H j (some A)) : IsLeaderBlock U j A ∧
      (certificatesAt U (IsVote U) (quorumCard Validator) A (S.slotRound j + 2)).Nonempty := by
  cases h with
  | directCommit hL hc =>
    exact ⟨hL, exists_certificate (U := U)
      (hc.trans (Finset.card_le_card (Finset.image_subset_image (Finset.filter_subset _ _))))⟩
  | indirectCommit _ _ _ _ hL hlink =>
    obtain ⟨C, hC, -, -⟩ := linkedIn_avail hH hlink
    exact ⟨hL, C, hC⟩

/-- **Below a committed run, every slot is decided**: a node holding the
available sub-DAG below every certified leader block up to slot `n`, which
has committed every slot from `b` to `n`, decides every slot below `b` that
`n` may anchor. -/
theorem nodeDecided_below (hH : H ⊆ U.ids) {b n : ℕ} (hbn : b ≤ n)
    (hspan : ∀ i, i < b → EligibleAt (S := S) 2 i n) (hav : AvailBelow U K n ⊆ ↑H)
    (hrun : ∀ j, b ≤ j → j ≤ n → ∃ A, NodeDecided U K H j (some A)) :
    ∀ i, i < b → ∃ v, NodeDecided U K H i v := by
  classical
  have key : ∀ d i, i < b → b - i ≤ d → ∃ v, NodeDecided U K H i v := by
    intro d
    induction d with
    | zero => intro i hi hd; omega
    | succ d ih =>
      intro i hi hd
      -- the nearest eligible committed slot above `i`
      have hex : ∃ j, EligibleAt (S := S) 2 i j ∧ j ≤ n ∧ ∃ A, NodeDecided U K H j (some A) :=
        ⟨n, hspan i hi, le_rfl, hrun n hbn le_rfl⟩
      obtain ⟨helig, hjn, A, hA⟩ := Nat.find_spec hex
      have hij : i < Nat.find hex := lt_of_eligibleAt helig
      have hmid : ∀ m, i < m → m < Nat.find hex → EligibleAt (S := S) 2 i m →
          NodeDecided U K H m none := by
        intro m him hmj hem
        have hnot : ¬ ∃ A', NodeDecided U K H m (some A') :=
          fun hc => Nat.find_min hex hmj ⟨hem, by omega, hc⟩
        by_cases hmb : b ≤ m
        · exact absurd (hrun m hmb (by omega)) hnot
        · obtain ⟨v, hv⟩ := ih m (by omega) (by omega)
          cases v with
          | none => exact hv
          | some A' => exact absurd ⟨A', hv⟩ hnot
      obtain ⟨hAL, hAc⟩ := hA.certified hH
      have hf : FetchedIn U K H A :=
        fetchedIn_of_subset fun z hz => hav ⟨Nat.find hex, A, hjn, hAL, hAc, hz⟩
      by_cases hc : ∃ L, IsLeaderBlock U i L ∧ LinkedIn U K H A L (S.slotRound i)
      · obtain ⟨L, hL, hlink⟩ := hc
        exact ⟨some L, NodeDecided.indirectCommit hij helig hA hmid hL hlink⟩
      · exact ⟨none, NodeDecided.indirectSkip hij helig hA hmid hf
          fun L hL hl => hc ⟨L, hL, hl⟩⟩
  exact fun i hi => key (b - i) i hi le_rfl

/-- **A run led by `T` decides every slot up to its end**, after synchrony,
for a node holding the blocks of `T` over the run with their references and
the available sub-DAG below every certified leader block up to the run's
end. -/
theorem nodeDecided_of_run (hcard : quorumCard Validator ≤ T.card)
    (hs : SynchronisedOn U T R) (hH : H ⊆ U.ids) {b c : ℕ} (hc : 0 < c)
    (hspan : ∀ b i, i < b → EligibleAt (S := S) 2 i (b + c - 1))
    (hR : R ≤ S.slotRound b) (hrun : ∀ i, i < c → S.leader (b + i) ∈ T)
    (hpop : ∀ r, S.slotRound b ≤ r → r ≤ S.slotRound (b + c - 1) + 2 → PopulatedOn U T r)
    (hheld : WithRefs U T (S.slotRound b) (S.slotRound (b + c - 1) + 2) ∪
      AvailBelow U K (b + c - 1) ⊆ ↑H) :
    ∀ i, i < b + c → ∃ v, NodeDecided U K H i v := by
  have hcommit : ∀ j, b ≤ j → j ≤ b + c - 1 → ∃ A, NodeDecided U K H j (some A) := by
    intro j h1 h2
    have hb : S.slotRound b ≤ S.slotRound j := S.mono h1
    have hj : S.slotRound j ≤ S.slotRound (b + c - 1) := S.mono h2
    have hlead : S.leader j ∈ T := by
      have := hrun (j - b) (by omega)
      rwa [Nat.add_sub_cancel' h1] at this
    obtain ⟨L, -, hL⟩ := nodeDecided_of_leader_mem (K := K) hcard hs (le_trans hR hb) hlead
      (fun r h1 h2 => hpop r (by omega) (by omega))
      (fun z hz => hheld (Set.mem_union_left _ (withRefs_mono (by omega) (by omega) hz)))
    exact ⟨L, hL⟩
  intro i hi
  by_cases hib : i < b
  · exact nodeDecided_below hH (by omega) (fun i hi => hspan b i hi)
      (fun z hz => hheld (Set.mem_union_right _ hz)) hcommit i hib
  · obtain ⟨A, hA⟩ := hcommit i (by omega) (by omega)
    exact ⟨some A, hA⟩

/-- **What a node needs, a correct node holds**: the blocks of `T` are their
correct authors', their references lie in those authors' windows, and the
available sub-DAG below a certified block lies in the window of a block
that a correct voter or a correct author's block of the sub-DAG
references. -/
theorem delivered (hT : T ⊆ Correct) {lo hi n : ℕ} :
    WithRefs U T lo hi ∪ AvailBelow U K n ⊆ CorrectHeld U K := by
  rintro z (⟨c, hc, hcT, -, -, hz | hz⟩ | ⟨j, A, -, hA, ⟨C, hC⟩, hz⟩)
  · exact ⟨c, hc, hT hcT, Or.inl hz⟩
  · exact ⟨c, hc, hT hcT, Or.inr ⟨z, hz, mem_historyUpto_self⟩⟩
  · obtain ⟨y, -, hzy, hyA | ⟨w, hw, hwc, hyw⟩⟩ := held hz
    · obtain ⟨hCi, -, hv⟩ := mem_certificatesAt.mp hC
      obtain ⟨u, hu, hucorr⟩ := exists_correct_of_card
        (S := creatorsOf U.block (carriedVotes U (IsVote U) C A))
        (by have := F.card_validators; unfold CarriesVotes at hv; omega)
      obtain ⟨b, hb, hbc⟩ := mem_creatorsOf.mp hu
      obtain ⟨hbC, hbA⟩ := mem_carriedVotes.mp hb
      refine ⟨b, U.complete C hCi b hbC, by rw [hbc]; exact hucorr, Or.inr ⟨y, ?_, hzy⟩⟩
      rw [hyA]
      exact hbA
    · exact ⟨w, avail_subset_ids hA.1 hw, hwc, Or.inr ⟨y, hyw, hzy⟩⟩

end KPartialDag

end LeanDag
