import LeanDag.KPartialSparse.Model.Live
import LeanDag.KPartialSparse.Helpers.Node
/-!
# Sparse K-partial DAG — liveness, helpers

`docs/kpartial-sparse.md` §6. Synchrony gives responsiveness
(`respondsFrom_of_syncFrom`) and the votes behind a claim
(`backs_of_syncFrom`); a responsive slot commits (`nodeDecided_of_responds`);
a committed run decides below it (`nodeDecided_below`); and a run of slots
led by `T` decides every slot up to its end (`nodeDecided_of_run`).
-/

namespace LeanDag

namespace KPartialSparse

open KPartialDag Scheme

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator] [F : Faults Validator]
variable [Cr : Crashes Validator] [Ld : Leaders Validator]
variable {BlockId : Type*} [LinearOrder BlockId] {Payload : Type*} [ClaimFormat BlockId Payload]
variable [S : Slots Validator]
variable {U : SRecord Validator BlockId Payload} {T : Finset Validator} {K : ℕ} {H : Finset BlockId}
variable {p : Params}

omit [LinearOrder BlockId] [ClaimFormat BlockId Payload] S in
/-- The certificate round lies one or two rounds above. -/
theorem certRound_bounds (r : ℕ) : r + 1 ≤ certRound p r ∧ certRound p r ≤ r + 2 := by
  unfold certRound; split_ifs <;> omega

omit [LinearOrder BlockId] [ClaimFormat BlockId Payload] S in
/-- The certificate round is monotone. -/
theorem certRound_mono {r r' : ℕ} (h : r ≤ r') : certRound p r ≤ certRound p r' := by
  unfold certRound; split_ifs <;> omega

omit S in
/-- A certificate of the record is a member of the certificates. -/
theorem mem_certsFor_of_certifies {C L : BlockId} {r : ℕ} (hC : C ∈ U.ids)
    (h : Certifies p U C L r) : C ∈ certsFor p U L r := by
  unfold Certifies at h
  unfold certsFor
  split_ifs at h ⊢
  · exact mem_votesFor.mpr ⟨hC, h.1, h.2⟩
  · exact Finset.mem_filter.mpr ⟨mem_blocksAt.mpr ⟨hC, h.1⟩, h.2⟩

omit [LinearOrder BlockId] in
/-- **Synchrony implies responsiveness**: a slot led by `T` has a leader block
of `T`, which every block of `T` one round up references and every block of
`T` two rounds up claims. -/
theorem respondsFrom_of_syncFrom {R N : ℕ} (h : SyncFrom U T R N) : RespondsFrom p U T R N := by
  obtain ⟨hcard, hpop, hvote, hclaim⟩ := h
  refine ⟨hcard, fun k hR hN hk => ?_⟩
  have hb := certRound_bounds (p := p) (S.slotRound k)
  obtain ⟨L, hL, hLc, hLr⟩ := hpop (S.slotRound k) hR (by omega) _ hk
  have hLl : IsLeaderBlock U k L := ⟨hL, hLr, hLc⟩
  refine ⟨hpop _ (by omega) hN, L, hLl, fun C hC hCT hCr => ?_⟩
  unfold Certifies
  unfold certRound at hCr hN
  split_ifs at hCr hN ⊢ with hv
  · exact ⟨hCr, hvote k hR (by omega) hk L hLl C hC hCT hCr⟩
  · exact ⟨hCr, hclaim k hR (by omega) hk L hLl C hC hCT hCr⟩

/-- **Under synchrony a node holding the votes of `T` backs a claim** for a
leader block of a slot led by `T`, at a certificate threshold within the
quorum. -/
theorem backs_of_syncFrom {R N : ℕ} (h : SyncFrom U T R N) {k : ℕ} (hR : R ≤ S.slotRound k)
    (hN : S.slotRound k + 1 ≤ N) (hk : S.leader k ∈ T) {L : BlockId} (hL : IsLeaderBlock U k L)
    {t : ℕ} (ht : t ≤ kQuorum Validator) (hLH : L ∈ H)
    (hH : HeldBy U T (S.slotRound k + 1) (S.slotRound k + 1) ⊆ ↑H) : Backs U t H L := by
  obtain ⟨hcard, hpop, hvote, -⟩ := h
  refine ⟨hLH, ht.trans (hcard.trans (Finset.card_le_card fun v hv => ?_))⟩
  obtain ⟨C, hC, hCc, hCr⟩ := hpop (S.slotRound k + 1) (by omega) hN v hv
  have hCT : (U.block C).creator ∈ T := by rw [hCc]; exact hv
  have hCH : C ∈ H := hH ⟨hC, hCT, by omega, by omega⟩
  exact mem_creatorsOf.mpr ⟨C, Finset.mem_filter.mpr ⟨hCH, by rw [hCr, hL.2.1],
    hvote k hR hN hk L hL C hC hCT hCr⟩, hCc⟩

/-- **A responsive slot commits** at a live row, for a node holding the blocks
of `T` at the round of the slot's certificates. -/
theorem nodeDecided_of_responds (hlive : LiveRow Validator p) (hcard : kQuorum Validator ≤ T.card)
    {k : ℕ} (hresp : Responds p U T k)
    (hH : HeldBy U T (certRound p (S.slotRound k)) (certRound p (S.slotRound k)) ⊆ ↑H) :
    ∃ L, IsLeaderBlock U k L ∧ NodeDecided p U K H k (some L) := by
  obtain ⟨hpop, L, hL, hcert⟩ := hresp
  refine ⟨L, hL, NodeDecided.directCommit hL ?_⟩
  refine hlive.1.trans (le_trans hcard (Finset.card_le_card fun v hv => ?_))
  obtain ⟨C, hC, hCc, hCr⟩ := hpop v hv
  have hCT : (U.block C).creator ∈ T := by rw [hCc]; exact hv
  exact mem_creatorsOf.mpr ⟨C, Finset.mem_filter.mpr ⟨mem_certsFor_of_certifies hC
    (hcert C hC hCT hCr), hH ⟨hC, hCT, by omega, by omega⟩⟩, hCc⟩

omit [ClaimFormat BlockId Payload] in
/-- A committed block is a leader block of its slot. -/
theorem NodeDecided.isLeaderBlock [ClaimFormat BlockId Payload] {j : ℕ} {A : BlockId}
    (h : NodeDecided p U K H j (some A)) : IsLeaderBlock U j A := by
  cases h with
  | directCommit hL _ => exact hL
  | indirectCommit _ _ _ _ _ hL _ _ => exact hL

/-- **A committed run decides below it**: a node holding the available sub-DAG
below every leader block it commits up to slot `n`, which has committed every
slot from `b` to `n`, decides every slot below `b` that `n` may anchor. -/
theorem nodeDecided_below {b n : ℕ} (hbn : b ≤ n)
    (hspan : ∀ i, i < b → EligibleAt (S := S) (p.waveLength - 1) i n)
    (hav : ∀ j A, j ≤ n → NodeDecided p U K H j (some A) → Avail U K A ⊆ ↑H)
    (hrun : ∀ j, b ≤ j → j ≤ n → ∃ A, NodeDecided p U K H j (some A)) :
    ∀ i, i < b → ∃ v, NodeDecided p U K H i v := by
  classical
  have key : ∀ d i, i < b → b - i ≤ d → ∃ v, NodeDecided p U K H i v := by
    intro d
    induction d with
    | zero => intro i hi hd; omega
    | succ d ih =>
      intro i hi hd
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
      have hf : FetchedIn U K H A (certRound p (S.slotRound i)) :=
        fetchedIn_of_subset fun y d hy z hz => hav _ A hjn hA ⟨y, d, hy, hz⟩
      set cands := U.ids.filter fun L => IsLeaderBlock U i L ∧ LinkedIn p U K H A L (S.slotRound i)
      by_cases hc : cands.Nonempty
      · obtain ⟨hLi, hL, hlink⟩ := Finset.mem_filter.mp (cands.min'_mem hc)
        refine ⟨some (cands.min' hc), NodeDecided.indirectCommit hij helig hA hmid hf hL hlink
          fun L' hL' hlt hl' => ?_⟩
        exact absurd (cands.min'_le L' (Finset.mem_filter.mpr ⟨hL'.1, hL', hl'⟩)) (not_le.mpr hlt)
      · exact ⟨none, NodeDecided.indirectSkip hij helig hA hmid hf
          fun L hL hl => hc ⟨L, Finset.mem_filter.mpr ⟨hL.1, hL, hl⟩⟩⟩
  exact fun i hi => key (b - i) i hi le_rfl

omit [LinearOrder BlockId] in
/-- **A run led by `T` after `R` responds**, on a record responsive among `T`
from `R` to the run's end. -/
theorem responds_of_run {R b c : ℕ} (hc : 0 < c) (hR : R ≤ S.slotRound b)
    (hrun : ∀ i, i < c → S.leader (b + i) ∈ T)
    (h : RespondsFrom p U T R (certRound p (S.slotRound (b + c - 1)))) :
    ∀ j, b ≤ j → j ≤ b + c - 1 → Responds p U T j := by
  intro j h1 h2
  refine h.2 j (le_trans hR (S.mono h1)) (certRound_mono (S.mono h2)) ?_
  have := hrun (j - b) (by omega)
  rwa [Nat.add_sub_cancel' h1] at this

/-- **A responsive run decides every slot up to its end** at a live row: a node
holding the blocks of `T` over the run and the available sub-DAG below the
leader blocks it commits decides every slot below the run's end. -/
theorem nodeDecided_of_run (hlive : LiveRow Validator p) (hcard : kQuorum Validator ≤ T.card)
    {b c : ℕ} (hc : 0 < c)
    (hspan : ∀ b i, i < b → EligibleAt (S := S) (p.waveLength - 1) i (b + c - 1))
    (hresp : ∀ j, b ≤ j → j ≤ b + c - 1 → Responds p U T j)
    (hheld : HeldBy U T (S.slotRound b) (certRound p (S.slotRound (b + c - 1))) ⊆ ↑H)
    (hav : ∀ j A, j ≤ b + c - 1 → NodeDecided p U K H j (some A) → Avail U K A ⊆ ↑H) :
    ∀ i, i < b + c → ∃ v, NodeDecided p U K H i v := by
  have hcommit : ∀ j, b ≤ j → j ≤ b + c - 1 → ∃ A, NodeDecided p U K H j (some A) := by
    intro j h1 h2
    have hb : S.slotRound b ≤ S.slotRound j := S.mono h1
    have hj : certRound p (S.slotRound j) ≤ certRound p (S.slotRound (b + c - 1)) :=
      certRound_mono (S.mono h2)
    have hcb := certRound_bounds (p := p) (S.slotRound j)
    obtain ⟨L, -, hL⟩ := nodeDecided_of_responds (K := K) hlive hcard (hresp j h1 h2)
      (fun z hz => hheld ⟨hz.1, hz.2.1, by have := hz.2.2.1; omega, by have := hz.2.2.2; omega⟩)
    exact ⟨L, hL⟩
  intro i hi
  by_cases hib : i < b
  · exact nodeDecided_below (by omega) (fun i hi => hspan b i hi) hav hcommit i hib
  · obtain ⟨A, hA⟩ := hcommit i (by omega) (by omega)
    exact ⟨some A, hA⟩

end KPartialSparse

end LeanDag
