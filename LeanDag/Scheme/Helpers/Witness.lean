import LeanDag.Scheme.Model.Witness
import LeanDag.Scheme.Helpers.TryDecide
/-!
# The witness of a decision decides it

`docs/node-sync.md` D13. The loop's decision of a slot on a view `V` is its
decision on every view `W ⊆ V` that holds the slot's witness
(`decisionAt_of_witness`), so on the histories of the witness
(`witnessView`, `decisionAt_witnessView`).

A smaller view holds no skip or commit the larger lacks
(`tryDirect_none_of_subset`), and one holding the blames or the
certificates the larger holds skips or commits alike. The walk over the
later slots reads their decisions, which the witnesses of the skipped
eligible slots and of the anchor carry, and the candidates linked from the
anchor, which lie in the anchor's history.
-/

namespace LeanDag

namespace Scheme

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [LinearOrder BlockId] {Payload : Type}
variable {P : Validity Validator BlockId Payload} {honest : Finset Validator}
variable {p : Params} {σ : VoteSel Validator BlockId Payload P honest} [S : Slots Validator]
variable {U : BlockRecord Validator BlockId Payload P honest} {V W : U.View}

omit [Fintype Validator] [DecidableEq Validator] [LinearOrder BlockId] in
theorem leastOf_of_subset {β : Type} [LinearOrder β] {s t : Finset β} {x : β} (hst : s ⊆ t)
    (ht : leastOf t = some x) (hx : x ∈ s) : leastOf s = some x := by
  obtain ⟨-, hmin⟩ := leastOf_eq_some ht
  exact leastOf_eq_some_iff.mpr ⟨hx, fun y hy => hmin y (hst hy)⟩

omit [Fintype Validator] [DecidableEq Validator] [LinearOrder BlockId] in
theorem leastOf_none_of_subset {β : Type} [LinearOrder β] {s t : Finset β} (hst : s ⊆ t)
    (ht : leastOf t = none) : leastOf s = none := by
  have hs : s = ∅ := Finset.subset_empty.mp (leastOf_eq_none ht ▸ hst)
  subst hs
  simp [leastOf]

omit [Fintype Validator] in
/-- The candidates a smaller view commits directly, the larger commits. -/
theorem commitFilter_subset (hWV : W.ids ⊆ V.ids) {k : ℕ} :
    (candidatesIn U W k).filter
        (fun L => (schemeAnchored p σ).Commit U W L (S.slotRound k) (S.kind k)) ⊆
      (candidatesIn U V k).filter
        (fun L => (schemeAnchored p σ).Commit U V L (S.slotRound k) (S.kind k)) := by
  intro L hL
  obtain ⟨hc, hcommit⟩ := Finset.mem_filter.mp hL
  obtain ⟨hLW, hrest⟩ := mem_candidatesIn.mp hc
  exact Finset.mem_filter.mpr ⟨mem_candidatesIn.mpr ⟨hWV hLW, hrest⟩,
    HoldsAtLeast.mono hWV hcommit⟩

omit [Fintype Validator] in
/-- **A smaller view decides nothing directly that the larger leaves open.** -/
theorem tryDirect_none_of_subset (hWV : W.ids ⊆ V.ids) {k : ℕ}
    (h : tryDirect p σ U V k = none) : tryDirect p σ U W k = none := by
  unfold tryDirect at h ⊢
  split at h
  · cases h
  · rename_i hskip
    rw [if_neg fun h' => hskip (HoldsAtLeast.mono hWV h'),
      leastOf_none_of_subset (commitFilter_subset hWV) (Option.map_eq_none_iff.mp h)]
    rfl

omit [Fintype Validator] in
/-- A view holding the blames a larger view holds skips as it does. -/
theorem tryDirect_skip_of_witness {k : ℕ} (h : tryDirect p σ U V k = some none)
    (hw : blamersAt p σ U k ∩ V.ids ⊆ W.ids) : tryDirect p σ U W k = some none := by
  unfold tryDirect at h ⊢
  split at h
  · rename_i hskip
    rw [if_pos (HoldsAtLeast.of_inter hw hskip)]
  · simp at h

omit [Fintype Validator] in
/-- A smaller view holding the certificates a larger view holds commits as it
does, at positive commit and certificate thresholds. -/
theorem tryDirect_commit_of_witness (hcm : 1 ≤ p.commitThreshold)
    (hc : p.voteIsCert = false → 1 ≤ p.certThreshold) (hWV : W.ids ⊆ V.ids) {k : ℕ}
    {L : BlockId} (h : tryDirect p σ U V k = some (some L))
    (hw : certsAt p σ U L (S.slotRound k) ∩ V.ids ⊆ W.ids) :
    tryDirect p σ U W k = some (some L) := by
  unfold tryDirect at h ⊢
  split at h
  · cases h
  · rename_i hskip
    rw [if_neg fun h' => hskip (HoldsAtLeast.mono hWV h')]
    obtain ⟨M, hM, hML⟩ := Option.map_eq_some_iff.mp h
    rw [Option.some.injEq] at hML
    subst hML
    obtain ⟨hmem, -⟩ := leastOf_eq_some hM
    obtain ⟨hcV, hcommit⟩ := Finset.mem_filter.mp hmem
    have hcW : (schemeAnchored p σ).Commit U W M (S.slotRound k) (S.kind k) :=
      HoldsAtLeast.of_inter hw hcommit
    have hMW := mem_view_of_commit hcm hc hcW
    rw [leastOf_of_subset (commitFilter_subset hWV) hM (Finset.mem_filter.mpr
      ⟨mem_candidatesIn.mpr ⟨hMW, (mem_candidatesIn.mp hcV).2⟩, hcW⟩)]
    rfl

omit [Fintype Validator] in
/-- **The walk decides alike on a smaller view** holding the witness of the walk,
when each slot it reads is decided alike on that view once the slot's witness
is held, and each commit on it names a block the view holds. -/
theorem tryIndirect_of_witness (hl : 1 ≤ p.linkSize)
    (hc : p.voteIsCert = false → 1 ≤ p.certThreshold) (hWV : W.ids ⊆ V.ids) {k : ℕ}
    {wit : ℕ → Finset BlockId} :
    ∀ (lV lW : List (ℕ × Option (Option BlockId))), lV.map Prod.fst = lW.map Prod.fst →
      (∀ e ∈ lW, ∀ A, e.2 = some (some A) → A ∈ W.ids) →
      (∀ e ∈ lV, ∀ e' ∈ lW, e'.1 = e.1 → ∀ v, e.2 = some v → wit e.1 ⊆ W.ids →
        e'.2 = some v) →
      anchorWitness (S := S) p k wit lV ⊆ W.ids → ∀ v, tryIndirect p σ U V k lV = some v →
        tryIndirect p σ U W k lW = some v := by
  intro lV
  induction lV with
  | nil => intro _ _ _ _ _ v hv; cases hv
  | cons e rest ih =>
    obtain ⟨j, s⟩ := e
    intro lW hfst hA hstep hwit v hv
    cases lW with
    | nil => simp at hfst
    | cons e' restW =>
      obtain ⟨j', s'⟩ := e'
      simp only [List.map_cons, List.cons.injEq] at hfst
      obtain ⟨hjj, hfst⟩ := hfst
      subst hjj
      have hss : ∀ v, s = some v → wit j ⊆ W.ids → s' = some v := fun v h1 h2 =>
        hstep (j, s) List.mem_cons_self (j, s') List.mem_cons_self rfl v h1 h2
      have hA' := fun e he => hA e (List.mem_cons_of_mem (j, s') he)
      have hstep' := fun e he e' he' =>
        hstep e (List.mem_cons_of_mem (j, s) he) e' (List.mem_cons_of_mem (j, s') he')
      unfold tryIndirect at hv ⊢
      unfold anchorWitness at hwit
      split at hv
      · rename_i helig
        rw [if_pos helig] at hwit ⊢
        rcases s with _ | _ | A
        · cases hv
        · rw [hss none rfl (Finset.union_subset_left hwit)]
          exact ih restW hfst hA' hstep' (Finset.union_subset_right hwit) v hv
        · have hs' := hss (some A) rfl hwit
          have hAW := hA (j, s') List.mem_cons_self A hs'
          rw [hs']
          have hset : (candidatesIn U W k).filter (fun L => p.linkSize ≤
                (creatorsOf U.block (linkCerts p σ U A L (S.slotRound k))).card) =
              (candidatesIn U V k).filter (fun L => p.linkSize ≤
                (creatorsOf U.block (linkCerts p σ U A L (S.slotRound k))).card) := by
            ext L
            simp only [Finset.mem_filter, mem_candidatesIn]
            constructor
            · rintro ⟨⟨h1, h2⟩, h3⟩
              exact ⟨⟨hWV h1, h2⟩, h3⟩
            · rintro ⟨⟨-, h2⟩, h3⟩
              exact ⟨⟨mem_view_of_link hl hc hAW h3, h2⟩, h3⟩
          simp only [hset]
          exact hv
      · rename_i hne
        rw [if_neg hne] at hwit ⊢
        exact ih restW hfst hA' hstep' hwit v hv

omit [Fintype Validator] [DecidableEq Validator] in
theorem anchorWitness_subset {k : ℕ} {wit : ℕ → Finset BlockId} {X : Finset BlockId}
    (h : ∀ j, wit j ⊆ X) : ∀ l, anchorWitness (S := S) p k wit l ⊆ X := by
  intro l
  induction l with
  | nil => exact Finset.empty_subset _
  | cons e rest ih =>
    obtain ⟨j, s⟩ := e
    unfold anchorWitness
    split
    · rcases s with _ | _ | A
      · exact Finset.empty_subset _
      · exact Finset.union_subset (h j) ih
      · exact h j
    · exact ih

omit [Fintype Validator] in
/-- **A witness is held by its view.** -/
theorem witnessAt_subset (N : ℕ) : ∀ k, witnessAt p σ U V N k ⊆ V.ids := by
  suffices h : ∀ n k, N + 1 - k = n → witnessAt p σ U V N k ⊆ V.ids from fun k => h _ k rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro k hn
    rw [witnessAt]
    split
    · exact Finset.inter_subset_right
    · exact Finset.inter_subset_right
    · refine anchorWitness_subset (fun j => ?_) _
      split
      · rename_i hj
        exact ih (N + 1 - j) (by omega) j rfl
      · exact Finset.empty_subset _

omit [Fintype Validator] in
/-- **A witness lies at or above its slot's round.** -/
theorem witnessAt_round (N : ℕ) :
    ∀ k, ∀ x ∈ witnessAt p σ U V N k, S.slotRound k ≤ (U.block x).round := by
  suffices h : ∀ n k, N + 1 - k = n →
      witnessAt p σ U V N k ⊆ U.ids.filter fun x => S.slotRound k ≤ (U.block x).round from
    fun k x hx => (Finset.mem_filter.mp (h _ k rfl hx)).2
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro k hn
    rw [witnessAt]
    split
    · intro x hx
      obtain ⟨hx, -⟩ := Finset.mem_inter.mp hx
      obtain ⟨hxU, hxr⟩ := mem_blocksAt.mp (Finset.mem_filter.mp hx).1
      exact Finset.mem_filter.mpr ⟨hxU, by omega⟩
    · intro x hx
      obtain ⟨hx, -⟩ := Finset.mem_inter.mp hx
      obtain ⟨hxU, hxr⟩ := mem_blocksAt.mp (Finset.mem_filter.mp hx).1
      exact Finset.mem_filter.mpr ⟨hxU, by omega⟩
    · refine anchorWitness_subset (fun j => ?_) _
      split
      · rename_i hj
        intro x hx
        have := Finset.mem_filter.mp (ih (N + 1 - j) (by omega) j rfl hx)
        exact Finset.mem_filter.mpr ⟨this.1, (S.mono hj.1.le).trans this.2⟩
      · exact Finset.empty_subset _

omit [Fintype Validator] in
/-- **The witness decides as the view does.** A view `W ⊆ V` holding the
witness of slot `k`'s decision on `V` decides `k` alike, at positive link,
commit and certificate thresholds. -/
theorem decisionAt_of_witness (hl : 1 ≤ p.linkSize) (hcm : 1 ≤ p.commitThreshold)
    (hc : p.voteIsCert = false → 1 ≤ p.certThreshold) (N : ℕ) :
    ∀ k, ∀ W : U.View, W.ids ⊆ V.ids → witnessAt p σ U V N k ⊆ W.ids → ∀ v,
      decisionAt p σ U V N k = some v → decisionAt p σ U W N k = some v := by
  suffices h : ∀ n k, N + 1 - k = n → ∀ W : U.View, W.ids ⊆ V.ids →
      witnessAt p σ U V N k ⊆ W.ids → ∀ v,
        decisionAt p σ U V N k = some v → decisionAt p σ U W N k = some v from
    fun k => h _ k rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro k hn W hWV hwit v hv
    rw [witnessAt] at hwit
    simp only [decisionAt, decideSlot] at hv ⊢
    cases hd : tryDirect p σ U V k with
    | some w =>
      rw [hd] at hv hwit
      obtain rfl : w = v := Option.some.inj hv
      rcases w with _ | L
      · rw [tryDirect_skip_of_witness hd hwit]
      · rw [tryDirect_commit_of_witness hcm hc hWV hd hwit]
    | none =>
      rw [hd] at hv hwit
      rw [tryDirect_none_of_subset hWV hd]
      obtain ⟨hrV, -⟩ := scan_sound (σ := σ) (U := U) (V := V) hl hc N (N - k) (by omega)
      obtain ⟨hrW, hsW⟩ := scan_sound (σ := σ) (U := U) (V := W) hl hc N (N - k) (by omega)
      refine tryIndirect_of_witness hl hc hWV _ _ (hrV.trans hrW.symm)
        (fun e he A hA => (mem_candidatesIn.mp ((hsW e he (some A) hA).2 A rfl)).1)
        (fun e he e' he' hee v' hv' hw' => ?_) hwit v hv
      have hmem : e.1 ∈ List.range' (N + 1 - (N - k)) (N - k) := hrV ▸ List.mem_map_of_mem he
      rw [List.mem_range'_1] at hmem
      have hkj : k < e.1 ∧ e.1 ≤ N := by omega
      have hw'' : witnessAt p σ U V N e.1 ⊆ W.ids := by simpa [hkj] using hw'
      rw [scan_entry (V := W) N (N - k) (by omega) e' he', hee]
      exact ih (N + 1 - e.1) (by omega) e.1 rfl W hWV hw'' v'
        (scan_entry N (N - k) (by omega) e he ▸ hv')

omit [Fintype Validator] in
/-- The scan to slot `N` covers slots up to `N`. -/
theorem scan_le (N : ℕ) : ∀ m, ∀ e ∈ scan p σ U V N m, e.1 ≤ N
  | 0, e, he => by simp [scan] at he
  | m + 1, e, he => by
    rcases List.mem_cons.mp he with rfl | he
    · exact Nat.sub_le N m
    · exact scan_le N m e he

omit [Fintype Validator] in
/-- An output of the loop is its decision for its slot. -/
theorem decisionAt_of_mem_tryDecide {lo N k : ℕ} {v : Option BlockId}
    (h : (k, v) ∈ tryDecide p σ U V lo N) : k ≤ N ∧ decisionAt p σ U V N k = some v := by
  unfold tryDecide at h
  obtain ⟨e, he, hev⟩ := List.mem_map.mp h
  obtain ⟨hmem, hsome⟩ := mem_takeWhile' he
  have hent := scan_entry N (N + 1 - lo) (by omega) e hmem
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp hsome
  simp only [Prod.mk.injEq] at hev
  obtain ⟨rfl, hv⟩ := hev
  refine ⟨scan_le N _ e hmem, ?_⟩
  rw [hw] at hv
  rw [← hent, hw]
  simpa using hv

omit [Fintype Validator] in
/-- A decision of slot `k` is the first output of the loop from `k`. -/
theorem mem_tryDecide_of_decisionAt {N k : ℕ} {v : Option BlockId} (hk : k ≤ N)
    (h : decisionAt p σ U V N k = some v) : (k, v) ∈ tryDecide p σ U V k N := by
  have hscan : scan p σ U V N (N + 1 - k) =
      (k, decisionAt p σ U V N k) :: scan p σ U V N (N - k) := by
    rw [show N + 1 - k = N - k + 1 by omega, scan, decisionAt,
      show N - (N - k) = k by omega]
  unfold tryDecide
  rw [hscan, h, List.takeWhile_cons_of_pos (by simp)]
  exact List.mem_cons_self

omit [Fintype Validator] in
/-- The walk over later slots none of which is decided stops undecided. -/
theorem tryIndirect_of_none {k : ℕ} :
    ∀ l : List (ℕ × Option (Option BlockId)), (∀ e ∈ l, e.2 = none) →
      tryIndirect p σ U V k l = none
  | [], _ => rfl
  | (j, s) :: l, h => by
    have hs : s = none := h (j, s) List.mem_cons_self
    subst hs
    unfold tryIndirect
    split
    · rfl
    · exact tryIndirect_of_none l fun e he => h e (List.mem_cons_of_mem _ he)

omit [Fintype Validator] in
/-- The walk over later slots reads past undecided ones at the end alike. -/
theorem tryIndirect_append {k : ℕ} {Z : List (ℕ × Option (Option BlockId))}
    (hZ : ∀ e ∈ Z, e.2 = none) :
    ∀ l : List (ℕ × Option (Option BlockId)),
      tryIndirect p σ U V k (l ++ Z) = tryIndirect p σ U V k l
  | [] => tryIndirect_of_none Z hZ
  | (j, s) :: l => by
    simp only [List.cons_append]
    unfold tryIndirect
    split
    · split
      · rfl
      · exact tryIndirect_append hZ l
      · rfl
    · exact tryIndirect_append hZ l

omit [Fintype Validator] in
/-- **Past slots that no rule decides directly, the scan decides nothing.** -/
theorem scan_none_above {N' : ℕ} (hq : ∀ j, N' < j → tryDirect p σ U V j = none) (N : ℕ) :
    ∀ m, N' + m ≤ N → ∀ e ∈ scan p σ U V N m, e.2 = none
  | 0, _, e, he => by simp [scan] at he
  | m + 1, hm, e, he => by
    rcases List.mem_cons.mp he with rfl | he
    · simp only [decideSlot]
      rw [hq _ (by omega)]
      exact tryIndirect_of_none _ (scan_none_above hq N m (by omega))
    · exact scan_none_above hq N m (by omega) e he

omit [Fintype Validator] in
/-- **Scanning past slots that no rule decides directly changes no
decision**: the scan to `N` is the scan to `N' ≤ N`, then undecided slots. -/
theorem scan_append {N' N : ℕ} (hq : ∀ j, N' < j → tryDirect p σ U V j = none)
    (hN : N' ≤ N) : ∀ m, m ≤ N' →
      scan p σ U V N (N - N' + m) = scan p σ U V N' m ++ scan p σ U V N (N - N')
  | 0, _ => by simp [scan]
  | m + 1, hm => by
    rw [show N - N' + (m + 1) = (N - N' + m) + 1 by omega, scan, scan_append hq hN m (by omega),
      scan, show N - (N - N' + m) = N' - m by omega]
    congr 2
    unfold decideSlot
    split
    · rfl
    · exact tryIndirect_append (scan_none_above hq N _ (by omega)) _

omit [Fintype Validator] in
/-- **The loop decides a slot alike scanning to `N` or to any `N'` between
the slot and `N`**, when no rule decides directly a slot past `N'`. -/
theorem decisionAt_of_quiet {N' N k : ℕ} (hq : ∀ j, N' < j → tryDirect p σ U V j = none)
    (hN : N' ≤ N) (hk : k ≤ N') : decisionAt p σ U V N k = decisionAt p σ U V N' k := by
  unfold decisionAt
  rw [show N - k = N - N' + (N' - k) by omega, scan_append hq hN _ (by omega)]
  unfold decideSlot
  split
  · rfl
  · exact tryIndirect_append (scan_none_above hq N _ (by omega)) _

omit S in
/-- **More than `f` held authors include one of any set missing at most
`f`.** -/
theorem exists_held_of_holdsAtLeast {A : Finset Validator} {f t : ℕ} (hA : Aᶜ.card ≤ f)
    (ht : f < t) {s : Finset BlockId} (h : HoldsAtLeast U V t s) :
    ∃ x ∈ s, x ∈ V.ids ∧ (U.block x).creator ∈ A := by
  by_contra hno
  push Not at hno
  have hsub : heldAuthors U V s ⊆ Aᶜ := fun a ha => by
    obtain ⟨b, hb, hbV, rfl⟩ := mem_heldAuthors.mp ha
    exact Finset.mem_compl.mpr (hno b hb hbV)
  have := Finset.card_le_card hsub
  unfold HoldsAtLeast at h
  omega

omit [Fintype Validator] in
/-- **A walk that decides stops at an anchor** whose witness its own holds. -/
theorem anchor_of_tryIndirect {k : ℕ} {wit : ℕ → Finset BlockId} :
    ∀ (l : List (ℕ × Option (Option BlockId))) (v : Option BlockId),
      tryIndirect p σ U V k l = some v →
      ∃ e ∈ l, (∃ A, e.2 = some (some A)) ∧
        S.slotRound k + (p.waveLength - 1) + 1 ≤ S.slotRound e.1 ∧
        wit e.1 ⊆ anchorWitness (S := S) p k wit l := by
  intro l
  induction l with
  | nil => intro v hv; cases hv
  | cons e rest ih =>
    obtain ⟨j, s⟩ := e
    intro v hv
    unfold tryIndirect at hv
    unfold anchorWitness
    split at hv
    · rename_i helig
      rw [if_pos helig]
      rcases s with _ | _ | A
      · cases hv
      · obtain ⟨e', he', hA, hr, hw⟩ := ih v hv
        exact ⟨e', List.mem_cons_of_mem _ he', hA, hr, hw.trans Finset.subset_union_right⟩
      · exact ⟨(j, some (some A)), List.mem_cons_self, ⟨A, rfl⟩, helig, subset_rfl⟩
    · rename_i hne
      rw [if_neg hne]
      obtain ⟨e', he', hA, hr, hw⟩ := ih v hv
      exact ⟨e', List.mem_cons_of_mem _ he', hA, hr, hw⟩

/-- **A decided slot's witness holds a block of an author of any set missing
at most `f`, at the slot's round plus `voteOffset` or above**, at skip and
commit thresholds above `f`: a direct skip's blames lie at the vote round, a
direct commit's certificates at the decision round, and an indirect
decision's witness holds its anchor's. -/
theorem witnessAt_author (hl : 1 ≤ p.linkSize) (hc : p.voteIsCert = false → 1 ≤ p.certThreshold)
    (hw : 2 ≤ p.waveLength) {A : Finset Validator} {f : ℕ} (hA : Aᶜ.card ≤ f)
    (hsk : f < p.skipThreshold) (hcm : f < p.commitThreshold) (N : ℕ) :
    ∀ k v, decisionAt p σ U V N k = some v →
      ∃ x ∈ witnessAt p σ U V N k, (U.block x).creator ∈ A ∧
        S.slotRound k + p.voteOffset ≤ (U.block x).round := by
  have hvo : p.voteOffset ≤ p.waveLength - 1 := by
    unfold Params.voteOffset; split <;> omega
  suffices h : ∀ n k, N + 1 - k = n → ∀ v, decisionAt p σ U V N k = some v →
      ∃ x ∈ witnessAt p σ U V N k, (U.block x).creator ∈ A ∧
        S.slotRound k + p.voteOffset ≤ (U.block x).round from fun k => h _ k rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro k hn v hv
    rw [witnessAt]
    simp only [decisionAt, decideSlot] at hv
    cases hd : tryDirect p σ U V k with
    | some w =>
      have hd' := hd
      unfold tryDirect at hd'
      split at hd'
      · rename_i hskip
        obtain rfl : w = none := (Option.some.inj hd').symm
        obtain ⟨x, hx, hxV, hxA⟩ := exists_held_of_holdsAtLeast hA hsk hskip
        exact ⟨x, Finset.mem_inter.mpr ⟨hx, hxV⟩, hxA,
          by rw [(mem_blocksAt.mp (Finset.mem_filter.mp hx).1).2]⟩
      · rename_i hskip
        obtain ⟨L, hL, hLw⟩ := Option.map_eq_some_iff.mp hd'
        subst hLw
        obtain ⟨hmem, -⟩ := leastOf_eq_some hL
        obtain ⟨-, hcommit⟩ := Finset.mem_filter.mp hmem
        obtain ⟨x, hx, hxV, hxA⟩ := exists_held_of_holdsAtLeast hA hcm hcommit
        refine ⟨x, Finset.mem_inter.mpr ⟨hx, hxV⟩, hxA, ?_⟩
        rw [(mem_blocksAt.mp (Finset.mem_filter.mp hx).1).2]
        omega
    | none =>
      rw [hd] at hv
      obtain ⟨hr, -⟩ := scan_sound (σ := σ) (U := U) (V := V) hl hc N (N - k) (by omega)
      obtain ⟨e, he, ⟨B, hB⟩, helig, hwit⟩ := anchor_of_tryIndirect
        (wit := fun j => if _ : k < j ∧ j ≤ N then witnessAt p σ U V N j else ∅) _ v hv
      have hmem : e.1 ∈ List.range' (N + 1 - (N - k)) (N - k) := hr ▸ List.mem_map_of_mem he
      rw [List.mem_range'_1] at hmem
      have hkj : k < e.1 ∧ e.1 ≤ N := by omega
      have hdec : decisionAt p σ U V N e.1 = some (some B) := by
        rw [← scan_entry N (N - k) (by omega) e he, hB]
      obtain ⟨x, hx, hxA, hxr⟩ := ih (N + 1 - e.1) (by omega) e.1 rfl _ hdec
      refine ⟨x, hwit (by simpa [hkj] using hx), hxA, ?_⟩
      omega

variable [P.Mechanised]

/-- **The witness's histories**, as a view. -/
def witnessView (p : Params) (σ : VoteSel Validator BlockId Payload P honest)
    (U : BlockRecord Validator BlockId Payload P honest) (V : U.View) (N k : ℕ) : U.View :=
  U.historiesView (witnessAt p σ U V N k) ((witnessAt_subset N k).trans V.subset_ids)

omit [Fintype Validator] in
theorem witnessView_subset (N k : ℕ) : (witnessView p σ U V N k).ids ⊆ V.ids := fun _ hi => by
  obtain ⟨a, ha, hia⟩ := Finset.mem_biUnion.mp
    (show _ ∈ (witnessAt p σ U V N k).biUnion (history U) from hi)
  exact history_subset_view (witnessAt_subset N k ha) hia

omit [Fintype Validator] in
/-- **The witness's histories decide as the view does.** -/
theorem decisionAt_witnessView (hl : 1 ≤ p.linkSize) (hcm : 1 ≤ p.commitThreshold)
    (hc : p.voteIsCert = false → 1 ≤ p.certThreshold) {N k : ℕ} {v : Option BlockId}
    (h : decisionAt p σ U V N k = some v) :
    decisionAt p σ U (witnessView p σ U V N k) N k = some v :=
  decisionAt_of_witness hl hcm hc N k _ (witnessView_subset N k)
    (fun a ha => Finset.mem_biUnion.mpr ⟨a, ha, mem_history_self⟩) v h

end Scheme

end LeanDag
