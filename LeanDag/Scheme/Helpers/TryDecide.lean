import LeanDag.Scheme.Model.TryDecide
import LeanDag.Scheme.Helpers.Sufficiency
/-!
# The commit loop decides only what the relation derives

Every decision the loop makes is a derivation of `Decided` from the same
view: a direct decision by the direct constructors, an indirect one by
the indirect constructors, the walk over the later slots supplying the
nearest eligible committed anchor and the skipped slots between. A
candidate linked from an anchor the view holds lies in the view, when
the link and the certificate thresholds are positive, so the least
linked candidate the view holds is the tie-break's choice and an empty
set of them is an empty rung.
-/

namespace LeanDag

namespace Scheme

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [LinearOrder BlockId] {Payload : Type}
variable {P : Validity Validator BlockId Payload} {honest : Finset Validator}
variable {p : Params} {σ : VoteSel Validator BlockId Payload P honest} [S : Slots Validator]
variable {U : BlockRecord Validator BlockId Payload P honest} {V : U.View}

omit [Fintype Validator] [LinearOrder BlockId] in
theorem mem_candidatesIn {k : ℕ} {L : BlockId} :
    L ∈ candidatesIn U V k ↔
      L ∈ V.ids ∧ (U.block L).creator = S.leader k ∧ (U.block L).round = S.slotRound k := by
  simp [candidatesIn]

omit [Fintype Validator] [LinearOrder BlockId] in
theorem isLeaderBlock_of_mem_candidatesIn {k : ℕ} {L : BlockId} (h : L ∈ candidatesIn U V k) :
    IsLeaderBlock U k L := by
  obtain ⟨hV, hc, hr⟩ := mem_candidatesIn.mp h
  exact ⟨V.subset_ids hV, hr, hc⟩

omit [Fintype Validator] [DecidableEq Validator] S in
theorem leastOf_eq_some {s : Finset BlockId} {L : BlockId} (h : leastOf s = some L) :
    L ∈ s ∧ ∀ L' ∈ s, L ≤ L' := by
  unfold leastOf at h
  split at h
  · rename_i hs
    cases h
    exact ⟨s.min'_mem hs, fun L' hL' => s.min'_le L' hL'⟩
  · cases h

omit [Fintype Validator] [DecidableEq Validator] S in
theorem leastOf_eq_none {s : Finset BlockId} (h : leastOf s = none) : s = ∅ := by
  unfold leastOf at h
  split at h
  · cases h
  · rename_i hs
    exact Finset.not_nonempty_iff_eq_empty.mp hs

omit [Fintype Validator] S in
/-- A view holds the history of every block it holds. -/
theorem history_subset_view {A : BlockId} (hA : A ∈ V.ids) : history U A ⊆ V.ids := by
  suffices h : ∀ n b, b ∈ V.ids → historyUpto U n b ⊆ V.ids from h _ A hA
  intro n
  induction n with
  | zero => intro b hb x hx; simp at hx; exact hx ▸ hb
  | succ n ih =>
    intro b hb x hx
    rcases mem_historyUpto_succ.mp hx with rfl | ⟨j, hj, hxj⟩
    · exact hb
    · exact ih j (V.complete b hb j hj) hxj

omit [Fintype Validator] in
/-- **A candidate linked from an anchor the view holds lies in the view**,
at positive link and certificate thresholds. -/
theorem mem_view_of_link (hl : 1 ≤ p.linkSize) (hc : p.voteIsCert = false → 1 ≤ p.certThreshold)
    {k : ℕ} {A L : BlockId} (hA : A ∈ V.ids)
    (h : p.linkSize ≤ (creatorsOf U.block ((certsAt p σ U L (S.slotRound k)).filter
      (fun C => C ∈ history U A))).card) : L ∈ V.ids := by
  obtain ⟨v, hv⟩ := Finset.card_pos.mp (lt_of_lt_of_le hl h)
  obtain ⟨C, hC, -⟩ := mem_creatorsOf.mp hv
  obtain ⟨hCc, hCA⟩ := Finset.mem_filter.mp hC
  have hCV : C ∈ V.ids := history_subset_view hA hCA
  have hcert := (Finset.mem_filter.mp hCc).2
  unfold IsCert at hcert
  split at hcert
  · exact history_subset_view hCV (σ.sound U C _ _ L hcert).1
  · rename_i hv
    obtain ⟨b, hb, hbL⟩ := exists_vote_of_carriesVotes (hc (by simpa using hv)) hcert
    exact history_subset_view (V.complete C hCV b hb) (σ.sound U b _ _ L hbL).1

/-- A slot's decision is sound, and a commit names a candidate the view
holds. -/
def SoundAt (p : Params) (σ : VoteSel Validator BlockId Payload P honest)
    (U : BlockRecord Validator BlockId Payload P honest) (V : U.View) (k : ℕ)
    (s : Option (Option BlockId)) : Prop :=
  ∀ v, s = some v → (schemeAnchored p σ).Decided U V k v ∧ ∀ A, v = some A → A ∈ candidatesIn U V k

omit [Fintype Validator] in
theorem tryDirect_sound {k : ℕ} : SoundAt p σ U V k (tryDirect p σ U V k) := by
  intro v hv
  unfold tryDirect at hv
  split at hv
  · rename_i hs
    cases hv
    exact ⟨.directSkip hs, fun _ h => by cases h⟩
  · cases hL : leastOf ((candidatesIn U V k).filter
        (fun L => (schemeAnchored p σ).Commit U V L (S.slotRound k) (S.kind k))) with
    | none => rw [hL] at hv; cases hv
    | some L =>
      rw [hL] at hv
      cases hv
      obtain ⟨hmem, -⟩ := leastOf_eq_some hL
      obtain ⟨hc, hcommit⟩ := Finset.mem_filter.mp hmem
      exact ⟨.directCommit (isLeaderBlock_of_mem_candidatesIn hc) hcommit,
        fun A h => by cases h; exact hc⟩

omit [Fintype Validator] in
/-- **The walk over the later slots is sound.** The slots of the list are
consecutive from `a`, each sound, and every eligible slot between `k`
and `a` is skipped. -/
theorem tryIndirect_sound (hl : 1 ≤ p.linkSize)
    (hc : p.voteIsCert = false → 1 ≤ p.certThreshold) {k : ℕ} :
    ∀ (l : List (ℕ × Option (Option BlockId))) (a : ℕ),
      l.map Prod.fst = List.range' a l.length → k < a →
      (∀ e ∈ l, SoundAt p σ U V e.1 e.2) →
      (∀ m, k < m → m < a → (schemeAnchored p σ).Eligible k m →
        (schemeAnchored p σ).Decided U V m none) →
      SoundAt p σ U V k (tryIndirect p σ U V k l) := by
  intro l
  induction l with
  | nil => intro a _ _ _ _ v hv; cases hv
  | cons e rest ih =>
    obtain ⟨j, s⟩ := e
    intro a hrange hka hsound hmid v hv
    simp only [List.map_cons, List.length_cons, List.range'_succ, List.cons.injEq] at hrange
    obtain ⟨rfl, hrest⟩ := hrange
    have hsj := hsound (j, s) (List.mem_cons_self ..)
    have hrest_sound : ∀ e ∈ rest, SoundAt p σ U V e.1 e.2 :=
      fun e he => hsound e (List.mem_cons_of_mem _ he)
    have helig_iff : (schemeAnchored p σ).Eligible k j ↔
        S.slotRound k + (p.waveLength - 1) + 1 ≤ S.slotRound j :=
      (schemeAnchored p σ).eligible_iff
    unfold tryIndirect at hv
    split at hv
    · rename_i helig
      have helig' := helig_iff.mpr helig
      rcases s with _ | _ | A
      · simp at hv
      · exact ih (j + 1) hrest (by omega) hrest_sound (fun m h1 h2 hm => by
          rcases Nat.lt_succ_iff_lt_or_eq.mp h2 with h2 | rfl
          · exact hmid m h1 h2 hm
          · exact (hsj none rfl).1) v hv
      · obtain ⟨hdA, hAc⟩ := hsj (some A) rfl
        have hAV : A ∈ V.ids := (mem_candidatesIn.mp (hAc A rfl)).1
        simp only [Option.some.injEq] at hv
        subst hv
        cases hL : leastOf ((candidatesIn U V k).filter (fun L => p.linkSize ≤
            (creatorsOf U.block ((certsAt p σ U L (S.slotRound k)).filter
              (fun C => C ∈ history U A))).card)) with
        | none =>
          refine ⟨.indirectSkip (by omega) helig' hdA hmid (fun i hi L hL' hlink => ?_),
            fun _ h => by cases h⟩
          have hLV := mem_view_of_link hl hc hAV hlink
          have hmem : L ∈ (candidatesIn U V k).filter (fun L => p.linkSize ≤
              (creatorsOf U.block ((certsAt p σ U L (S.slotRound k)).filter
                (fun C => C ∈ history U A))).card) :=
            Finset.mem_filter.mpr ⟨mem_candidatesIn.mpr ⟨hLV, hL'.2.2, hL'.2.1⟩, hlink⟩
          rw [leastOf_eq_none hL] at hmem
          exact Finset.notMem_empty _ hmem
        | some L =>
          obtain ⟨hmem, hmin⟩ := leastOf_eq_some hL
          obtain ⟨hLc, hlink⟩ := Finset.mem_filter.mp hmem
          refine ⟨.indirectCommit (i := 0) (by omega) helig' hdA hmid Nat.one_pos
            (fun _ h => absurd h (Nat.not_lt_zero _)) (isLeaderBlock_of_mem_candidatesIn hLc)
            hlink (fun L' hL' hlink' hlt => ?_), fun _ h => by cases h; exact hLc⟩
          have hL'V := mem_view_of_link hl hc hAV hlink'
          have := hmin L' (Finset.mem_filter.mpr
            ⟨mem_candidatesIn.mpr ⟨hL'V, hL'.2.2, hL'.2.1⟩, hlink'⟩)
          exact absurd hlt (not_lt.mpr this)
    · rename_i hne
      exact ih (j + 1) hrest (by omega) hrest_sound (fun m h1 h2 hm => by
        rcases Nat.lt_succ_iff_lt_or_eq.mp h2 with h2 | rfl
        · exact hmid m h1 h2 hm
        · exact absurd (helig_iff.mp hm) hne) v hv

omit [Fintype Validator] in
/-- **The scan is sound**, and its slots are `N + 1 − m, …, N`. -/
theorem scan_sound (hl : 1 ≤ p.linkSize) (hc : p.voteIsCert = false → 1 ≤ p.certThreshold)
    (N : ℕ) : ∀ m, m ≤ N + 1 →
      (scan p σ U V N m).map Prod.fst = List.range' (N + 1 - m) m ∧
      ∀ e ∈ scan p σ U V N m, SoundAt p σ U V e.1 e.2 := by
  intro m
  induction m with
  | zero => intro _; simp [scan]
  | succ m ih =>
    intro hm
    obtain ⟨hrange, hsound⟩ := ih (by omega)
    have hlen : (scan p σ U V N m).length = m := by
      simpa using congrArg List.length hrange
    refine ⟨?_, ?_⟩
    · simp only [scan, List.map_cons, hrange, List.range'_succ]
      congr 1 <;> [omega; (congr 1; omega)]
    · intro e he
      simp only [scan, List.mem_cons] at he
      rcases he with rfl | he
      · intro v hv
        simp only [decideSlot] at hv
        cases hd : tryDirect p σ U V (N - m) with
        | some w =>
          rw [hd] at hv
          simp only [Option.some.injEq] at hv
          subst hv
          exact tryDirect_sound w hd
        | none =>
          rw [hd] at hv
          exact tryIndirect_sound hl hc _ (N - m + 1) (by rw [hrange, hlen]; congr 1; omega)
            (by omega) hsound (fun m' h1 h2 _ => absurd h2 (by omega)) v hv
      · exact hsound e he

omit [Fintype Validator] [DecidableEq Validator] [LinearOrder BlockId] S in
theorem range_takeWhile {β : Type} (q : ℕ × β → Bool) :
    ∀ (l : List (ℕ × β)) (a : ℕ), l.map Prod.fst = List.range' a l.length →
      (l.takeWhile q).map Prod.fst = List.range' a (l.takeWhile q).length := by
  intro l
  induction l with
  | nil => intro a _; simp
  | cons e rest ih =>
    intro a h
    simp only [List.map_cons, List.length_cons, List.range'_succ, List.cons.injEq] at h
    simp only [List.takeWhile_cons]
    split
    · simp only [List.map_cons, List.length_cons, List.range'_succ, h.1, ih (a + 1) h.2]
    · simp

omit [Fintype Validator] [DecidableEq Validator] [LinearOrder BlockId] S in
theorem mem_takeWhile' {β : Type} {q : β → Bool} :
    ∀ {l : List β} {e : β}, e ∈ l.takeWhile q → e ∈ l ∧ q e = true := by
  intro l
  induction l with
  | nil => intro e h; simp at h
  | cons x rest ih =>
    intro e h
    simp only [List.takeWhile_cons] at h
    split at h
    · rename_i hx
      rcases List.mem_cons.mp h with rfl | h
      · exact ⟨List.mem_cons_self .., hx⟩
      · exact ⟨List.mem_cons_of_mem _ (ih h).1, (ih h).2⟩
    · simp at h

omit [Fintype Validator] in
/-- **`TryDecide` outputs only derivable verdicts**, at consecutive slots
from `lo`. -/
theorem tryDecide_sound (hl : 1 ≤ p.linkSize) (hc : p.voteIsCert = false → 1 ≤ p.certThreshold)
    {lo N : ℕ} (hlo : lo ≤ N + 1) :
    (tryDecide p σ U V lo N).map Prod.fst = List.range' lo (tryDecide p σ U V lo N).length ∧
    ∀ e ∈ tryDecide p σ U V lo N, (schemeAnchored p σ).Decided U V e.1 e.2 := by
  obtain ⟨hrange, hsound⟩ := scan_sound (σ := σ) (U := U) (V := V) hl hc N (N + 1 - lo)
    (by omega)
  rw [show N + 1 - (N + 1 - lo) = lo by omega] at hrange
  refine ⟨?_, ?_⟩
  · unfold tryDecide
    rw [List.map_map, List.length_map]
    have hlen : (scan p σ U V N (N + 1 - lo)).length = N + 1 - lo := by
      simpa using congrArg List.length hrange
    have := range_takeWhile (fun e : ℕ × Option (Option BlockId) => e.2.isSome) _ lo
      (by rw [hrange, hlen])
    simpa [Function.comp_def] using this
  · intro e he
    unfold tryDecide at he
    obtain ⟨e', he', rfl⟩ := List.mem_map.mp he
    obtain ⟨hmem, hsome⟩ := mem_takeWhile' he'
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hsome
    have := (hsound e' hmem v hv).1
    simpa [hv] using this

omit [Fintype Validator] [DecidableEq Validator] [LinearOrder BlockId] S in
/-- Two lists over consecutive slots from `lo` that agree at every common
slot are prefix-comparable. -/
theorem prefix_or_prefix {β : Type} :
    ∀ (l₁ l₂ : List (ℕ × β)) (lo : ℕ),
      l₁.map Prod.fst = List.range' lo l₁.length → l₂.map Prod.fst = List.range' lo l₂.length →
      (∀ e₁ ∈ l₁, ∀ e₂ ∈ l₂, e₁.1 = e₂.1 → e₁.2 = e₂.2) → l₁ <+: l₂ ∨ l₂ <+: l₁ := by
  intro l₁
  induction l₁ with
  | nil => intro l₂ _ _ _ _; exact Or.inl (List.nil_prefix)
  | cons e₁ r₁ ih =>
    intro l₂ lo h₁ h₂ hagree
    cases l₂ with
    | nil => exact Or.inr List.nil_prefix
    | cons e₂ r₂ =>
      simp only [List.map_cons, List.length_cons, List.range'_succ, List.cons.injEq] at h₁ h₂
      have he : e₁ = e₂ := Prod.ext (h₁.1.trans h₂.1.symm)
        (hagree e₁ (List.mem_cons_self ..) e₂ (List.mem_cons_self ..) (h₁.1.trans h₂.1.symm))
      subst he
      rcases ih r₂ (lo + 1) h₁.2 h₂.2 (fun a ha b hb => hagree a (List.mem_cons_of_mem _ ha) b
        (List.mem_cons_of_mem _ hb)) with h | h
      · exact Or.inl (List.prefix_cons_inj _ |>.mpr h)
      · exact Or.inr (List.prefix_cons_inj _ |>.mpr h)

omit [Fintype Validator] in
/-- **Two validators' outputs are prefix-comparable** when the rule has
its laws: every common slot carries one verdict. -/
theorem tryDecide_prefix (hl : 1 ≤ p.linkSize) (hc : p.voteIsCert = false → 1 ≤ p.certThreshold)
    {I : Slots Validator → BlockRecord Validator BlockId Payload P honest → Prop}
    (hlaws : (schemeAnchored p σ).Laws I) (hI : I S U) {lo N₁ N₂ : ℕ} (h₁ : lo ≤ N₁ + 1)
    (h₂ : lo ≤ N₂ + 1) (V₁ V₂ : U.View) :
    tryDecide p σ U V₁ lo N₁ <+: tryDecide p σ U V₂ lo N₂ ∨
      tryDecide p σ U V₂ lo N₂ <+: tryDecide p σ U V₁ lo N₁ := by
  obtain ⟨r₁, s₁⟩ := tryDecide_sound (σ := σ) (U := U) (V := V₁) hl hc h₁
  obtain ⟨r₂, s₂⟩ := tryDecide_sound (σ := σ) (U := U) (V := V₂) hl hc h₂
  refine prefix_or_prefix _ _ lo r₁ r₂ fun e₁ he₁ e₂ he₂ heq => ?_
  have d₁ := s₁ e₁ he₁
  have d₂ := s₂ e₂ he₂
  rw [heq] at d₁
  exact AnchoredRule.decided_unique hlaws hI d₁ V₂ _ d₂

end Scheme

end LeanDag
