import LeanDag.Scheme.Model.TryDecide
import LeanDag.Scheme.Helpers.Sufficiency
import LeanDag.Common.Anchored.Bounded
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

omit [Fintype Validator] S in
/-- A candidate certified by a block the view holds lies in the view, at a
positive certificate threshold. -/
theorem mem_view_of_cert (hc : p.voteIsCert = false → 1 ≤ p.certThreshold)
    {r : ℕ} {C L : BlockId} (hCV : C ∈ V.ids) (hC : C ∈ certsAt p σ U L r) : L ∈ V.ids := by
  have hcert := (Finset.mem_filter.mp hC).2
  cases hv : p.voteIsCert
  · obtain ⟨b, hb, hbL⟩ := exists_vote_of_carriesVotes (hc hv)
      ((isCert_iff_carries σ p hv).mp hcert)
    exact history_subset_view (V.complete C hCV b hb) (σ.sound U b _ _ L hbL).1
  · exact history_subset_view hCV (σ.sound U C _ _ L ((isCert_iff_votes σ p hv).mp hcert)).1

omit [Fintype Validator] in
/-- **A candidate linked from an anchor the view holds lies in the view**,
at positive link and certificate thresholds. -/
theorem mem_view_of_link (hl : 1 ≤ p.linkSize) (hc : p.voteIsCert = false → 1 ≤ p.certThreshold)
    {k : ℕ} {A L : BlockId} (hA : A ∈ V.ids)
    (h : p.linkSize ≤ (creatorsOf U.block (linkCerts p σ U A L (S.slotRound k))).card) :
    L ∈ V.ids := by
  obtain ⟨v, hv⟩ := Finset.card_pos.mp (lt_of_lt_of_le hl h)
  obtain ⟨C, hC, -⟩ := mem_creatorsOf.mp hv
  obtain ⟨hCc, hCA⟩ := Finset.mem_filter.mp hC
  exact mem_view_of_cert hc (history_subset_view hA hCA) hCc

/-- A slot's decision is derived below the bound `B`, and a commit names a
candidate the view holds. -/
def SoundAt (p : Params) (σ : VoteSel Validator BlockId Payload P honest)
    (U : BlockRecord Validator BlockId Payload P honest) (V : U.View) (B k : ℕ)
    (s : Option (Option BlockId)) : Prop :=
  ∀ v, s = some v → (schemeAnchored p σ).DecidedWithin U V B k v ∧
    ∀ A, v = some A → A ∈ candidatesIn U V k

omit [Fintype Validator] in
theorem tryDirect_sound {B k : ℕ} (hk : k < B) : SoundAt p σ U V B k (tryDirect p σ U V k) := by
  intro v hv
  unfold tryDirect at hv
  split at hv
  · rename_i hs
    cases hv
    exact ⟨.directSkip hk hs, fun _ h => by cases h⟩
  · cases hL : leastOf ((candidatesIn U V k).filter
        (fun L => (schemeAnchored p σ).Commit U V L (S.slotRound k) (S.kind k))) with
    | none => rw [hL] at hv; cases hv
    | some L =>
      rw [hL] at hv
      cases hv
      obtain ⟨hmem, -⟩ := leastOf_eq_some hL
      obtain ⟨hc, hcommit⟩ := Finset.mem_filter.mp hmem
      exact ⟨.directCommit hk (isLeaderBlock_of_mem_candidatesIn hc) hcommit,
        fun A h => by cases h; exact hc⟩

omit [Fintype Validator] in
/-- **The walk over the later slots is sound.** The slots of the list are
consecutive from `a` and below `B`, each sound, and every eligible slot
between `k` and `a` is skipped. -/
theorem tryIndirect_sound (hl : 1 ≤ p.linkSize)
    (hc : p.voteIsCert = false → 1 ≤ p.certThreshold) {B k : ℕ} :
    ∀ (l : List (ℕ × Option (Option BlockId))) (a : ℕ),
      l.map Prod.fst = List.range' a l.length → k < a → a + l.length ≤ B →
      (∀ e ∈ l, SoundAt p σ U V B e.1 e.2) →
      (∀ m, k < m → m < a → (schemeAnchored p σ).Eligible k m →
        (schemeAnchored p σ).DecidedWithin U V B m none) →
      SoundAt p σ U V B k (tryIndirect p σ U V k l) := by
  intro l
  induction l with
  | nil => intro a _ _ _ _ _ v hv; cases hv
  | cons e rest ih =>
    obtain ⟨j, s⟩ := e
    intro a hrange hka haB hsound hmid v hv
    simp only [List.map_cons, List.length_cons, List.range'_succ, List.cons.injEq] at hrange
    obtain ⟨rfl, hrest⟩ := hrange
    have hsj := hsound (j, s) (List.mem_cons_self ..)
    have hjB : j < B := by simp only [List.length_cons] at haB; omega
    have haB' : j + 1 + rest.length ≤ B := by simp only [List.length_cons] at haB; omega
    have hrest_sound : ∀ e ∈ rest, SoundAt p σ U V B e.1 e.2 :=
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
      · exact ih (j + 1) hrest (by omega) haB' hrest_sound (fun m h1 h2 hm => by
          rcases Nat.lt_succ_iff_lt_or_eq.mp h2 with h2 | rfl
          · exact hmid m h1 h2 hm
          · exact (hsj none rfl).1) v hv
      · obtain ⟨hdA, hAc⟩ := hsj (some A) rfl
        have hAV : A ∈ V.ids := (mem_candidatesIn.mp (hAc A rfl)).1
        simp only [Option.some.injEq] at hv
        subst hv
        cases hL : leastOf ((candidatesIn U V k).filter (fun L => p.linkSize ≤
            (creatorsOf U.block (linkCerts p σ U A L (S.slotRound k))).card)) with
        | none =>
          refine ⟨.indirectSkip (by omega) hjB helig' hdA hmid (fun i hi L hL' hlink => ?_),
            fun _ h => by cases h⟩
          have hLV := mem_view_of_link hl hc hAV hlink
          have hmem : L ∈ (candidatesIn U V k).filter (fun L => p.linkSize ≤
              (creatorsOf U.block (linkCerts p σ U A L (S.slotRound k))).card) :=
            Finset.mem_filter.mpr ⟨mem_candidatesIn.mpr ⟨hLV, hL'.2.2, hL'.2.1⟩, hlink⟩
          rw [leastOf_eq_none hL] at hmem
          exact Finset.notMem_empty _ hmem
        | some L =>
          obtain ⟨hmem, hmin⟩ := leastOf_eq_some hL
          obtain ⟨hLc, hlink⟩ := Finset.mem_filter.mp hmem
          refine ⟨.indirectCommit (i := 0) (by omega) hjB helig' hdA hmid Nat.one_pos
            (fun _ h => absurd h (Nat.not_lt_zero _)) (isLeaderBlock_of_mem_candidatesIn hLc)
            hlink (fun L' hL' hlink' hlt => ?_), fun _ h => by cases h; exact hLc⟩
          have hL'V := mem_view_of_link hl hc hAV hlink'
          have := hmin L' (Finset.mem_filter.mpr
            ⟨mem_candidatesIn.mpr ⟨hL'V, hL'.2.2, hL'.2.1⟩, hlink'⟩)
          exact absurd hlt (not_lt.mpr this)
    · rename_i hne
      exact ih (j + 1) hrest (by omega) haB' hrest_sound (fun m h1 h2 hm => by
        rcases Nat.lt_succ_iff_lt_or_eq.mp h2 with h2 | rfl
        · exact hmid m h1 h2 hm
        · exact absurd (helig_iff.mp hm) hne) v hv

omit [Fintype Validator] in
/-- **The scan is sound**, below `N + 1`, and its slots are `N + 1 − m, …, N`. -/
theorem scan_sound (hl : 1 ≤ p.linkSize) (hc : p.voteIsCert = false → 1 ≤ p.certThreshold)
    (N : ℕ) : ∀ m, m ≤ N + 1 →
      (scan p σ U V N m).map Prod.fst = List.range' (N + 1 - m) m ∧
      ∀ e ∈ scan p σ U V N m, SoundAt p σ U V (N + 1) e.1 e.2 := by
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
          exact tryDirect_sound (by omega) w hd
        | none =>
          rw [hd] at hv
          exact tryIndirect_sound hl hc _ (N - m + 1) (by rw [hrange, hlen]; congr 1; omega)
            (by omega) (by rw [hlen]; omega) hsound (fun m' h1 h2 _ => absurd h2 (by omega)) v hv
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
    have := (hsound e' hmem v hv).1.toDecided
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

/-! ## Completeness -/

omit [Fintype Validator] in
/-- Every entry of the scan is the loop's decision for its slot. -/
theorem scan_entry (N : ℕ) : ∀ m, m ≤ N + 1 → ∀ e ∈ scan p σ U V N m,
    e.2 = decisionAt p σ U V N e.1 := by
  intro m
  induction m with
  | zero => intro _ e he; simp [scan] at he
  | succ m ih =>
    intro hm e he
    simp only [scan, List.mem_cons] at he
    rcases he with rfl | he
    · simp only [decisionAt]
      rw [show N - (N - m) = m by omega]
    · exact ih (by omega) e he

omit [Fintype Validator] S in
/-- A direct commit holds a candidate the view holds, at positive commit
and certificate thresholds. -/
theorem mem_view_of_commit (hcm : 1 ≤ p.commitThreshold)
    (hc : p.voteIsCert = false → 1 ≤ p.certThreshold) {r κ : ℕ} {L : BlockId}
    (h : (schemeAnchored p σ).Commit U V L r κ) : L ∈ V.ids := by
  have h' : p.commitThreshold ≤ (heldAuthors U V (certsAt p σ U L r)).card := h
  obtain ⟨v, hv⟩ := Finset.card_pos.mp (lt_of_lt_of_le hcm h')
  obtain ⟨C, hC, hCV, -⟩ := mem_heldAuthors.mp hv
  exact mem_view_of_cert hc hCV hC

omit [Fintype Validator] in
/-- **The walk finds the anchor**: past skipped and ineligible slots, at
the first committed eligible slot it decides from that anchor. -/
theorem tryIndirect_eq {k : ℕ} {ent : ℕ → Option (Option BlockId)} {j : ℕ} {A : BlockId}
    (hj : S.slotRound k + (p.waveLength - 1) + 1 ≤ S.slotRound j) (hjA : ent j = some (some A))
    (hmid : ∀ m, k < m → m < j → S.slotRound k + (p.waveLength - 1) + 1 ≤ S.slotRound m →
      ent m = some none) :
    ∀ (l : List (ℕ × Option (Option BlockId))) (a : ℕ),
      l.map Prod.fst = List.range' a l.length → k < a → a ≤ j → j < a + l.length →
      (∀ e ∈ l, e.2 = ent e.1) →
      tryIndirect p σ U V k l = some (leastOf ((candidatesIn U V k).filter
        (fun L => p.linkSize ≤ (creatorsOf U.block (linkCerts p σ U A L (S.slotRound k))).card))) := by
  intro l
  induction l with
  | nil => intro a _ _ _ h _; simp at h; omega
  | cons e rest ih =>
    obtain ⟨m, s⟩ := e
    intro a hrange hka haj hjl hent
    simp only [List.map_cons, List.length_cons, List.range'_succ, List.cons.injEq] at hrange
    obtain ⟨rfl, hrest⟩ := hrange
    have hs : s = ent m := hent (m, s) (List.mem_cons_self ..)
    have hent' : ∀ e ∈ rest, e.2 = ent e.1 := fun e he => hent e (List.mem_cons_of_mem _ he)
    have hlen : rest.length = (rest.map Prod.fst).length := by simp
    rcases Nat.lt_or_eq_of_le haj with hlt | rfl
    · have hrec := ih (m + 1) hrest (by omega) (by omega)
        (by simp only [List.length_cons] at hjl; omega) hent'
      unfold tryIndirect
      split
      · rename_i helig
        rw [hs, hmid m hka hlt helig]
        exact hrec
      · exact hrec
    · unfold tryIndirect
      rw [if_pos hj, hs, hjA]

/-- **Completeness of a slot's decision.** A verdict the bounded relation
derives below `N + 1` is the loop's decision, when the rule has its laws. -/
theorem decisionAt_complete (hl : 1 ≤ p.linkSize) (hcm : 1 ≤ p.commitThreshold)
    (hc : p.voteIsCert = false → 1 ≤ p.certThreshold)
    {I : Slots Validator → BlockRecord Validator BlockId Payload P honest → Prop}
    (hlaws : (schemeAnchored p σ).Laws I) (hI : I S U) {N B k : ℕ} {v : Option BlockId}
    (hB : B ≤ N + 1) (h : (schemeAnchored p σ).DecidedWithin U V B k v) :
    decisionAt p σ U V N k = some v := by
  -- A direct decision, when there is one, is the derived one.
  have hdirect : ∀ {k w v}, (schemeAnchored p σ).Decided U V k v →
      tryDirect p σ U V k = some w → w = v := fun {k w v} hd hw =>
    AnchoredRule.decided_unique hlaws hI
      (tryDirect_sound (Nat.lt_succ_self k) w hw).1.toDecided V v hd
  -- The scan below slot `k` lists slots `k + 1, …, N`.
  have hscan : ∀ k, k ≤ N →
      (scan p σ U V N (N - k)).map Prod.fst = List.range' (k + 1) (N - k) ∧
      (scan p σ U V N (N - k)).length = N - k ∧
      ∀ e ∈ scan p σ U V N (N - k), e.2 = decisionAt p σ U V N e.1 := fun k hk => by
    obtain ⟨hr, -⟩ := scan_sound (σ := σ) (U := U) (V := V) hl hc N (N - k) (by omega)
    refine ⟨by rw [hr]; congr 1; omega, by simpa using congrArg List.length hr,
      scan_entry N (N - k) (by omega)⟩
  -- The anchor the scan finds is the anchor the derivation names.
  have hwalk : ∀ {k j : ℕ} {A : BlockId}, k < j → j ≤ N → (schemeAnchored p σ).Eligible k j →
      decisionAt p σ U V N j = some (some A) →
      (∀ m, k < m → m < j → (schemeAnchored p σ).Eligible k m →
        decisionAt p σ U V N m = some none) →
      tryIndirect p σ U V k (scan p σ U V N (N - k)) = some (leastOf ((candidatesIn U V k).filter
        (fun L => p.linkSize ≤ (creatorsOf U.block (linkCerts p σ U A L (S.slotRound k))).card))) := fun {k j A} hkj hjN helig hjA hmid => by
    obtain ⟨hr, hlen, hent⟩ := hscan k (by omega)
    exact tryIndirect_eq ((schemeAnchored p σ).eligible_iff.mp helig) hjA
      (fun m h1 h2 hm => hmid m h1 h2 ((schemeAnchored p σ).eligible_iff.mpr hm))
      _ (k + 1) (by rw [hr, hlen]) (by omega) (by omega) (by rw [hlen]; omega) hent
  -- The anchor's commit is a candidate the view holds.
  have hAV : ∀ {j A}, j ≤ N → decisionAt p σ U V N j = some (some A) → A ∈ V.ids :=
    fun {j A} hjN hjA => by
      obtain ⟨-, hsound⟩ := scan_sound (σ := σ) (U := U) (V := V) hl hc N (N - j + 1) (by omega)
      have hmem : (j, decisionAt p σ U V N j) ∈ scan p σ U V N (N - j + 1) := by
        simp only [scan, decisionAt, List.mem_cons]
        left; congr 1 <;> [omega; (congr 2; omega)]
      exact (mem_candidatesIn.mp ((hsound _ hmem (some A) hjA).2 A rfl)).1
  induction h with
  | @directCommit k L hkB hL hcommit =>
    simp only [decisionAt, decideSlot]
    cases hd : tryDirect p σ U V k with
    | some w => rw [hdirect (.directCommit hL hcommit) hd]
    | none =>
      exfalso
      unfold tryDirect at hd
      split at hd
      · cases hd
      · rename_i hskip
        have hLV := mem_view_of_commit hcm hc hcommit
        have hmem : L ∈ (candidatesIn U V k).filter
            (fun L => (schemeAnchored p σ).Commit U V L (S.slotRound k) (S.kind k)) :=
          Finset.mem_filter.mpr ⟨mem_candidatesIn.mpr ⟨hLV, hL.2.2, hL.2.1⟩, hcommit⟩
        unfold leastOf at hd
        rw [dif_pos ⟨L, hmem⟩] at hd
        cases hd
  | @directSkip k hkB hskip =>
    simp only [decisionAt, decideSlot]
    cases hd : tryDirect p σ U V k with
    | some w => rw [hdirect (.directSkip hskip) hd]
    | none =>
      exfalso
      unfold tryDirect at hd
      rw [if_pos (show HoldsAtLeast U V p.skipThreshold (blamersAt p σ U k) from hskip)] at hd
      cases hd
  | @indirectCommit k j A L i hkj hjB helig hdj hmid hi hemp hL hlink hleast ihj ihmid =>
    have hd := (AnchoredRule.DecidedWithin.indirectCommit hkj hjB helig hdj hmid hi hemp hL
      hlink hleast).toDecided
    simp only [decisionAt, decideSlot]
    cases hdir : tryDirect p σ U V k with
    | some w => rw [hdirect hd hdir]
    | none =>
      have hi0 : i = 0 := by simp only [schemeAnchored] at hi; omega
      subst hi0
      rw [hwalk hkj (by omega) helig ihj (fun m h1 h2 hm => ihmid m h1 h2 hm)]
      have hAV' := hAV (by omega) ihj
      have hLV := mem_view_of_link hl hc hAV' hlink
      have hmem : L ∈ (candidatesIn U V k).filter (fun L => p.linkSize ≤
          (creatorsOf U.block (linkCerts p σ U A L (S.slotRound k))).card) :=
        Finset.mem_filter.mpr ⟨mem_candidatesIn.mpr ⟨hLV, hL.2.2, hL.2.1⟩, hlink⟩
      cases hmin : leastOf ((candidatesIn U V k).filter (fun L => p.linkSize ≤
          (creatorsOf U.block (linkCerts p σ U A L (S.slotRound k))).card)) with
      | none => rw [leastOf_eq_none hmin] at hmem; exact absurd hmem (Finset.notMem_empty _)
      | some L₀ =>
        obtain ⟨hL₀, hle⟩ := leastOf_eq_some hmin
        obtain ⟨hL₀c, hL₀link⟩ := Finset.mem_filter.mp hL₀
        have h1 := hle L hmem
        have h2 : ¬ L₀ < L := hleast L₀ (isLeaderBlock_of_mem_candidatesIn hL₀c) hL₀link
        rw [le_antisymm h1 (not_lt.mp h2)]
  | @indirectSkip k j A hkj hjB helig hdj hmid hemp ihj ihmid =>
    have hd := (AnchoredRule.DecidedWithin.indirectSkip hkj hjB helig hdj hmid hemp).toDecided
    simp only [decisionAt, decideSlot]
    cases hdir : tryDirect p σ U V k with
    | some w => rw [hdirect hd hdir]
    | none =>
      rw [hwalk hkj (by omega) helig ihj (fun m h1 h2 hm => ihmid m h1 h2 hm)]
      cases hmin : leastOf ((candidatesIn U V k).filter (fun L => p.linkSize ≤
          (creatorsOf U.block (linkCerts p σ U A L (S.slotRound k))).card)) with
      | none => rfl
      | some L₀ =>
        exfalso
        obtain ⟨hL₀, -⟩ := leastOf_eq_some hmin
        obtain ⟨hL₀c, hL₀link⟩ := Finset.mem_filter.mp hL₀
        exact hemp 0 (by simp [schemeAnchored]) L₀ (isLeaderBlock_of_mem_candidatesIn hL₀c)
          hL₀link

/-- **Completeness, unbounded.** A verdict the relation derives is the
loop's decision once the scan reaches far enough. -/
theorem decisionAt_eventually (hl : 1 ≤ p.linkSize) (hcm : 1 ≤ p.commitThreshold)
    (hc : p.voteIsCert = false → 1 ≤ p.certThreshold)
    {I : Slots Validator → BlockRecord Validator BlockId Payload P honest → Prop}
    (hlaws : (schemeAnchored p σ).Laws I) (hI : I S U) {k : ℕ} {v : Option BlockId}
    (h : (schemeAnchored p σ).Decided U V k v) :
    ∃ N₀, ∀ N, N₀ ≤ N → decisionAt p σ U V N k = some v := by
  obtain ⟨B, hB⟩ := AnchoredRule.exists_bound h
  exact ⟨B, fun N hN => decisionAt_complete hl hcm hc hlaws hI (by omega) hB⟩

omit [Fintype Validator] [DecidableEq Validator] [LinearOrder BlockId] S in
theorem mem_takeWhile_of {β : Type} {q : ℕ × β → Bool} :
    ∀ (l : List (ℕ × β)) (a : ℕ) {e : ℕ × β}, l.map Prod.fst = List.range' a l.length →
      e ∈ l → (∀ e' ∈ l, e'.1 ≤ e.1 → q e' = true) → e ∈ l.takeWhile q := by
  intro l
  induction l with
  | nil => intro a e _ h; simp at h
  | cons x rest ih =>
    intro a e hr he hq
    simp only [List.map_cons, List.length_cons, List.range'_succ, List.cons.injEq] at hr
    have hx : x.1 ≤ e.1 := by
      rcases List.mem_cons.mp he with rfl | he
      · exact le_rfl
      · have : e.1 ∈ rest.map Prod.fst := List.mem_map_of_mem he
        rw [hr.2, List.mem_range'_1] at this
        omega
    rw [List.takeWhile_cons, if_pos (hq x (List.mem_cons_self ..) hx)]
    rcases List.mem_cons.mp he with rfl | he
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (ih (a + 1) hr.2 he
        fun e' he' h => hq e' (List.mem_cons_of_mem _ he') h)

/-- **`TryDecide` outputs every verdict derived within a bound** `B`, once
every slot from `lo` to `k` has one and the scan reaches `B - 1` and `k`. -/
theorem tryDecide_within (hl : 1 ≤ p.linkSize) (hcm : 1 ≤ p.commitThreshold)
    (hc : p.voteIsCert = false → 1 ≤ p.certThreshold)
    {I : Slots Validator → BlockRecord Validator BlockId Payload P honest → Prop}
    (hlaws : (schemeAnchored p σ).Laws I) (hI : I S U) {lo k B N : ℕ} (hlok : lo ≤ k)
    (hkN : k ≤ N) (hBN : B ≤ N + 1)
    (hall : ∀ m, lo ≤ m → m ≤ k → ∃ v, (schemeAnchored p σ).DecidedWithin U V B m v) :
    ∀ v, (schemeAnchored p σ).Decided U V k v → (k, v) ∈ tryDecide p σ U V lo N := by
  classical
  have hB : ∀ m, lo ≤ m → m ≤ k → ∀ v, (schemeAnchored p σ).Decided U V m v →
      decisionAt p σ U V N m = some v := by
    intro m h1 h2 v hv
    obtain ⟨w, hw⟩ := hall m h1 h2
    rw [AnchoredRule.decided_unique hlaws hI hv V w hw.toDecided]
    exact decisionAt_complete hl hcm hc hlaws hI hBN hw
  intro v hv
  obtain ⟨hrange, -⟩ := scan_sound (σ := σ) (U := U) (V := V) hl hc N (N + 1 - lo) (by omega)
  have hent := scan_entry (p := p) (σ := σ) (U := U) (V := V) N (N + 1 - lo) (by omega)
  have hlen : (scan p σ U V N (N + 1 - lo)).length = N + 1 - lo := by
    simpa using congrArg List.length hrange
  rw [show N + 1 - (N + 1 - lo) = lo by omega] at hrange
  have hmem : (k, decisionAt p σ U V N k) ∈ scan p σ U V N (N + 1 - lo) := by
    have : k ∈ (scan p σ U V N (N + 1 - lo)).map Prod.fst := by
      rw [hrange, List.mem_range'_1]; omega
    obtain ⟨e, he, hek⟩ := List.mem_map.mp this
    have := hent e he
    rw [hek] at this
    rwa [show (k, decisionAt p σ U V N k) = e from Prod.ext hek.symm this.symm]
  have hkv : decisionAt p σ U V N k = some v := hB k hlok le_rfl v hv
  unfold tryDecide
  refine List.mem_map.mpr ⟨(k, decisionAt p σ U V N k), mem_takeWhile_of _ lo
    (by rw [hrange, hlen]) hmem fun e' he' hle => ?_, by simp [hkv]⟩
  have hee := hent e' he'
  have hlo' : lo ≤ e'.1 := by
    have : e'.1 ∈ (scan p σ U V N (N + 1 - lo)).map Prod.fst := List.mem_map_of_mem he'
    rw [hrange, List.mem_range'_1] at this
    omega
  obtain ⟨w, hw⟩ := hall e'.1 hlo' hle
  rw [hee, hB e'.1 hlo' hle w hw.toDecided]
  rfl

/-- **`TryDecide` outputs every derived verdict** once every slot from `lo`
to `k` has one and the scan reaches far enough. -/
theorem tryDecide_eventually (hl : 1 ≤ p.linkSize) (hcm : 1 ≤ p.commitThreshold)
    (hc : p.voteIsCert = false → 1 ≤ p.certThreshold)
    {I : Slots Validator → BlockRecord Validator BlockId Payload P honest → Prop}
    (hlaws : (schemeAnchored p σ).Laws I) (hI : I S U) {lo k : ℕ} (hlok : lo ≤ k)
    (hall : ∀ m, lo ≤ m → m ≤ k → ∃ v, (schemeAnchored p σ).Decided U V m v) :
    ∃ N₀, ∀ N, N₀ ≤ N → ∀ v, (schemeAnchored p σ).Decided U V k v →
      (k, v) ∈ tryDecide p σ U V lo N := by
  classical
  have hb : ∀ m, ∃ B, lo ≤ m → m ≤ k → ∃ v, (schemeAnchored p σ).DecidedWithin U V B m v := by
    intro m
    by_cases hm : lo ≤ m ∧ m ≤ k
    · obtain ⟨v, hv⟩ := hall m hm.1 hm.2
      obtain ⟨B, hB⟩ := AnchoredRule.exists_bound hv
      exact ⟨B, fun _ _ => ⟨v, hB⟩⟩
    · exact ⟨0, fun h1 h2 => absurd ⟨h1, h2⟩ hm⟩
  choose B hB using hb
  refine ⟨(Finset.range (k + 1)).sup B + k, fun N hN => tryDecide_within hl hcm hc hlaws hI hlok
    (by omega) (B := (Finset.range (k + 1)).sup B) (by omega) fun m h1 h2 => ?_⟩
  obtain ⟨v, hv⟩ := hB m h1 h2
  exact ⟨v, hv.mono (Finset.le_sup (f := B) (Finset.mem_range.mpr (by omega)))⟩

end Scheme

end LeanDag
