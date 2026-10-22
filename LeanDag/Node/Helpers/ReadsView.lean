import LeanDag.Scheme.Helpers.TryDecide
import LeanDag.Node.Vote
import LeanDag.Node.Store
/-!
# The commit loop reads only the view, from the slot's round up

Two records, at any validity predicates and honest sets, with views that
agree from a round `R` up (`ViewsAbove`), give the same decisions from
any slot whose round is at least `R`: `tryDecide` is equal on the two.
Every set the loop counts lies at or above the slot's round: the
candidates at it, the blamers and certificates above it, a vote's slot
at it, a certificate's votes one round below it, and a link's
certificates, which the anchor reaches through blocks above them. The
references of blocks at `R` itself are never read.

At `R = 0` the two views hold the same blocks.

`ViewsAbove.of_boundedSel`: at the bounded vote, the vote clause follows
from the others, since the vote reads only the voter's history down to
the slot's round. `ViewsAbove.of_store`: a store agrees with every view
of which it holds the blocks, read alike.
-/

namespace LeanDag

namespace Node

open Scheme

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [LinearOrder BlockId] {Payload : Type}
variable {P₁ P₂ : Validity Validator BlockId Payload} {H₁ H₂ : Finset Validator}

/-- **Two views agree from round `R` up**: the same identifiers at rounds
`R` and above, the same rounds and authors there, the same references
strictly above `R`, and vote rules selecting alike at slots from `R` up. -/
structure ViewsAbove (R : ℕ) {U₁ : BlockRecord Validator BlockId Payload P₁ H₁}
    {U₂ : BlockRecord Validator BlockId Payload P₂ H₂}
    (σ₁ : VoteSel Validator BlockId Payload P₁ H₁) (σ₂ : VoteSel Validator BlockId Payload P₂ H₂)
    (V₁ : U₁.View) (V₂ : U₂.View) : Prop where
  mem : ∀ i ∈ V₁.ids, R ≤ (U₁.block i).round → i ∈ V₂.ids
  mem' : ∀ i ∈ V₂.ids, R ≤ (U₂.block i).round → i ∈ V₁.ids ∧ R ≤ (U₁.block i).round
  round : ∀ i ∈ V₁.ids, R ≤ (U₁.block i).round → (U₂.block i).round = (U₁.block i).round
  creator : ∀ i ∈ V₁.ids, R ≤ (U₁.block i).round → (U₂.block i).creator = (U₁.block i).creator
  refs : ∀ i ∈ V₁.ids, R < (U₁.block i).round → (U₂.block i).refs = (U₁.block i).refs
  sel : ∀ b ∈ V₁.ids, R ≤ (U₁.block b).round → ∀ a r, R ≤ r →
    σ₁.sel U₁ b a r = σ₂.sel U₂ b a r

omit [Fintype Validator] in
/-- The round of a block of a filtered layer. -/
theorem round_of_mem_layer {P : Validity Validator BlockId Payload} {H : Finset Validator}
    {U : BlockRecord Validator BlockId Payload P H} {r : ℕ} {q : BlockId → Prop}
    [DecidablePred q] {x : BlockId} (hx : x ∈ (blocksAt U r).filter q) :
    (U.block x).round = r :=
  (mem_blocksAt.mp (Finset.mem_filter.mp hx).1).2

namespace ViewsAbove

variable {R : ℕ} {U₁ : BlockRecord Validator BlockId Payload P₁ H₁}
variable {U₂ : BlockRecord Validator BlockId Payload P₂ H₂}
variable {σ₁ : VoteSel Validator BlockId Payload P₁ H₁}
variable {σ₂ : VoteSel Validator BlockId Payload P₂ H₂}
variable {V₁ : U₁.View} {V₂ : U₂.View}

omit [Fintype Validator] in
theorem symm (h : ViewsAbove R σ₁ σ₂ V₁ V₂) : ViewsAbove R σ₂ σ₁ V₂ V₁ where
  mem i hi hr := (h.mem' i hi hr).1
  mem' i hi hr := ⟨h.mem i hi hr, by rw [h.round i hi hr]; exact hr⟩
  round i hi hr := by
    obtain ⟨h₁, h₂⟩ := h.mem' i hi hr
    exact (h.round i h₁ h₂).symm
  creator i hi hr := by
    obtain ⟨h₁, h₂⟩ := h.mem' i hi hr
    exact (h.creator i h₁ h₂).symm
  refs i hi hr := by
    obtain ⟨h₁, h₂⟩ := h.mem' i hi hr.le
    have := h.round i h₁ h₂
    exact (h.refs i h₁ (by omega)).symm
  sel b hb hr a r hR := by
    obtain ⟨h₁, h₂⟩ := h.mem' b hb hr
    exact (h.sel b h₁ h₂ a r hR).symm

variable (h : ViewsAbove R σ₁ σ₂ V₁ V₂)
include h

omit [Fintype Validator] in
theorem creatorsOf_eq {s : Finset BlockId}
    (hs : ∀ x ∈ s, x ∈ V₁.ids ∧ R ≤ (U₁.block x).round) :
    creatorsOf U₁.block s = creatorsOf U₂.block s :=
  Finset.image_congr fun x hx => (h.creator x (hs x hx).1 (hs x hx).2).symm

omit [Fintype Validator] in
/-- A round layer at or above `R`, filtered alike, meets the two views alike. -/
theorem layer_inter {r : ℕ} (hr : R ≤ r) {q₁ q₂ : BlockId → Prop} [DecidablePred q₁]
    [DecidablePred q₂] (hq : ∀ x ∈ V₁.ids, (U₁.block x).round = r → (q₁ x ↔ q₂ x)) :
    (blocksAt U₁ r).filter q₁ ∩ V₁.ids = (blocksAt U₂ r).filter q₂ ∩ V₂.ids := by
  ext x
  simp only [Finset.mem_inter, Finset.mem_filter, mem_blocksAt]
  constructor
  · rintro ⟨⟨⟨-, hxr⟩, hq₁⟩, hx⟩
    have hR : R ≤ (U₁.block x).round := by omega
    exact ⟨⟨⟨V₂.subset_ids (h.mem x hx hR), (h.round x hx hR).trans hxr⟩,
      (hq x hx hxr).mp hq₁⟩, h.mem x hx hR⟩
  · rintro ⟨⟨⟨-, hxr⟩, hq₂⟩, hx⟩
    obtain ⟨hx₁, hR⟩ := h.mem' x hx (by omega)
    have hxr₁ : (U₁.block x).round = r := (h.round x hx₁ hR).symm.trans hxr
    exact ⟨⟨⟨V₁.subset_ids hx₁, hxr₁⟩, (hq x hx₁ hxr₁).mpr hq₂⟩, hx₁⟩

omit [Fintype Validator] in
theorem heldAuthors_eq {s₁ s₂ : Finset BlockId} (hs : s₁ ∩ V₁.ids = s₂ ∩ V₂.ids)
    (hR : ∀ x ∈ s₁ ∩ V₁.ids, R ≤ (U₁.block x).round) :
    heldAuthors U₁ V₁ s₁ = heldAuthors U₂ V₂ s₂ := by
  unfold heldAuthors
  rw [← hs]
  exact h.creatorsOf_eq fun x hx => ⟨(Finset.mem_inter.mp hx).2, hR x hx⟩

omit [Fintype Validator] in
theorem holdsAtLeast_iff {s₁ s₂ : Finset BlockId} (hs : s₁ ∩ V₁.ids = s₂ ∩ V₂.ids)
    (hR : ∀ x ∈ s₁ ∩ V₁.ids, R ≤ (U₁.block x).round) (t : ℕ) :
    HoldsAtLeast U₁ V₁ t s₁ ↔ HoldsAtLeast U₂ V₂ t s₂ := by
  unfold HoldsAtLeast
  rw [h.heldAuthors_eq hs hR]

omit [Fintype Validator] in
theorem votes_iff {b L : BlockId} (hb : b ∈ V₁.ids) (hbR : R ≤ (U₁.block b).round)
    (hL : L ∈ V₁.ids) (hLR : R ≤ (U₁.block L).round) :
    σ₁.Votes U₁ b L ↔ σ₂.Votes U₂ b L := by
  unfold VoteSel.Votes
  rw [h.creator L hL hLR, h.round L hL hLR, h.sel b hb hbR _ _ hLR]

omit [Fintype Validator] in
theorem isCert_iff [P₁.Mechanised] (p : Params) {C L : BlockId} (hC : C ∈ V₁.ids)
    (hCR : R < (U₁.block C).round) (hL : L ∈ V₁.ids) (hLR : R ≤ (U₁.block L).round) :
    IsCert p σ₁ U₁ C L ↔ IsCert p σ₂ U₂ C L := by
  unfold IsCert
  split
  · exact h.votes_iff hC hCR.le hL hLR
  · unfold CarriesVotes carriedVotes
    have href : ∀ j ∈ (U₁.block C).refs, j ∈ V₁.ids ∧ R ≤ (U₁.block j).round := fun j hj =>
      ⟨V₁.complete C hC j hj, by
        have := U₁.causal.refs_round C (V₁.subset_ids hC) j hj; omega⟩
    have hf : (U₁.block C).refs.filter (fun b => σ₁.Votes U₁ b L) =
        (U₂.block C).refs.filter (fun b => σ₂.Votes U₂ b L) := by
      rw [h.refs C hC hCR]
      exact Finset.filter_congr fun b hb => h.votes_iff (href b hb).1 (href b hb).2 hL hLR
    rw [← hf, h.creatorsOf_eq (fun x hx => href x (Finset.mem_filter.mp hx).1)]

omit [Fintype Validator] in
theorem certsAt_inter [P₁.Mechanised] (p : Params) (hw : 2 ≤ p.waveLength) {L : BlockId}
    (hL : L ∈ V₁.ids) (hLR : R ≤ (U₁.block L).round) {r : ℕ} (hr : R ≤ r) :
    certsAt p σ₁ U₁ L r ∩ V₁.ids = certsAt p σ₂ U₂ L r ∩ V₂.ids :=
  h.layer_inter (by omega) fun x hx hxr => h.isCert_iff p hx (by omega) hL hLR

omit [Fintype Validator] in
theorem blamersAt_inter [S : Slots Validator] (p : Params) {k : ℕ} (hk : R ≤ S.slotRound k) :
    blamersAt p σ₁ U₁ k ∩ V₁.ids = blamersAt p σ₂ U₂ k ∩ V₂.ids :=
  h.layer_inter (by omega) fun x hx hxr => by rw [h.sel x hx (by omega) _ _ hk]

omit [Fintype Validator] in
theorem candidatesIn_eq [S : Slots Validator] {k : ℕ} (hk : R ≤ S.slotRound k) :
    candidatesIn U₁ V₁ k = candidatesIn U₂ V₂ k := by
  ext x
  simp only [mem_candidatesIn]
  constructor
  · rintro ⟨hx, hc, hr⟩
    have hR : R ≤ (U₁.block x).round := by omega
    exact ⟨h.mem x hx hR, by rw [h.creator x hx hR]; exact hc, by rw [h.round x hx hR]; exact hr⟩
  · rintro ⟨hx, hc, hr⟩
    obtain ⟨hx₁, hR⟩ := h.mem' x hx (by omega)
    exact ⟨hx₁, by rw [← h.creator x hx₁ hR]; exact hc, by rw [← h.round x hx₁ hR]; exact hr⟩

omit [Fintype Validator] in
/-- A candidate of the second view is one of the first, from `R` up. -/
theorem mem_of_candidatesIn [S : Slots Validator] {k : ℕ} (hk : R ≤ S.slotRound k) {L : BlockId}
    (hL : L ∈ candidatesIn U₂ V₂ k) : L ∈ V₁.ids ∧ R ≤ (U₁.block L).round := by
  rw [← h.candidatesIn_eq hk] at hL
  obtain ⟨hL, -, hr⟩ := mem_candidatesIn.mp hL
  exact ⟨hL, by omega⟩

omit [Fintype Validator] in
theorem tryDirect_eq [P₁.Mechanised] [S : Slots Validator] (p : Params) (hw : 2 ≤ p.waveLength)
    {k : ℕ} (hk : R ≤ S.slotRound k) :
    tryDirect p σ₁ U₁ V₁ k = tryDirect p σ₂ U₂ V₂ k := by
  have hskip := h.holdsAtLeast_iff (h.blamersAt_inter p hk) (fun x hx => by
    have := round_of_mem_layer (Finset.mem_inter.mp hx).1; omega) p.skipThreshold
  unfold tryDirect
  by_cases hs : HoldsAtLeast U₁ V₁ p.skipThreshold (blamersAt p σ₁ U₁ k)
  · rw [if_pos hs, if_pos (hskip.mp hs)]
  · rw [if_neg hs, if_neg (mt hskip.mpr hs), h.candidatesIn_eq hk]
    congr 2
    refine Finset.filter_congr fun L hL => ?_
    obtain ⟨hLV, hLR⟩ := h.mem_of_candidatesIn hk hL
    exact h.holdsAtLeast_iff (h.certsAt_inter p hw hLV hLR hk) (fun x hx => by
      have := round_of_mem_layer (Finset.mem_inter.mp hx).1; omega) p.commitThreshold

omit [Fintype Validator] in
/-- **Reaching a block from `R` up reads only references above `R`.** -/
theorem reaches_above [P₁.Mechanised] {x : BlockId} (hx : R ≤ (U₁.block x).round) :
    ∀ {A : BlockId}, A ∈ V₁.ids → ReachesFrom U₁.block A x → ReachesFrom U₂.block A x := by
  intro A hA hr
  induction hr using Relation.ReflTransGen.head_induction_on with
  | refl => exact ReachesFrom.refl
  | @head a c hstep hrest ih =>
    have hstep : c ∈ (U₁.block a).refs := hstep
    have hc := V₁.complete a hA c hstep
    have hac := U₁.causal.refs_round a (V₁.subset_ids hA) c hstep
    have hxc := U₁.causal.round_le_of_reaches (V₁.subset_ids hc) hrest
    refine ReachesFrom.of_mem_refs ?_ (ih hc)
    rw [h.refs a hA (by omega)]
    exact hstep

omit [Fintype Validator] in
theorem history_iff [P₁.Mechanised] [P₂.Mechanised] {A x : BlockId} (hA : A ∈ V₁.ids)
    (hAR : R ≤ (U₁.block A).round) (hxR : R ≤ (U₁.block x).round) (hx : x ∈ V₁.ids) :
    x ∈ history U₁ A ↔ x ∈ history U₂ A := by
  have hA₂ := h.mem A hA hAR
  rw [LeanDag.mem_history_iff (V₁.subset_ids hA), LeanDag.mem_history_iff (V₂.subset_ids hA₂)]
  exact ⟨h.reaches_above hxR hA, h.symm.reaches_above (by rw [h.round x hx hxR]; exact hxR) hA₂⟩

omit [Fintype Validator] in
theorem linkCerts_eq [P₁.Mechanised] [P₂.Mechanised] (p : Params) (hw : 2 ≤ p.waveLength)
    {A L : BlockId} (hA : A ∈ V₁.ids) (hAR : R ≤ (U₁.block A).round) (hL : L ∈ V₁.ids)
    (hLR : R ≤ (U₁.block L).round) {r : ℕ} (hr : R ≤ r) :
    linkCerts p σ₁ U₁ A L r = linkCerts p σ₂ U₂ A L r := by
  have hc := h.certsAt_inter p hw hL hLR hr
  ext x
  simp only [linkCerts, Finset.mem_filter]
  constructor
  · rintro ⟨hx, hxh⟩
    have hxV := history_subset_view hA hxh
    have hxR : R ≤ (U₁.block x).round := by have := round_of_mem_layer hx; omega
    have hm : x ∈ certsAt p σ₂ U₂ L r ∩ V₂.ids := hc ▸ Finset.mem_inter.mpr ⟨hx, hxV⟩
    exact ⟨(Finset.mem_inter.mp hm).1, (h.history_iff hA hAR hxR hxV).mp hxh⟩
  · rintro ⟨hx, hxh⟩
    have hxV₂ := history_subset_view (h.mem A hA hAR) hxh
    have hm : x ∈ certsAt p σ₁ U₁ L r ∩ V₁.ids := hc.symm ▸ Finset.mem_inter.mpr ⟨hx, hxV₂⟩
    obtain ⟨hx₁, hxV₁⟩ := Finset.mem_inter.mp hm
    have hxR : R ≤ (U₁.block x).round := by have := round_of_mem_layer hx₁; omega
    exact ⟨hx₁, (h.history_iff hA hAR hxR hxV₁).mpr hxh⟩

omit [Fintype Validator] in
theorem linkCount_eq [P₁.Mechanised] [P₂.Mechanised] (p : Params) (hw : 2 ≤ p.waveLength)
    {A L : BlockId} (hA : A ∈ V₁.ids) (hAR : R ≤ (U₁.block A).round) (hL : L ∈ V₁.ids)
    (hLR : R ≤ (U₁.block L).round) {r : ℕ} (hr : R ≤ r) :
    (creatorsOf U₁.block (linkCerts p σ₁ U₁ A L r)).card =
      (creatorsOf U₂.block (linkCerts p σ₂ U₂ A L r)).card := by
  rw [← h.linkCerts_eq p hw hA hAR hL hLR hr, h.creatorsOf_eq fun x hx => by
    obtain ⟨hx, hxh⟩ := Finset.mem_filter.mp hx
    exact ⟨history_subset_view hA hxh, by have := round_of_mem_layer hx; omega⟩]

end ViewsAbove

section Members

variable {P : Validity Validator BlockId Payload} {H : Finset Validator}
variable {U : BlockRecord Validator BlockId Payload P H} {V : U.View}

omit [Fintype Validator] in
theorem mem_of_leastOf {s : Finset BlockId} {x : BlockId} (hx : leastOf s = some x) : x ∈ s := by
  unfold leastOf at hx
  split at hx
  · rw [Option.some.injEq] at hx
    exact hx ▸ Finset.min'_mem _ _
  · exact absurd hx (by simp)

omit [Fintype Validator] in
/-- **What the indirect test commits is a candidate the view holds.** -/
theorem tryIndirect_mem [S : Slots Validator] (p : Params) (σ : VoteSel Validator BlockId Payload P H)
    (k : ℕ) : ∀ (later : List (ℕ × Option (Option BlockId))) {A : BlockId},
    tryIndirect p σ U V k later = some (some A) →
      A ∈ V.ids ∧ (U.block A).round = S.slotRound k
  | [], _, hA => by simp [tryIndirect] at hA
  | (j, s) :: rest, A, hA => by
    unfold tryIndirect at hA
    split at hA
    · split at hA
      · exact absurd hA (by simp)
      · exact tryIndirect_mem p σ k rest hA
      · rw [Option.some.injEq] at hA
        obtain ⟨h₁, -, h₂⟩ := mem_candidatesIn.mp (Finset.mem_filter.mp (mem_of_leastOf hA)).1
        exact ⟨h₁, h₂⟩
    · exact tryIndirect_mem p σ k rest hA

omit [Fintype Validator] in
/-- **What a slot's decision commits is a candidate the view holds.** -/
theorem decideSlot_mem [S : Slots Validator] (p : Params) (σ : VoteSel Validator BlockId Payload P H)
    (k : ℕ) (later : List (ℕ × Option (Option BlockId))) {A : BlockId}
    (hA : decideSlot p σ U V k later = some (some A)) :
    A ∈ V.ids ∧ (U.block A).round = S.slotRound k := by
  unfold decideSlot at hA
  split at hA
  · rename_i v hv
    rw [hA] at hv
    unfold tryDirect at hv
    split at hv
    · exact absurd hv (by simp)
    · obtain ⟨x, hx, hxe⟩ := Option.map_eq_some_iff.mp hv
      rw [Option.some.injEq] at hxe
      obtain ⟨h₁, -, h₂⟩ := mem_candidatesIn.mp (Finset.mem_filter.mp (mem_of_leastOf hx)).1
      exact hxe ▸ ⟨h₁, h₂⟩
  · exact tryIndirect_mem p σ k later hA

omit [Fintype Validator] in
theorem scan_mem [S : Slots Validator] (p : Params) (σ : VoteSel Validator BlockId Payload P H)
    (N : ℕ) : ∀ m, ∀ e ∈ scan p σ U V N m, ∀ A, e.2 = some (some A) →
      A ∈ V.ids ∧ (U.block A).round = S.slotRound e.1
  | 0, e, he, _, _ => by simp [scan] at he
  | m + 1, e, he, A, hA => by
    rcases List.mem_cons.mp he with rfl | he
    · exact decideSlot_mem p σ _ _ hA
    · exact scan_mem p σ N m e he A hA

omit [Fintype Validator] in
/-- The scan of `m` slots to `N` covers the slots from `N + 1 − m`. -/
theorem scan_fst [Slots Validator] (p : Params) (σ : VoteSel Validator BlockId Payload P H)
    (N : ℕ) : ∀ m, ∀ e ∈ scan p σ U V N m, N + 1 - m ≤ e.1
  | 0, e, he => by simp [scan] at he
  | m + 1, e, he => by
    rcases List.mem_cons.mp he with rfl | he
    · exact le_of_eq (by omega)
    · have := scan_fst p σ N m e he
      omega

end Members

namespace ViewsAbove

variable {R : ℕ} {U₁ : BlockRecord Validator BlockId Payload P₁ H₁}
variable {U₂ : BlockRecord Validator BlockId Payload P₂ H₂}
variable {σ₁ : VoteSel Validator BlockId Payload P₁ H₁}
variable {σ₂ : VoteSel Validator BlockId Payload P₂ H₂}
variable {V₁ : U₁.View} {V₂ : U₂.View} (h : ViewsAbove R σ₁ σ₂ V₁ V₂)
variable [P₁.Mechanised] [P₂.Mechanised] [S : Slots Validator] (p : Params) (hw : 2 ≤ p.waveLength)
include h hw

omit [Fintype Validator] in
theorem tryIndirect_eq {k : ℕ} (hk : R ≤ S.slotRound k) :
    ∀ (later : List (ℕ × Option (Option BlockId))),
    (∀ e ∈ later, ∀ A, e.2 = some (some A) → A ∈ V₁.ids ∧ R ≤ (U₁.block A).round) →
    tryIndirect p σ₁ U₁ V₁ k later = tryIndirect p σ₂ U₂ V₂ k later
  | [], _ => rfl
  | (j, s) :: rest, hl => by
    have ih := tryIndirect_eq hk rest fun e he => hl e (List.mem_cons_of_mem _ he)
    unfold tryIndirect
    split
    · split
      · rfl
      · exact ih
      · rename_i A
        obtain ⟨hA, hAR⟩ := hl _ List.mem_cons_self A rfl
        rw [h.candidatesIn_eq hk]
        congr 2
        refine Finset.filter_congr fun L hL => ?_
        obtain ⟨hLV, hLR⟩ := h.mem_of_candidatesIn hk hL
        rw [h.linkCount_eq p hw hA hAR hLV hLR hk]
    · exact ih

omit [Fintype Validator] in
theorem decideSlot_eq {k : ℕ} (hk : R ≤ S.slotRound k)
    (later : List (ℕ × Option (Option BlockId)))
    (hl : ∀ e ∈ later, ∀ A, e.2 = some (some A) → A ∈ V₁.ids ∧ R ≤ (U₁.block A).round) :
    decideSlot p σ₁ U₁ V₁ k later = decideSlot p σ₂ U₂ V₂ k later := by
  unfold decideSlot
  rw [h.tryDirect_eq p hw hk, h.tryIndirect_eq p hw hk later hl]

omit [Fintype Validator] in
theorem scan_eq (N : ℕ) :
    ∀ m, R ≤ S.slotRound (N + 1 - m) → scan p σ₁ U₁ V₁ N m = scan p σ₂ U₂ V₂ N m
  | 0, _ => rfl
  | m + 1, hR => by
    have hR' : R ≤ S.slotRound (N + 1 - m) := le_trans hR (S.mono (by omega))
    have hk : R ≤ S.slotRound (N - m) := by rwa [show N + 1 - (m + 1) = N - m by omega] at hR
    unfold scan
    rw [h.decideSlot_eq p hw hk _ fun e he A hA => by
        obtain ⟨h₁, h₂⟩ := scan_mem p σ₁ N m e he A hA
        have := S.mono (scan_fst p σ₁ N m e he)
        exact ⟨h₁, by omega⟩,
      scan_eq N m hR']

omit [Fintype Validator] in
/-- **The loop decides alike on two views agreeing from the round of its
first slot up.** -/
theorem tryDecide_eq {lo : ℕ} (N : ℕ) (hlo : R ≤ S.slotRound lo) :
    tryDecide p σ₁ U₁ V₁ lo N = tryDecide p σ₂ U₂ V₂ lo N := by
  unfold tryDecide
  rcases Nat.lt_or_ge (N + 1) lo with hl | hl
  · rw [Nat.sub_eq_zero_of_le hl.le]
    rfl
  · rw [h.scan_eq p hw N (N + 1 - lo) (by rwa [show N + 1 - (N + 1 - lo) = lo by omega])]

end ViewsAbove

omit [Fintype Validator] in
theorem historyUptoFrom_subset_view {P : Validity Validator BlockId Payload}
    {H : Finset Validator} {U : BlockRecord Validator BlockId Payload P H} (V : U.View) :
    ∀ (n : ℕ) {b : BlockId}, b ∈ V.ids → historyUptoFrom U.block n b ⊆ V.ids
  | 0, _, hb => by intro x hx; rw [historyUptoFrom_zero, Finset.mem_singleton] at hx; exact hx ▸ hb
  | n + 1, b, hb => by
    intro x hx
    rcases mem_historyUptoFrom_succ.mp hx with rfl | ⟨j, hj, hxj⟩
    · exact hb
    · exact historyUptoFrom_subset_view V n (V.complete b hb j hj) hxj

omit [Fintype Validator] in
/-- A block `n` steps below `b` lies at most `n` rounds below it. -/
theorem round_le_of_mem_historyUptoFrom {P : Validity Validator BlockId Payload} [P.Mechanised]
    {H : Finset Validator} (U : BlockRecord Validator BlockId Payload P H) :
    ∀ (n : ℕ) {b x : BlockId}, b ∈ U.ids → x ∈ historyUptoFrom U.block n b →
      (U.block b).round ≤ n + (U.block x).round
  | 0, _, _, _, hx => by
    rw [historyUptoFrom_zero, Finset.mem_singleton] at hx
    subst hx
    omega
  | n + 1, b, x, hb, hx => by
    rcases mem_historyUptoFrom_succ.mp hx with rfl | ⟨j, hj, hxj⟩
    · omega
    · have := U.causal.refs_round b hb j hj
      have := round_le_of_mem_historyUptoFrom U n (U.causal.complete b hb j hj) hxj
      omega

omit [Fintype Validator] in
/-- **The near search reads only references above `R`.** -/
theorem historyUptoFrom_above {P : Validity Validator BlockId Payload} [P.Mechanised]
    {H : Finset Validator} {U : BlockRecord Validator BlockId Payload P H} (V : U.View) {R : ℕ}
    {blk : BlockId → Block Validator BlockId Payload}
    (hrefs : ∀ i ∈ V.ids, R < (U.block i).round → (blk i).refs = (U.block i).refs) :
    ∀ (n : ℕ) {b : BlockId}, b ∈ V.ids → R + n ≤ (U.block b).round →
      historyUptoFrom U.block n b = historyUptoFrom blk n b
  | 0, _, _, _ => rfl
  | n + 1, b, hb, hn => by
    rw [historyUptoFrom_succ, historyUptoFrom_succ, hrefs b hb (by omega)]
    exact congrArg (insert b) (Finset.biUnion_congr rfl fun j hj =>
      historyUptoFrom_above V hrefs n (V.complete b hb j hj) (by
        have := U.causal.refs_round b (V.subset_ids hb) j hj; omega))

omit [Fintype Validator] in
/-- **At the bounded vote, views agreeing on their blocks from `R` up
agree from `R` up.** -/
theorem ViewsAbove.of_boundedSel [P₁.Mechanised] [P₂.Mechanised] {R : ℕ}
    {U₁ : BlockRecord Validator BlockId Payload P₁ H₁}
    {U₂ : BlockRecord Validator BlockId Payload P₂ H₂} {V₁ : U₁.View} {V₂ : U₂.View}
    (mem : ∀ i ∈ V₁.ids, R ≤ (U₁.block i).round → i ∈ V₂.ids)
    (mem' : ∀ i ∈ V₂.ids, R ≤ (U₂.block i).round → i ∈ V₁.ids ∧ R ≤ (U₁.block i).round)
    (round : ∀ i ∈ V₁.ids, R ≤ (U₁.block i).round → (U₂.block i).round = (U₁.block i).round)
    (creator : ∀ i ∈ V₁.ids, R ≤ (U₁.block i).round →
      (U₂.block i).creator = (U₁.block i).creator)
    (refs : ∀ i ∈ V₁.ids, R < (U₁.block i).round → (U₂.block i).refs = (U₁.block i).refs) :
    ViewsAbove R boundedSel boundedSel V₁ V₂ where
  mem := mem
  mem' := mem'
  round := round
  creator := creator
  refs := refs
  sel := fun b hb hbR a r hr => by
    change leastOf (slotNear U₁ b a r) = leastOf (slotNear U₂ b a r)
    congr 1
    unfold slotNear
    rw [round b hb hbR]
    split
    · rfl
    · rename_i hlt
      rw [← historyUptoFrom_above V₁ refs _ hb (by omega)]
      refine Finset.filter_congr fun x hx => ?_
      have hxV := historyUptoFrom_subset_view V₁ _ hb hx
      have hxR : R ≤ (U₁.block x).round := by
        have := round_le_of_mem_historyUptoFrom U₁ _ (V₁.subset_ids hb) hx
        omega
      rw [creator x hxV hxR, round x hxV hxR]

omit [Fintype Validator] in
/-- **A store agrees with every view holding its blocks**, read as the
store reads them. -/
theorem ViewsAbove.of_store {P : Validity Validator BlockId Payload} [P.Mechanised]
    {H : Finset Validator} {st : Store Validator BlockId Payload}
    {U : BlockRecord Validator BlockId Payload P H} {V : U.View}
    (hV : ∀ i, i ∈ V.ids ↔ i ∈ st.ids) (hU : ∀ i ∈ st.ids, U.block i = st.blk i) :
    ViewsAbove 0 boundedSel boundedSel st.view V :=
  ViewsAbove.of_boundedSel (fun i hi _ => (hV i).mpr hi)
    (fun i hi _ => ⟨(hV i).mp hi, Nat.zero_le _⟩)
    (fun i hi _ => by change (U.block i).round = (st.blk i).round; rw [hU i hi])
    (fun i hi _ => by change (U.block i).creator = (st.blk i).creator; rw [hU i hi])
    (fun i hi _ => by change (U.block i).refs = (st.blk i).refs; rw [hU i hi])

end Node

end LeanDag
