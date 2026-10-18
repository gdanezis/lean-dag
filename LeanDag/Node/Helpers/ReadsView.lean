import LeanDag.Scheme.Helpers.TryDecide
import LeanDag.Node.Vote
/-!
# The commit loop reads only the view

Two records, at any validity predicates and honest sets, with views that
hold the same identifiers, denote the same blocks there, and whose vote
rules select alike at every block of the view (`ViewsAlike`), give the
same decisions: `tryDecide` is equal on the two. Every set the loop
counts is read inside the view: the blamers and certificates of a round
through `heldAuthors`, which intersects with the view; a certificate's
votes among its references; and a link's certificates inside the
anchor's history, which the view holds.

`ViewsAlike.of_boundedSel`: at the bounded vote, the third condition
follows from the first two, since the vote reads only the voter's
history.
-/

namespace LeanDag

namespace Node

open Scheme

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [LinearOrder BlockId] {Payload : Type}
variable {P₁ P₂ : Validity Validator BlockId Payload} {H₁ H₂ : Finset Validator}

/-- **Two views read alike**: the same identifiers, the same blocks there,
and vote rules selecting alike at each of them. -/
structure ViewsAlike {U₁ : BlockRecord Validator BlockId Payload P₁ H₁}
    {U₂ : BlockRecord Validator BlockId Payload P₂ H₂}
    (σ₁ : VoteSel Validator BlockId Payload P₁ H₁) (σ₂ : VoteSel Validator BlockId Payload P₂ H₂)
    (V₁ : U₁.View) (V₂ : U₂.View) : Prop where
  ids : V₁.ids = V₂.ids
  block : ∀ i ∈ V₁.ids, U₁.block i = U₂.block i
  sel : ∀ b ∈ V₁.ids, ∀ a r, σ₁.sel U₁ b a r = σ₂.sel U₂ b a r

namespace ViewsAlike

variable {U₁ : BlockRecord Validator BlockId Payload P₁ H₁}
variable {U₂ : BlockRecord Validator BlockId Payload P₂ H₂}
variable {σ₁ : VoteSel Validator BlockId Payload P₁ H₁}
variable {σ₂ : VoteSel Validator BlockId Payload P₂ H₂}
variable {V₁ : U₁.View} {V₂ : U₂.View} (h : ViewsAlike σ₁ σ₂ V₁ V₂)
include h

omit [Fintype Validator] in
theorem creatorsOf_eq {s : Finset BlockId} (hs : s ⊆ V₁.ids) :
    creatorsOf U₁.block s = creatorsOf U₂.block s :=
  Finset.image_congr fun x hx => by rw [h.block x (hs hx)]

omit [Fintype Validator] in
theorem heldAuthors_eq {s₁ s₂ : Finset BlockId} (hs : s₁ ∩ V₁.ids = s₂ ∩ V₂.ids) :
    heldAuthors U₁ V₁ s₁ = heldAuthors U₂ V₂ s₂ := by
  unfold heldAuthors
  rw [hs]
  exact h.creatorsOf_eq (by rw [← h.ids]; exact Finset.inter_subset_right)

omit [Fintype Validator] in
theorem holdsAtLeast_iff {s₁ s₂ : Finset BlockId} (hs : s₁ ∩ V₁.ids = s₂ ∩ V₂.ids) (t : ℕ) :
    HoldsAtLeast U₁ V₁ t s₁ ↔ HoldsAtLeast U₂ V₂ t s₂ := by
  unfold HoldsAtLeast
  rw [h.heldAuthors_eq hs]

omit [Fintype Validator] [DecidableEq Validator] in
theorem votes_iff {b L : BlockId} (hb : b ∈ V₁.ids) (hL : L ∈ V₁.ids) :
    σ₁.Votes U₁ b L ↔ σ₂.Votes U₂ b L := by
  unfold VoteSel.Votes
  rw [h.block L hL, h.sel b hb]

omit [Fintype Validator] in
theorem isCert_iff (p : Params) {C L : BlockId} (hC : C ∈ V₁.ids) (hL : L ∈ V₁.ids) :
    IsCert p σ₁ U₁ C L ↔ IsCert p σ₂ U₂ C L := by
  unfold IsCert
  split
  · exact h.votes_iff hC hL
  · unfold CarriesVotes carriedVotes
    have href : (U₁.block C).refs ⊆ V₁.ids := fun j hj => V₁.complete C hC j hj
    have hf : (U₁.block C).refs.filter (fun b => σ₁.Votes U₁ b L) =
        (U₂.block C).refs.filter (fun b => σ₂.Votes U₂ b L) := by
      rw [← h.block C hC]
      exact Finset.filter_congr fun b hb => h.votes_iff (href hb) hL
    rw [← hf, h.creatorsOf_eq (fun x hx => href (Finset.mem_filter.mp hx).1)]

omit [Fintype Validator] in
theorem certsAt_inter (p : Params) {L : BlockId} (hL : L ∈ V₁.ids) (r : ℕ) :
    certsAt p σ₁ U₁ L r ∩ V₁.ids = certsAt p σ₂ U₂ L r ∩ V₂.ids := by
  ext x
  simp only [certsAt, blocksAt, Finset.mem_inter, Finset.mem_filter, ← h.ids]
  constructor
  · rintro ⟨⟨⟨-, hr⟩, hc⟩, hx⟩
    exact ⟨⟨⟨V₂.subset_ids (h.ids ▸ hx), h.block x hx ▸ hr⟩, (h.isCert_iff p hx hL).mp hc⟩, hx⟩
  · rintro ⟨⟨⟨-, hr⟩, hc⟩, hx⟩
    exact ⟨⟨⟨V₁.subset_ids hx, (h.block x hx).symm ▸ hr⟩, (h.isCert_iff p hx hL).mpr hc⟩, hx⟩

omit [Fintype Validator] [DecidableEq Validator] in
theorem blamersAt_inter [Slots Validator] (p : Params) (k : ℕ) :
    blamersAt p σ₁ U₁ k ∩ V₁.ids = blamersAt p σ₂ U₂ k ∩ V₂.ids := by
  ext x
  simp only [blamersAt, blocksAt, Finset.mem_inter, Finset.mem_filter, ← h.ids]
  constructor
  · rintro ⟨⟨⟨-, hr⟩, hc⟩, hx⟩
    exact ⟨⟨⟨V₂.subset_ids (h.ids ▸ hx), h.block x hx ▸ hr⟩, h.sel x hx _ _ ▸ hc⟩, hx⟩
  · rintro ⟨⟨⟨-, hr⟩, hc⟩, hx⟩
    exact ⟨⟨⟨V₁.subset_ids hx, (h.block x hx).symm ▸ hr⟩, (h.sel x hx _ _).symm ▸ hc⟩, hx⟩

omit [Fintype Validator] in
theorem candidatesIn_eq [Slots Validator] (k : ℕ) :
    candidatesIn U₁ V₁ k = candidatesIn U₂ V₂ k := by
  unfold candidatesIn
  rw [← h.ids]
  exact Finset.filter_congr fun x hx => by rw [h.block x hx]

omit [Fintype Validator] in
theorem tryDirect_eq [Slots Validator] (p : Params) (k : ℕ) :
    tryDirect p σ₁ U₁ V₁ k = tryDirect p σ₂ U₂ V₂ k := by
  have hskip := h.holdsAtLeast_iff (h.blamersAt_inter p k) p.skipThreshold
  unfold tryDirect
  by_cases hs : HoldsAtLeast U₁ V₁ p.skipThreshold (blamersAt p σ₁ U₁ k)
  · rw [if_pos hs, if_pos (hskip.mp hs)]
  · rw [if_neg hs, if_neg (mt hskip.mpr hs), h.candidatesIn_eq k]
    congr 2
    refine Finset.filter_congr fun L hL => ?_
    have hLV : L ∈ V₁.ids := h.ids ▸ (mem_candidatesIn.mp hL).1
    exact h.holdsAtLeast_iff (h.certsAt_inter p hLV _) p.commitThreshold

omit [Fintype Validator] in
theorem linkCerts_eq (p : Params) {A L : BlockId} (hA : A ∈ V₁.ids) (hL : L ∈ V₁.ids) (r : ℕ) :
    linkCerts p σ₁ U₁ A L r = linkCerts p σ₂ U₂ A L r := by
  have hhist : history U₁ A = history U₂ A :=
    historyFrom_congr V₁.complete h.block hA
  have hsub : history U₁ A ⊆ V₁.ids := history_subset_view hA
  have hc := h.certsAt_inter p hL r
  ext x
  simp only [linkCerts, Finset.mem_filter, ← hhist]
  constructor
  · rintro ⟨hx, hxh⟩
    have : x ∈ certsAt p σ₂ U₂ L r ∩ V₂.ids := hc ▸ Finset.mem_inter.mpr ⟨hx, hsub hxh⟩
    exact ⟨(Finset.mem_inter.mp this).1, hxh⟩
  · rintro ⟨hx, hxh⟩
    have : x ∈ certsAt p σ₁ U₁ L r ∩ V₁.ids :=
      hc.symm ▸ Finset.mem_inter.mpr ⟨hx, h.ids ▸ hsub hxh⟩
    exact ⟨(Finset.mem_inter.mp this).1, hxh⟩

omit [Fintype Validator] in
theorem linkCount_eq (p : Params) {A L : BlockId} (hA : A ∈ V₁.ids) (hL : L ∈ V₁.ids) (r : ℕ) :
    (creatorsOf U₁.block (linkCerts p σ₁ U₁ A L r)).card =
      (creatorsOf U₂.block (linkCerts p σ₂ U₂ A L r)).card := by
  rw [← h.linkCerts_eq p hA hL r,
    h.creatorsOf_eq (fun x hx => history_subset_view hA (Finset.mem_filter.mp hx).2)]

end ViewsAlike

section Members

variable {P : Validity Validator BlockId Payload} {H : Finset Validator}
variable {U : BlockRecord Validator BlockId Payload P H} {V : U.View}

omit [Fintype Validator] [DecidableEq Validator] in
theorem mem_of_leastOf {s : Finset BlockId} {x : BlockId} (hx : leastOf s = some x) : x ∈ s := by
  unfold leastOf at hx
  split at hx
  · rw [Option.some.injEq] at hx
    exact hx ▸ Finset.min'_mem _ _
  · exact absurd hx (by simp)

omit [Fintype Validator] in
/-- **What the indirect test commits lies in the view.** -/
theorem tryIndirect_mem [Slots Validator] (p : Params) (σ : VoteSel Validator BlockId Payload P H)
    (k : ℕ) : ∀ (later : List (ℕ × Option (Option BlockId))) {A : BlockId},
    tryIndirect p σ U V k later = some (some A) → A ∈ V.ids
  | [], _, hA => by simp [tryIndirect] at hA
  | (j, s) :: rest, A, hA => by
    unfold tryIndirect at hA
    split at hA
    · split at hA
      · exact absurd hA (by simp)
      · exact tryIndirect_mem p σ k rest hA
      · rw [Option.some.injEq] at hA
        exact (mem_candidatesIn.mp (Finset.mem_filter.mp (mem_of_leastOf hA)).1).1
    · exact tryIndirect_mem p σ k rest hA

omit [Fintype Validator] in
/-- **What a slot's decision commits lies in the view.** -/
theorem decideSlot_mem [Slots Validator] (p : Params) (σ : VoteSel Validator BlockId Payload P H)
    (k : ℕ) (later : List (ℕ × Option (Option BlockId))) {A : BlockId}
    (hA : decideSlot p σ U V k later = some (some A)) : A ∈ V.ids := by
  unfold decideSlot at hA
  split at hA
  · rename_i v hv
    rw [hA] at hv
    unfold tryDirect at hv
    split at hv
    · exact absurd hv (by simp)
    · obtain ⟨x, hx, hxe⟩ := Option.map_eq_some_iff.mp hv
      rw [Option.some.injEq] at hxe
      exact hxe ▸ (mem_candidatesIn.mp (Finset.mem_filter.mp (mem_of_leastOf hx)).1).1
  · exact tryIndirect_mem p σ k later hA

omit [Fintype Validator] in
theorem scan_mem [Slots Validator] (p : Params) (σ : VoteSel Validator BlockId Payload P H)
    (N : ℕ) : ∀ m, ∀ e ∈ scan p σ U V N m, ∀ A, e.2 = some (some A) → A ∈ V.ids
  | 0, e, he, _, _ => by simp [scan] at he
  | m + 1, e, he, A, hA => by
    rcases List.mem_cons.mp he with rfl | he
    · exact decideSlot_mem p σ _ _ hA
    · exact scan_mem p σ N m e he A hA

end Members

namespace ViewsAlike

variable {U₁ : BlockRecord Validator BlockId Payload P₁ H₁}
variable {U₂ : BlockRecord Validator BlockId Payload P₂ H₂}
variable {σ₁ : VoteSel Validator BlockId Payload P₁ H₁}
variable {σ₂ : VoteSel Validator BlockId Payload P₂ H₂}
variable {V₁ : U₁.View} {V₂ : U₂.View} (h : ViewsAlike σ₁ σ₂ V₁ V₂)
include h

omit [Fintype Validator] in
theorem tryIndirect_eq [Slots Validator] (p : Params) (k : ℕ) :
    ∀ (later : List (ℕ × Option (Option BlockId))),
    (∀ e ∈ later, ∀ A, e.2 = some (some A) → A ∈ V₁.ids) →
    tryIndirect p σ₁ U₁ V₁ k later = tryIndirect p σ₂ U₂ V₂ k later
  | [], _ => rfl
  | (j, s) :: rest, hl => by
    have ih := tryIndirect_eq p k rest fun e he => hl e (List.mem_cons_of_mem _ he)
    unfold tryIndirect
    split
    · split
      · rfl
      · exact ih
      · rename_i A
        have hA : A ∈ V₁.ids := hl _ List.mem_cons_self A rfl
        rw [h.candidatesIn_eq k]
        congr 2
        refine Finset.filter_congr fun L hL => ?_
        have hLV : L ∈ V₁.ids := h.ids ▸ (mem_candidatesIn.mp hL).1
        rw [h.linkCount_eq p hA hLV]
    · exact ih

omit [Fintype Validator] in
theorem decideSlot_eq [Slots Validator] (p : Params) (k : ℕ)
    (later : List (ℕ × Option (Option BlockId)))
    (hl : ∀ e ∈ later, ∀ A, e.2 = some (some A) → A ∈ V₁.ids) :
    decideSlot p σ₁ U₁ V₁ k later = decideSlot p σ₂ U₂ V₂ k later := by
  unfold decideSlot
  rw [h.tryDirect_eq p k, h.tryIndirect_eq p k later hl]

omit [Fintype Validator] in
theorem scan_eq [Slots Validator] (p : Params) (N : ℕ) :
    ∀ m, scan p σ₁ U₁ V₁ N m = scan p σ₂ U₂ V₂ N m
  | 0 => rfl
  | m + 1 => by
    unfold scan
    rw [h.decideSlot_eq p _ _ (scan_mem p σ₁ N m), scan_eq p N m]

omit [Fintype Validator] in
/-- **The loop decides alike on two views that read alike.** -/
theorem tryDecide_eq [Slots Validator] (p : Params) (lo N : ℕ) :
    tryDecide p σ₁ U₁ V₁ lo N = tryDecide p σ₂ U₂ V₂ lo N := by
  unfold tryDecide
  rw [h.scan_eq p N]

end ViewsAlike

omit [Fintype Validator] [DecidableEq Validator] in
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
/-- **At the bounded vote, views with the same blocks read alike.** -/
theorem ViewsAlike.of_boundedSel [P₁.Mechanised] [P₂.Mechanised]
    {U₁ : BlockRecord Validator BlockId Payload P₁ H₁}
    {U₂ : BlockRecord Validator BlockId Payload P₂ H₂} {V₁ : U₁.View} {V₂ : U₂.View}
    (hids : V₁.ids = V₂.ids) (hblk : ∀ i ∈ V₁.ids, U₁.block i = U₂.block i) :
    ViewsAlike boundedSel boundedSel V₁ V₂ where
  ids := hids
  block := hblk
  sel := fun b hb a r => by
    change leastOf (slotNear U₁ b a r) = leastOf (slotNear U₂ b a r)
    congr 1
    unfold slotNear
    rw [← hblk b hb]
    split
    · rfl
    · rw [← historyUptoFrom_congr V₁.complete hblk _ b hb]
      exact Finset.filter_congr fun x hx => by
        rw [hblk x (historyUptoFrom_subset_view V₁ _ hb hx)]

end Node

end LeanDag
