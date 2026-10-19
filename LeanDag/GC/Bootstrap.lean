import LeanDag.GC.Window
import LeanDag.GC.AttestedBase
import LeanDag.GC.ChopDecided
import LeanDag.Properties.Arcs.GC
import LeanDag.Properties.Arcs.Record
/-!
# Bootstrap: the joiner's view, assembled and bounded

`garbage.md` **G11**, **G6b**, **G7**, **G12**: the base is complete for
the whole obtainable window, not just the correct layer (G10 gave the
correct case); the fetch and the serving obligation are both bounded by
the G6 constant; and the view a joiner assembles from base plus window
is a bona-fide view of the truncation, so `decided_agree_chop` applies
to it directly.

Stated on any block record: the reliable validators are a set `T` inside
the honest set that holds the record's quorum `q`, with `n + f + 1 ≤ 2q`,
and `f` bounds the validators outside the honest set.
-/

namespace LeanDag

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {P : Validity Validator BlockId Payload} {honest : Finset Validator} [P.Mechanised]
variable {U : BlockRecord Validator BlockId Payload P honest}
variable {D : Delivery U} {v w : Validator} {y : BlockId} {G f q : ℕ} {T : Finset Validator}

/-- A retained store is closed under references: whatever cone brought `i`
also holds everything `i` references. -/
theorem mem_viewUpto_of_mem_refs {i j : BlockId} {n : ℕ}
    (hi : i ∈ viewUpto D v n) (hj : j ∈ (U.block i).refs) :
    j ∈ viewUpto D v n := by
  obtain ⟨k, hk, a, ha, hia⟩ := mem_viewUpto.mp hi
  have haids : a ∈ U.ids := (D.held_spec v k a (D.accepted_sub v k ha)).1
  exact mem_viewUpto.mpr ⟨k, hk, a, ha,
    (mem_history_iff haids).mpr
      (((mem_history_iff haids).mp hia).trans (Reaches.single hj))⟩

/-! ## G11 — window completeness of the base -/

/-- **G11.** Every round-`G` block a correct validator accepted into its
window by `m` — Byzantine-authored included — is in the base attested at
any `t ≥ m + 2`. Acceptance → the keeper's round-`(m+1)` block carries it
(`viewUpto_subset_history`) → the backbone hands that block to every
correct round-`t` cone → every correct author attests it, clearing `f + 1`
in **every** sample. Nothing obtainable is ever filtered out. -/
theorem accepted_mem_base [P.SelfParent] [P.Quorate q] {R m t : ℕ} (hT : q ≤ T.card)
    (hq : Fintype.card Validator + f + 1 ≤ 2 * q) (hTh : T ⊆ honest) (hs : SynchronisedOn U T R)
    (hv : v ∈ T) (hy : y ∈ viewUpto D v m)
    (hyr : (U.block y).round = G) (hcar : PopulatedOn U T (m + 1))
    (hpop : PopulatedOn U T t) (hR : R ≤ m + 1) (hmt : m + 2 ≤ t) :
    y ∈ Base U f t G := by
  obtain ⟨b, hb, hbc, hbr⟩ := hcar v hv
  have hyb : y ∈ history U b := viewUpto_subset_history (hTh hv) hb hbc hbr hy
  have hyids : y ∈ U.ids := history_subset_ids hb hyb
  refine mem_base.mpr ⟨⟨hyids, hyr⟩, ?_⟩
  have hsub : T ⊆ attesters U t y := by
    intro x hx
    obtain ⟨a, ha, hac, har⟩ := hpop x hx
    refine mem_attesters.mpr ⟨a, ha, har, ?_, hac⟩
    have hba : b ∈ history U a :=
      mem_history_of_correct hT (by omega) hs (t - m - 2) a ha b hb
        (by rw [hac]; exact hx) (by rw [hbc]; exact hv)
        (by omega) (by omega)
    exact history_subset_of_reaches ha ((mem_history_iff ha).mp hba) hyb
  have := Finset.card_le_card hsub
  have := le_card_of_quorum hT hq
  omega

/-! ## G6b — the fetch is bounded -/

/-- The base is inside every correct peer's retained store: each base
block sits in a correct attester's cone (G10 soundness), the attestation
is delivered and accepted post-`R`, and an accepted block's cone is
retained. -/
theorem base_subset_retained {R t : ℕ} (hf : honestᶜ.card ≤ f)
    (hED : EventuallyDeliversOn D T R) (hTh : T ⊆ honest) (hw : w ∈ T) (hR : R ≤ t) :
    Base U f t G ⊆ (viewUpto D w t).filter fun i => G ≤ (U.block i).round := by
  intro y hy
  obtain ⟨a, ha, har, hac, hya⟩ := exists_honest_attester_of_mem_base hf hy
  have hacc : a ∈ D.accepted w t :=
    D.accepts_correct w (hTh hw) t a (hED t hR w hw a ha har hac) hac
  obtain ⟨⟨-, hyr⟩, -⟩ := mem_base.mp hy
  exact Finset.mem_filter.mpr
    ⟨history_subset_viewUpto (le_refl t) hacc hya, by omega⟩

/-- The base alone is bounded by the G6 constant. -/
theorem card_base_le {κ Λ R t : ℕ} (hf : honestᶜ.card ≤ f) (hbyz : ByzBudget D κ)
    (hra : RefsAccepted D) (hED : EventuallyDeliversOn D T R) (hTh : T ⊆ honest)
    (hw : w ∈ T) (hR : R ≤ t) (hG : G ≤ t) (hΛ : t ≤ G + Λ) :
    (Base U f t G).card ≤
      honest.card * (Λ + 1) + (honest.card * f + Λ * (honest.card * (f * κ))) :=
  le_trans (Finset.card_le_card (base_subset_retained hf hED hTh hw hR))
    (card_retained_le hf hbyz hra (hTh hw) hG hΛ)

/-! ## G12 — the joiner's view -/

/-- What a joiner fetches: the attested base as its genesis layer, plus a
correct peer's window strictly above the cut, up to frontier `m`. The
round-`G` layer comes **only** from the base — that is the rebasing. -/
def joinIds (D : Delivery U) (w : Validator) (f m t G : ℕ) : Finset BlockId :=
  Base U f t G ∪ ((viewUpto D w m).filter fun i => G < (U.block i).round)

/-- **G6b.** The joiner's entire fetch is inside one correct peer's
retained store, hence bounded by the G6 constant: sync cost, not just
storage, is constant at lag `Λ`. -/
theorem card_joinIds_le {κ Λ R m t : ℕ} (hf : honestᶜ.card ≤ f) (hbyz : ByzBudget D κ)
    (hra : RefsAccepted D) (hED : EventuallyDeliversOn D T R) (hTh : T ⊆ honest)
    (hw : w ∈ T) (hR : R ≤ t) (hmt : m ≤ t) (hG : G ≤ t) (hΛ : t ≤ G + Λ) :
    (joinIds D w f m t G).card ≤
      honest.card * (Λ + 1) + (honest.card * f + Λ * (honest.card * (f * κ))) := by
  refine le_trans (Finset.card_le_card ?_) (card_retained_le hf hbyz hra (hTh hw) hG hΛ)
  refine Finset.union_subset (base_subset_retained hf hED hTh hw hR) ?_
  intro i hi
  obtain ⟨hiv, hiG⟩ := Finset.mem_filter.mp hi
  exact Finset.mem_filter.mpr ⟨viewUpto_mono hmt hiv, by omega⟩

/-- **G12, the assembly.** Base plus window is a bona-fide view of the
truncation. Closure is the whole content: a window reference above the cut
is in the window (stores are reference-closed), and a window reference *at*
the cut is a round-`G` block the peer accepted — which is exactly what G11
puts in the base. The base layer itself has no references to chase: `chop`
made it the genesis layer. -/
def joinView [P.SelfParent] [P.Quorate q] {R m t : ℕ} (hT : q ≤ T.card)
    (hq : Fintype.card Validator + f + 1 ≤ 2 * q) (hTh : T ⊆ honest) (hs : SynchronisedOn U T R)
    (hw : w ∈ T) (hcar : PopulatedOn U T (m + 1))
    (hpop : PopulatedOn U T t) (hR : R ≤ m + 1) (hmt : m + 2 ≤ t) : (chop U G).View where
  ids := joinIds D w f m t G
  subset_ids := by
    intro i hi
    rcases Finset.mem_union.mp hi with h | h
    · obtain ⟨⟨hids, hround⟩, -⟩ := mem_base.mp h
      exact mem_chop_ids.mpr ⟨hids, by omega⟩
    · obtain ⟨hiv, hround⟩ := Finset.mem_filter.mp h
      exact mem_chop_ids.mpr ⟨viewUpto_subset_ids hiv, by omega⟩
  complete := by
    intro i hi j hj
    rw [chop_block] at hj
    rcases Finset.mem_union.mp hi with h | h
    · obtain ⟨⟨hids, hround⟩, -⟩ := mem_base.mp h
      rw [chopBlk_refs_of_le (by omega)] at hj
      simp at hj
    · obtain ⟨hiv, hround⟩ := Finset.mem_filter.mp h
      have hiids : i ∈ U.ids := viewUpto_subset_ids hiv
      rw [chopBlk_refs_of_lt hround] at hj
      have hjv : j ∈ viewUpto D w m := mem_viewUpto_of_mem_refs hiv hj
      have hjr : (U.block j).round + 1 = (U.block i).round :=
        U.round_of_mem_refs hiids hj
      rcases Nat.lt_or_ge G (U.block j).round with hlt | hge
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hjv, hlt⟩)
      · exact Finset.mem_union_left _
          (accepted_mem_base hT hq hTh hs hw hjv (by omega) hcar hpop hR hmt)

theorem joinView_ids [P.SelfParent] [P.Quorate q] {R m t : ℕ} (hT : q ≤ T.card)
    (hq : Fintype.card Validator + f + 1 ≤ 2 * q) (hTh : T ⊆ honest) (hs : SynchronisedOn U T R)
    (hw : w ∈ T) (hcar : PopulatedOn U T (m + 1))
    (hpop : PopulatedOn U T t) (hR : R ≤ m + 1) (hmt : m + 2 ≤ t) :
    (joinView (D := D) (G := G) hT hq hTh hs hw hcar hpop hR hmt).ids =
      joinIds D w f m t G := rfl

/-- **G12 (bootstrap safety).** A joiner that assembles its view from the
attested base and a correct peer's window, and runs the rule on the
truncation, never conflicts with any full-history validator on any slot.
The composition *is* the proof: `joinView` is a view of `chop U G`, and
cross-cut agreement never asked whose view it was. Stated for any rule
with a carrier on the records of the invariant `I`, which survives the
cut — the round trip of the carrier is what reads the joiner's view,
built on the record, as the rule's. -/
theorem bootstrap_agree [P.SelfParent] [P.Quorate q] {R : Properties.DagRule Validator BlockId Payload}
    {I : BlockRecord Validator BlockId Payload P honest → Prop} [BlockRecord.Invariant.Chops I]
    (c : R.OnRecord P honest I) (hI : I U)
    (ha : Properties.Agree R) (hb : Properties.Banded R)
    [S : Slots Validator] {d : ℕ} (hd : G ≤ S.slotRound d)
    {R' m t : ℕ} (hT : q ≤ T.card) (hq : Fintype.card Validator + f + 1 ≤ 2 * q)
    (hTh : T ⊆ honest) (hs : SynchronisedOn U T R') (hw : w ∈ T)
    (hcar : PopulatedOn U T (m + 1)) (hpop : PopulatedOn U T t) (hR : R' ≤ m + 1)
    (hmt : m + 2 ≤ t)
    {V : R.View (c.ofRec U hI)} {k : ℕ} {jv fv : Option BlockId}
    (hJ : R.Decided (S.chop G d hd)
      (c.chop_ofRec U hI ▸
        c.ofView (h := BlockRecord.Invariant.Chops.chop G hI)
          (joinView (D := D) (G := G) hT hq hTh hs hw hcar hpop hR hmt)) k jv)
    (hV : R.Decided S V (d + k) fv) : jv = fv :=
  c.decided_agree_chop ha hb hd hJ hV

/-! ## G7 — the windowed relay obligation -/

/-- A correct author's cone is its own retained store plus the block
itself: `RefsAccepted` one step down, S10 the rest of the way. -/
theorem history_subset_insert_viewUpto (hra : RefsAccepted D)
    (hw : w ∈ honest) {b : BlockId} {n : ℕ}
    (hb : b ∈ U.ids) (hbc : (U.block b).creator = w)
    (hbr : (U.block b).round = n + 1) :
    history U b ⊆ insert b (viewUpto D w n) := by
  intro i hi
  rcases (mem_history_succ_iff hb).mp hi with rfl | ⟨j, hj, hij⟩
  · exact Finset.mem_insert_self _ _
  · exact Finset.mem_insert_of_mem
      (history_subset_viewUpto (le_refl n) (hra w hw n b hb hbc hbr hj) hij)

/-- **G7.** The windowed relay obligation: everything a correct author can
be asked to serve for its block — the block's truncated cone — is its own
retained store above the horizon, plus the block itself. Everything below
the cut is the base's job. -/
theorem history_chop_subset_retained (hra : RefsAccepted D)
    (hw : w ∈ honest) {b : BlockId} {n : ℕ}
    (hb : b ∈ U.ids) (hbc : (U.block b).creator = w)
    (hbr : (U.block b).round = n + 1) (hG : G ≤ n + 1) :
    history (chop U G) b ⊆
      insert b ((viewUpto D w n).filter fun i => G ≤ (U.block i).round) := by
  intro i hi
  rw [history_chop (mem_chop_ids.mpr ⟨hb, by omega⟩), Finset.mem_filter] at hi
  obtain ⟨hih, hiG⟩ := hi
  rcases Finset.mem_insert.mp
      (history_subset_insert_viewUpto hra hw hb hbc hbr hih) with rfl | h
  · exact Finset.mem_insert_self _ _
  · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨h, hiG⟩)

/-- **G7, priced.** Serving cost is the G6 constant plus one. -/
theorem card_serve_le {κ Λ n : ℕ} (hf : honestᶜ.card ≤ f) (hbyz : ByzBudget D κ)
    (hra : RefsAccepted D) (hw : w ∈ honest)
    {b : BlockId} (hb : b ∈ U.ids) (hbc : (U.block b).creator = w)
    (hbr : (U.block b).round = n + 1) (hG : G ≤ n) (hΛ : n ≤ G + Λ) :
    (history (chop U G) b).card ≤
      (honest.card * (Λ + 1) + (honest.card * f + Λ * (honest.card * (f * κ)))) + 1 := by
  refine le_trans (Finset.card_le_card
    (history_chop_subset_retained hra hw hb hbc hbr (by omega))) ?_
  refine le_trans (Finset.card_insert_le _ _) ?_
  have := card_retained_le (G := G) hf hbyz hra hw hG hΛ
  omega

end LeanDag
