import LeanDag.Common.CausalHistory
import LeanDag.Common.Support
/-!
# Causal history as a `Finset`

`Reaches` is a `Prop`, which the DoS budgets cannot count. `history U b`
is the same relation as data, walked with the fuel `round + 1` — enough
by T2, since a reference drops the round by one. `Causality.lean` has
the walk itself, over raw block data; this file reads it at
`U.block`/`U.ids`.
-/

namespace LeanDag

variable {Validator : Type*} [DecidableEq Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {P : Validity Validator BlockId Payload} {honest : Finset Validator}
variable {U : BlockRecord Validator BlockId Payload P honest}

/-- Everything reachable from `b` in at most `n` reference steps.
Structural in the fuel `n`, so computable with no decidability
hypothesis. -/
def historyUpto (U : BlockRecord Validator BlockId Payload P honest) :
    ℕ → BlockId → Finset BlockId :=
  historyUptoFrom U.block

@[simp]
theorem historyUpto_zero (b : BlockId) : historyUpto U 0 b = {b} := rfl

theorem historyUpto_succ (n : ℕ) (b : BlockId) :
    historyUpto U (n + 1) b = insert b ((U.block b).refs.biUnion (historyUpto U n)) := rfl

theorem mem_historyUpto_succ {n : ℕ} {b i : BlockId} :
    i ∈ historyUpto U (n + 1) b ↔
      i = b ∨ ∃ j ∈ (U.block b).refs, i ∈ historyUpto U n j :=
  mem_historyUptoFrom_succ

theorem mem_historyUpto_self {n : ℕ} {b : BlockId} : b ∈ historyUpto U n b :=
  mem_historyUptoFrom_self

/-- More fuel never loses anything. Needed because `mem_history_iff` fixes the
fuel at `round + 1` while the recursion hands out whatever is left. -/
theorem historyUpto_mono {m n : ℕ} (h : m ≤ n) (b : BlockId) :
    historyUpto U m b ⊆ historyUpto U n b :=
  historyUptoFrom_mono h b

/-- **Soundness.** Anything the fuelled search finds really is reachable. No
hypothesis on `b`: even off the universe, `historyUpto` only ever walks
references. -/
theorem reaches_of_mem_historyUpto {n : ℕ} {b i : BlockId}
    (h : i ∈ historyUpto U n b) : Reaches U b i :=
  reaches_of_mem_historyUptoFrom h

variable [P.Mechanised]

/-- **Completeness**, with the fuel accounted for: a path from `b` drops
the round by one per step (T2), so `round b` steps exhaust it, and one
more is harmless by `historyUpto_mono`. -/
theorem mem_historyUpto_of_reaches {n : ℕ} {b i : BlockId} (hb : b ∈ U.ids)
    (hn : (U.block b).round ≤ n) (h : Reaches U b i) : i ∈ historyUpto U n b :=
  U.causal.mem_historyUpto_of_reaches hb hn h

omit [P.Mechanised] in
/-- The causal history of `b`, as a `Finset`. -/
def history (U : BlockRecord Validator BlockId Payload P honest) (b : BlockId) : Finset BlockId :=
  historyFrom U.block b

/-- **The representation is faithful** (`dos-equivocation-and-growth.md` §7 S6). For a block of the universe,
membership of `history` and reachability are the same thing. -/
theorem mem_history_iff {b i : BlockId} (hb : b ∈ U.ids) :
    i ∈ history U b ↔ Reaches U b i :=
  U.causal.mem_history_iff hb

omit [P.Mechanised] in
/-- A block lies in its own causal history. -/
@[simp]
theorem mem_history_self {b : BlockId} : b ∈ history U b := mem_historyFrom_self

/-- Histories stay inside the universe. -/
theorem history_subset_ids {b : BlockId} (hb : b ∈ U.ids) : history U b ⊆ U.ids :=
  U.causal.history_subset_ids hb

/-- **The causal history of a block, as a view.** -/
def BlockRecord.historyView (U : BlockRecord Validator BlockId Payload P honest) (A : BlockId)
    (hA : A ∈ U.ids) : U.View where
  ids := history U A
  subset_ids := history_subset_ids hA
  complete := fun _ hi _ hj =>
    (mem_history_iff hA).mpr (((mem_history_iff hA).mp hi).trans (ReachesFrom.single hj))

/-- Histories nest along reachability — the `Finset` form of transitivity, and
what makes D12 one line. -/
theorem history_subset_of_reaches {c b : BlockId} (hc : c ∈ U.ids) (h : Reaches U c b) :
    history U b ⊆ history U c :=
  U.causal.history_subset_of_reaches hc h

/-- The one-step unfolding: a history is its block, plus the histories of
its references. Needs a proof, not `rfl`, because the fuel splits
unevenly between the block and each reference. -/
theorem mem_history_succ_iff {b : BlockId} (hb : b ∈ U.ids) {i : BlockId} :
    i ∈ history U b ↔ i = b ∨ ∃ j ∈ (U.block b).refs, i ∈ history U j :=
  U.causal.mem_history_succ_iff hb

/-- Causal history runs downward (T2), in the `Finset` form. -/
theorem round_le_of_mem_history {b i : BlockId} (hb : b ∈ U.ids) (hi : i ∈ history U b) :
    (U.block i).round ≤ (U.block b).round :=
  U.causal.round_le_of_mem_history hb hi

/-- Nothing in a block's history sits at the block's own round except the block
itself: a reference step drops the round strictly. -/
theorem eq_of_mem_history_of_round_eq {b i : BlockId} (hb : b ∈ U.ids)
    (hi : i ∈ history U b) (hround : (U.block i).round = (U.block b).round) : i = b :=
  U.causal.eq_of_mem_history_of_round_eq hb hi hround

/-- **The layer one below is exactly the reference set.** Anything in `b`'s
history at round `round b - 1` is a direct reference of `b`. -/
theorem mem_refs_of_mem_history_of_round_succ {b i : BlockId} (hb : b ∈ U.ids)
    (hi : i ∈ history U b) (hround : (U.block i).round + 1 = (U.block b).round) :
    i ∈ (U.block b).refs :=
  U.causal.mem_refs_of_mem_history_of_round_succ hb hi hround

/-- A block's references lie in its history, one step down. -/
theorem mem_history_of_mem_refs {b j : BlockId} (hb : b ∈ U.ids) (hj : j ∈ (U.block b).refs) :
    j ∈ history U b :=
  U.causal.mem_history_of_mem_refs hb hj

/-- A block of `b`'s history other than `b` is referenced by a block of that
history. -/
theorem exists_mem_refs_of_mem_history {b i : BlockId} (hb : b ∈ U.ids)
    (hi : i ∈ history U b) (hne : i ≠ b) : ∃ j ∈ history U b, i ∈ (U.block j).refs := by
  rcases Relation.ReflTransGen.cases_tail ((mem_history_iff hb).mp hi) with h | ⟨j, hj, hji⟩
  · exact absurd h hne
  · exact ⟨j, (mem_history_iff hb).mpr hj, hji⟩

/-- **Every round between is crossed.** For `i` in `b`'s history and a round
`k` between theirs, `b`'s history holds a block of round `k` whose history
holds `i`. -/
theorem exists_mem_history_of_round_between {b i : BlockId} (hb : b ∈ U.ids)
    (hi : i ∈ history U b) {k : ℕ} (hik : (U.block i).round ≤ k)
    (hkb : k ≤ (U.block b).round) :
    ∃ j ∈ history U b, (U.block j).round = k ∧ i ∈ history U j := by
  obtain ⟨d, hd⟩ : ∃ d, (U.block b).round = k + d := ⟨(U.block b).round - k, by omega⟩
  induction d generalizing b with
  | zero => exact ⟨b, mem_history_self, by omega, hi⟩
  | succ d ih =>
      have hne : i ≠ b := by
        rintro rfl
        omega
      rcases Relation.ReflTransGen.cases_head ((mem_history_iff hb).mp hi) with h | ⟨c, hc, hci⟩
      · exact absurd h.symm hne
      · have hc_ids : c ∈ U.ids := U.complete b hb c hc
        have hcr := U.round_of_mem_refs hb hc
        obtain ⟨j, hj, hjr, hij⟩ :=
          ih hc_ids ((mem_history_iff hc_ids).mpr hci) (by omega) (by omega)
        exact ⟨j, history_subset_of_reaches hb (Reaches.single hc) hj, hjr, hij⟩

/-! ## A block of a set in the anchor's cone

The indirect rules ask whether a certificate or vote lies in the
anchor's cone: reachability, with the `history` reading for
decidability on data. -/

section Linked

variable {P : Validity Validator BlockId Payload} {honest : Finset Validator}
variable {U : BlockRecord Validator BlockId Payload P honest}

/-- Some block of `s` lies in `A`'s causal history. -/
abbrev LinkedVia (U : BlockRecord Validator BlockId Payload P honest) (A : BlockId)
    (s : Finset BlockId) : Prop :=
  ∃ C ∈ s, Reaches U A C

namespace LinkedVia

variable {A B : BlockId} {s s' : Finset BlockId}

theorem of_mem {C : BlockId} (hC : C ∈ s) (h : Reaches U A C) : LinkedVia U A s := ⟨C, hC, h⟩

theorem nonempty (h : LinkedVia U A s) : s.Nonempty := by
  obtain ⟨C, hC, -⟩ := h; exact ⟨C, hC⟩

theorem mono (hs : s ⊆ s') (h : LinkedVia U A s) : LinkedVia U A s' := by
  obtain ⟨C, hC, hre⟩ := h; exact ⟨C, hs hC, hre⟩

/-- Cones nest: whatever an anchor links, everything above the anchor links. -/
theorem of_reaches (h : Reaches U B A) (hl : LinkedVia U A s) : LinkedVia U B s := by
  obtain ⟨C, hC, hre⟩ := hl; exact ⟨C, hC, h.trans hre⟩

end LinkedVia

variable [P.Mechanised]

/-- The `history` reading: decidable on data. -/
theorem linkedVia_iff_history {A : BlockId} {s : Finset BlockId} (hA : A ∈ U.ids) :
    LinkedVia U A s ↔ (s ∩ history U A).Nonempty := by
  constructor
  · rintro ⟨C, hC, hre⟩
    exact ⟨C, Finset.mem_inter.mpr ⟨hC, (mem_history_iff hA).mpr hre⟩⟩
  · rintro ⟨C, hC⟩
    obtain ⟨h1, h2⟩ := Finset.mem_inter.mp hC
    exact ⟨C, h1, (mem_history_iff hA).mp h2⟩

/-! ## Votes in an anchor's cone

The votes for a candidate in the anchor's cone, by distinct authors — the
count equivocation cannot inflate. -/

/-- The round-`n` votes for `L` in `A`'s cone. -/
def coneVotesFor (U : BlockRecord Validator BlockId Payload P honest) (A L : BlockId) (n : ℕ) :
    Finset BlockId :=
  (votesFor U L n).filter (fun q => q ∈ history U A)

/-- The authors of the round-`n` votes for `L` in `A`'s cone. -/
def coneSupporters (U : BlockRecord Validator BlockId Payload P honest) (A L : BlockId)
    (n : ℕ) : Finset Validator :=
  creatorsOf U.block (coneVotesFor U A L n)

theorem mem_coneSupporters {A L : BlockId} {n : ℕ} {v : Validator} :
    v ∈ coneSupporters U A L n ↔
      ∃ q ∈ U.ids, (U.block q).round = n ∧ L ∈ (U.block q).refs ∧
        q ∈ history U A ∧ (U.block q).creator = v := by
  simp only [coneSupporters, coneVotesFor, mem_creatorsOf, Finset.mem_filter, mem_votesFor,
    and_assoc]

/-- In-cone supporters are supporters. -/
theorem coneSupporters_subset_supporters {A L : BlockId} {n : ℕ} :
    coneSupporters U A L n ⊆ supporters U L n :=
  Finset.image_subset_image (Finset.filter_subset _ _)

/-- Cones nest, so in-cone support does. -/
theorem coneSupporters_subset_of_reaches {A B L : BlockId} {n : ℕ} (hB : B ∈ U.ids)
    (h : Reaches U B A) : coneSupporters U A L n ⊆ coneSupporters U B L n := by
  refine Finset.image_subset_image fun q hq => ?_
  rw [coneVotesFor, Finset.mem_filter] at hq ⊢
  exact ⟨hq.1, history_subset_of_reaches hB h hq.2⟩

end Linked

/-! ## Visibility

A block above a round sees, through its references, most of that round's
authors: all but those its quorum misses and those outside a
non-equivocating set. -/

section Visibility

variable [Fintype Validator] {q : ℕ} [P.Quorate q]
variable {Hon : Finset Validator} {f : ℕ}

/-- **Visibility.** A block `d + 1` rounds above a set `X` of round-`D`
blocks holds in its history the blocks of `X` of at least
`|authors X| + q − n − f` authors. -/
theorem card_inHistory_ge (hne : U.NoEquivOn Hon) (hHon : Honᶜ.card ≤ f)
    {X : Finset BlockId} {D : ℕ} (hX : ∀ b ∈ X, b ∈ U.ids ∧ (U.block b).round = D) :
    ∀ d A, A ∈ U.ids → (U.block A).round = D + 1 + d →
      (creatorsOf U.block X).card + q ≤
        Fintype.card Validator + f +
          (creatorsOf U.block (X.filter (fun C => C ∈ history U A))).card := by
  intro d
  induction d with
  | zero =>
    intro A hA hround
    have hq : q ≤ (creatorsOf U.block (U.block A).refs).card := U.creators_quorum hA (by omega)
    set R := creatorsOf U.block (U.block A).refs
    set CX := creatorsOf U.block X
    have hsub : (R ∩ CX) ∩ Hon ⊆ creatorsOf U.block (X.filter (fun C => C ∈ history U A)) := by
      intro v hv
      obtain ⟨hvRC, hvH⟩ := Finset.mem_inter.mp hv
      obtain ⟨hvR, hvC⟩ := Finset.mem_inter.mp hvRC
      obtain ⟨b, hb, hbc⟩ := mem_creatorsOf.mp hvR
      obtain ⟨x, hx, hxc⟩ := mem_creatorsOf.mp hvC
      have hbU := U.complete A hA b hb
      have hbr := U.round_of_mem_refs hA hb
      obtain ⟨hxU, hxr⟩ := hX x hx
      have hbx : b = x := hne.eq_of_creator_eq hbU hxU hvH hbc hxc (by omega)
      subst hbx
      exact mem_creatorsOf.mpr ⟨b, Finset.mem_filter.mpr ⟨hx, mem_history_of_mem_refs hA hb⟩, hbc⟩
    have h1 := Finset.card_union_add_card_inter R CX
    have h2 := Finset.card_le_univ (R ∪ CX)
    have h3 := Finset.card_inter_add_card_sdiff (R ∩ CX) Hon
    have h4 : ((R ∩ CX) \ Hon).card ≤ Honᶜ.card :=
      Finset.card_le_card fun v hv => Finset.mem_compl.mpr (Finset.mem_sdiff.mp hv).2
    have h5 := Finset.card_le_card hsub
    omega
  | succ d ih =>
    intro A hA hround
    obtain ⟨b, hb⟩ := U.refs_nonempty hA (by omega)
    have hbU := U.complete A hA b hb
    have hbr := U.round_of_mem_refs hA hb
    refine le_trans (ih b hbU (by omega)) (Nat.add_le_add_left (Finset.card_le_card
      (Finset.image_subset_image fun C hC => ?_)) _)
    rw [Finset.mem_filter] at hC ⊢
    exact ⟨hC.1, history_subset_of_reaches hA (Reaches.single hb) hC.2⟩

end Visibility

end LeanDag
