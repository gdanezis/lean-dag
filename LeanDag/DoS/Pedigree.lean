import LeanDag.DoS.Adoption
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Ring

/-!
# Pedigrees, and the general bound

`dos-equivocation-and-growth.md` §5, the multi-equivocator case, the
last open piece of C1′. With several exposed authors, distinct tops need
not have distinct namer authors, so the flat count of `Adoption.lean`
stalls. What grounds it is nesting: an adopted top lies inside its
adopter's history, and climbing "who adopted the adopter" ends at `b`.
Three facts turn the climb into a count: pedigrees exist with
pairwise-distinct authors (`exists_pedigree`), a pedigree determines its
top from its author list (`pedigree_deterministic`), and duplicate-free
author lists over `3f+1` validators number at most `(3f+2)^(3f+1)`.
Together: `|topsOf U b X| ≤ (3f+2)^(3f+1) =: c(f)`, giving C1′
(`card_historyBlocksOf_le`) and the general bound
(`card_history_le`): `|H(b)| ≤ (3f+1)·c(f)·(r+1)`, linear in `r` at
every fault budget, though `c(f)` is astronomically loose.
-/

namespace LeanDag

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {U : BlockUniverse Validator BlockId Payload}

/-- The block itself tops its own chain: nothing in its history can
reference it. -/
theorem self_mem_topsOf {b : BlockId} (hb : b ∈ U.ids) :
    b ∈ topsOf U b (U.block b).creator := by
  refine mem_topsOf.mpr ⟨mem_history_self, rfl, ?_⟩
  intro c hc _ hbc
  have hc_ids := history_subset_ids hb hc
  have h1 := U.round_of_mem_refs hc_ids hbc
  have h2 := round_le_of_mem_history hb hc
  omega

/-- A same-author block strictly inside a history is on the root's chain
(D21/D22), so it has a same-author child there. The tool that unmakes
would-be tops. -/
theorem exists_child_of_mem_history_of_creator_eq (hdos : DoSValid U) {s t : BlockId}
    (hs : s ∈ U.ids) (hts : t ∈ history U s)
    (hc : (U.block t).creator = (U.block s).creator) (hne : t ≠ s) :
    ∃ q ∈ history U s, (U.block q).creator = (U.block s).creator ∧
      t ∈ (U.block q).refs := by
  have hle := round_le_of_mem_history hs hts
  have hlt : (U.block t).round < (U.block s).round := by
    rcases Nat.lt_or_ge (U.block t).round (U.block s).round with h | h
    · exact h
    · exact absurd (eq_of_mem_history_of_round_eq hs hts (by omega)) hne
  obtain ⟨q, hq, hqc, hqr⟩ := exists_self_ancestor hs
    (t := (U.block t).round + 1) (by omega)
  have hq_ids := history_subset_ids hs hq
  obtain ⟨p, hp, hpc⟩ := (U.valid q hq_ids).self_parent (by omega)
  have hpr := U.round_of_mem_refs hq_ids hp
  have hqsub : history U q ⊆ history U s :=
    history_subset_of_reaches hs ((mem_history_iff hs).mp hq)
  have hpt : p = t :=
    eq_of_not_exposedIn (not_exposedIn_self_creator hdos hs)
      (hqsub (mem_history_of_mem_refs hq_ids hp)) hts
      (hpc.trans hqc) hc (by omega)
  exact ⟨q, hq, hqc, hpt ▸ hp⟩

/-- `t` is adopted under `T`: some block of `T`'s own author, inside `T`'s
history, references `t`. By D21/D22 such a block sits on `T`'s chain, so
per (`T`, author-of-`t`) the adopted top is unique
(`top_eq_of_mem_namer_history`). -/
def AdoptedUnder (U : BlockUniverse Validator BlockId Payload) (b t T : BlockId) : Prop :=
  ∃ j ∈ history U b, j ∈ history U T ∧
    (U.block j).creator = (U.block T).creator ∧ t ∈ (U.block j).refs

/-- An adoption pedigree: the climb from a top to `b`, recording the
adopters' authors. -/
inductive PedigreeTo (U : BlockUniverse Validator BlockId Payload) (b : BlockId) :
    BlockId → List Validator → Prop
  | base : PedigreeTo U b b []
  | step {t T : BlockId} {l : List Validator} :
      t ∈ topsOf U b (U.block t).creator →
      AdoptedUnder U b t T →
      PedigreeTo U b T l →
      PedigreeTo U b t ((U.block T).creator :: l)

/-- Every author on a pedigree is realised by a *top* strictly above the
pedigree's base, whose history contains the base. The nesting that makes
pedigree authors distinct. -/
theorem pedigree_spec {b : BlockId} (hb : b ∈ U.ids) {s : BlockId} {l : List Validator}
    (hped : PedigreeTo U b s l) :
    s ∈ history U b ∧
      ∀ W ∈ l, ∃ s', s' ∈ history U b ∧ (U.block s').creator = W ∧
        s' ∈ topsOf U b (U.block s').creator ∧ s ∈ history U s' ∧
        (U.block s).round < (U.block s').round := by
  induction hped with
  | base => exact ⟨mem_history_self, fun W hW => by simp at hW⟩
  | @step t T l htop hadopt hrest ih =>
      obtain ⟨j, hjb, hjT, hjc, htref⟩ := hadopt
      have hTb : T ∈ history U b := ih.1
      have hT_ids : T ∈ U.ids := history_subset_ids hb hTb
      have hj_ids : j ∈ U.ids := history_subset_ids hb hjb
      have htT : t ∈ history U T :=
        history_subset_of_reaches hT_ids ((mem_history_iff hT_ids).mp hjT)
          (mem_history_of_mem_refs hj_ids htref)
      have hround_tj := U.round_of_mem_refs hj_ids htref
      have hround_jT := round_le_of_mem_history hT_ids hjT
      refine ⟨(mem_topsOf.mp htop).1, ?_⟩
      intro W hW
      rcases List.mem_cons.mp hW with rfl | hWl
      · refine ⟨T, hTb, rfl, ?_, htT, by omega⟩
        cases hrest with
        | base => exact self_mem_topsOf hb
        | step htop' _ _ => exact htop'
      · obtain ⟨s', hs'b, hs'c, hs'top, hTs', hTr⟩ := ih.2 W hWl
        have hs'_ids : s' ∈ U.ids := history_subset_ids hb hs'b
        exact ⟨s', hs'b, hs'c, hs'top,
          history_subset_of_reaches hs'_ids ((mem_history_iff hs'_ids).mp hTs') htT,
          by omega⟩

/-- **Pedigrees exist, with fresh authors all the way.** Every top climbs to
`b` through adopters whose authors, together with its own, are pairwise
distinct — a repeated author would put the earlier block on the later one's
chain and hand it a child. -/
theorem exists_pedigree (hdos : DoSValid U) {b : BlockId} (hb : b ∈ U.ids) :
    ∀ (n : ℕ) (t : BlockId), (U.block b).round - (U.block t).round ≤ n →
      t ∈ topsOf U b (U.block t).creator →
      ∃ l, PedigreeTo U b t l ∧ ((U.block t).creator :: l).Nodup := by
  intro n
  induction n with
  | zero =>
      intro t hfuel htop
      obtain ⟨htb, -, -⟩ := mem_topsOf.mp htop
      have hle := round_le_of_mem_history hb htb
      have : t = b := eq_of_mem_history_of_round_eq hb htb (by omega)
      subst this
      exact ⟨[], .base, List.nodup_singleton _⟩
  | succ n ih =>
      intro t hfuel htop
      by_cases hbt : t = b
      · subst hbt
        exact ⟨[], .base, List.nodup_singleton _⟩
      obtain ⟨htb, -, httop⟩ := mem_topsOf.mp htop
      obtain ⟨j, hjb, htref⟩ := exists_referencer hb htb hbt
      have hj_ids : j ∈ U.ids := history_subset_ids hb hjb
      obtain ⟨T, hTtop, hjT⟩ := exists_top_of_mem_history hb hjb rfl
      have hTc : (U.block T).creator = (U.block j).creator := (mem_topsOf.mp hTtop).2.1
      have hTb : T ∈ history U b := (mem_topsOf.mp hTtop).1
      have hT_ids := history_subset_ids hb hTb
      have hround_tj := U.round_of_mem_refs hj_ids htref
      have hround_jT := round_le_of_mem_history hT_ids hjT
      have hround_Tb := round_le_of_mem_history hb hTb
      have hTtop' : T ∈ topsOf U b (U.block T).creator := by
        rw [hTc]; exact hTtop
      obtain ⟨l, hped, hnodup⟩ := ih T (by omega) hTtop'
      have hadopt : AdoptedUnder U b t T := ⟨j, hjb, hjT, hTc.symm, htref⟩
      have hfull : PedigreeTo U b t ((U.block T).creator :: l) := .step htop hadopt hped
      refine ⟨(U.block T).creator :: l, hfull, ?_⟩
      rw [List.nodup_cons]
      refine ⟨?_, hnodup⟩
      intro hmem
      obtain ⟨-, hall⟩ := pedigree_spec hb hfull
      obtain ⟨s', hs'b, hs'c, -, hts', hround⟩ := hall _ hmem
      have hs'_ids := history_subset_ids hb hs'b
      have hne : t ≠ s' := by intro h; rw [h] at hround; omega
      obtain ⟨q, hq, hqc, htq⟩ :=
        exists_child_of_mem_history_of_creator_eq hdos hs'_ids hts' hs'c.symm hne
      have hqb : q ∈ history U b :=
        history_subset_of_reaches hb ((mem_history_iff hb).mp hs'b) hq
      exact httop q hqb (hqc.trans hs'c) htq

/-- Inverting one pedigree step against a cons list. -/
theorem pedigree_cons_inv {b t : BlockId} {W : Validator} {l : List Validator}
    (h : PedigreeTo U b t (W :: l)) :
    ∃ T, (U.block T).creator = W ∧ t ∈ topsOf U b (U.block t).creator ∧
      AdoptedUnder U b t T ∧ PedigreeTo U b T l := by
  cases h with
  | step htop hadopt hrest => exact ⟨_, rfl, htop, hadopt, hrest⟩

/-- **Pedigrees determine.** Two tops of one author with the same pedigree
author-list are equal: each step downward is the unique adopted top of that
author under that adopter (the adoption collapse). -/
theorem pedigree_deterministic (hdos : DoSValid U) {b : BlockId} (hb : b ∈ U.ids) :
    ∀ {l : List Validator} {t₁ t₂ : BlockId},
      PedigreeTo U b t₁ l → PedigreeTo U b t₂ l →
      (U.block t₁).creator = (U.block t₂).creator → t₁ = t₂ := by
  intro l
  induction l with
  | nil =>
      intro t₁ t₂ h₁ h₂ _
      cases h₁
      cases h₂
      rfl
  | cons W l ih =>
      intro t₁ t₂ h₁ h₂ hcreator
      obtain ⟨T₁, hW₁, htop₁, hadopt₁, hrest₁⟩ := pedigree_cons_inv h₁
      obtain ⟨T₂, hW₂, htop₂, hadopt₂, hrest₂⟩ := pedigree_cons_inv h₂
      have hTT : T₂ = T₁ := ih hrest₂ hrest₁ (hW₂.trans hW₁.symm)
      subst hTT
      obtain ⟨j₁, hj₁b, hj₁T, hj₁c, ht₁ref⟩ := hadopt₁
      obtain ⟨j₂, hj₂b, hj₂T, hj₂c, ht₂ref⟩ := hadopt₂
      have hT_ids : T₂ ∈ U.ids :=
        history_subset_ids hb (pedigree_spec hb hrest₁).1
      have hXexp : ¬ ExposedIn U T₂ (U.block T₂).creator :=
        not_exposedIn_self_creator hdos hT_ids
      have htop₂' : t₂ ∈ topsOf U b (U.block t₁).creator := by
        rw [hcreator]; exact htop₂
      rcases le_total (U.block j₁).round (U.block j₂).round with hle | hle
      · have hchain : j₁ ∈ history U j₂ :=
          mem_history_of_creator_eq_of_not_exposedIn hT_ids hXexp hj₁T hj₂T
            hj₁c hj₂c hle
        have hj₂_ids : j₂ ∈ U.ids := history_subset_ids hb hj₂b
        have ht₁j₂ : t₁ ∈ history U j₂ :=
          history_subset_of_reaches hj₂_ids ((mem_history_iff hj₂_ids).mp hchain)
            (mem_history_of_mem_refs (history_subset_ids hb hj₁b) ht₁ref)
        exact top_eq_of_mem_namer_history hdos hb htop₁ htop₂' hj₂b ht₂ref ht₁j₂
      · have hchain : j₂ ∈ history U j₁ :=
          mem_history_of_creator_eq_of_not_exposedIn hT_ids hXexp hj₂T hj₁T
            hj₂c hj₁c hle
        have hj₁_ids : j₁ ∈ U.ids := history_subset_ids hb hj₁b
        have ht₂j₁ : t₂ ∈ history U j₁ :=
          history_subset_of_reaches hj₁_ids ((mem_history_iff hj₁_ids).mp hchain)
            (mem_history_of_mem_refs (history_subset_ids hb hj₂b) ht₂ref)
        exact (top_eq_of_mem_namer_history hdos hb htop₂' htop₁ hj₁b ht₁ref
          ht₂j₁).symm

/-- **The general top count.** A top is determined by its own author and its
pedigree's duplicate-free author list, of which there are at most
`(3f+2)^(3f+1)`. -/
theorem card_topsOf_le_pow (hdos : DoSValid U) {b : BlockId} (hb : b ∈ U.ids)
    (X : Validator) :
    (topsOf U b X).card ≤ ((Fintype.card Validator + 1)) ^ (Fintype.card Validator) := by
  classical
  have hex : ∀ t ∈ topsOf U b X,
      ∃ l, PedigreeTo U b t l ∧ ((U.block t).creator :: l).Nodup := by
    intro t ht
    have htc : (U.block t).creator = X := (mem_topsOf.mp ht).2.1
    exact exists_pedigree hdos hb _ t (le_refl _) (by rw [htc]; exact ht)
  have hinj : (topsOf U b X).card
      ≤ Fintype.card (Fin (Fintype.card Validator) → Option Validator) := by
    rw [← Finset.card_univ]
    refine Finset.card_le_card_of_injOn
      (fun t => (fun k : Fin (Fintype.card Validator) =>
        (if h : ∃ l, PedigreeTo U b t l ∧ ((U.block t).creator :: l).Nodup
          then h.choose else [])[(k : ℕ)]?))
      (fun _ _ => Finset.mem_univ _) ?_
    intro t₁ h₁ t₂ h₂ heq
    rw [Finset.mem_coe] at h₁ h₂
    have hex₁ := hex t₁ h₁
    have hex₂ := hex t₂ h₂
    simp only [dif_pos hex₁, dif_pos hex₂] at heq
    have hlen₁ : hex₁.choose.length ≤ (Fintype.card Validator - 1) := by
      have hlc := hex₁.choose_spec.2.length_le_card
      simp only [List.length_cons] at hlc
      omega
    have hlen₂ : hex₂.choose.length ≤ (Fintype.card Validator - 1) := by
      have hlc := hex₂.choose_spec.2.length_le_card
      simp only [List.length_cons] at hlc
      omega
    have hlists : hex₁.choose = hex₂.choose := by
      apply List.ext_getElem?'
      intro n hn
      have hn' : n < Fintype.card Validator := by
        have hmax : max hex₁.choose.length hex₂.choose.length ≤ (Fintype.card Validator - 1) :=
          max_le hlen₁ hlen₂
        omega
      have := congrFun heq ⟨n, hn'⟩
      simpa using this
    have hped₂ : PedigreeTo U b t₂ hex₁.choose := by
      rw [hlists]; exact hex₂.choose_spec.1
    have hcreator : (U.block t₁).creator = (U.block t₂).creator :=
      ((mem_topsOf.mp h₁).2.1).trans ((mem_topsOf.mp h₂).2.1).symm
    exact pedigree_deterministic hdos hb hex₁.choose_spec.1 hped₂ hcreator
  calc (topsOf U b X).card
      ≤ Fintype.card (Fin (Fintype.card Validator) → Option Validator) := hinj
    _ = ((Fintype.card Validator + 1)) ^ (Fintype.card Validator) := by
        rw [Fintype.card_fun, Fintype.card_option, Fintype.card_fin]

/-- An author's per-round contribution never exceeds its chain count: each
round-`n` block sits on the chain of a distinct top. -/
theorem card_historyBlocksOf_le_card_topsOf (hdos : DoSValid U) {b : BlockId}
    (hb : b ∈ U.ids) (X : Validator) (n : ℕ) :
    (historyBlocksOf U b X n).card ≤ (topsOf U b X).card := by
  classical
  refine Finset.card_le_card_of_injOn
    (fun i => if h : ∃ t ∈ topsOf U b X, i ∈ history U t then h.choose else i) ?_ ?_
  · intro i hi
    simp only [Finset.mem_coe] at hi
    obtain ⟨hih, hic, -⟩ := mem_historyBlocksOf.mp hi
    have hex := exists_top_of_mem_history hb hih hic
    refine Finset.mem_coe.mpr ?_
    change (if h : ∃ t ∈ topsOf U b X, i ∈ history U t then h.choose else i) ∈ topsOf U b X
    rw [dif_pos hex]
    exact hex.choose_spec.1
  · intro i₁ h₁ i₂ h₂ heq
    simp only [Finset.mem_coe] at h₁ h₂
    obtain ⟨hi₁h, hi₁c, hi₁r⟩ := mem_historyBlocksOf.mp h₁
    obtain ⟨hi₂h, hi₂c, hi₂r⟩ := mem_historyBlocksOf.mp h₂
    have hex₁ := exists_top_of_mem_history hb hi₁h hi₁c
    have hex₂ := exists_top_of_mem_history hb hi₂h hi₂c
    simp only [dif_pos hex₁, dif_pos hex₂] at heq
    obtain ⟨htmem, hi₁t⟩ := hex₁.choose_spec
    have hi₂t : i₂ ∈ history U hex₁.choose := heq ▸ hex₂.choose_spec.2
    obtain ⟨htb, htc, -⟩ := mem_topsOf.mp htmem
    have ht_ids : hex₁.choose ∈ U.ids := history_subset_ids hb htb
    exact eq_of_not_exposedIn (not_exposedIn_self_creator hdos ht_ids) hi₁t hi₂t
      (hi₁c.trans htc.symm) (hi₂c.trans htc.symm) (by rw [hi₁r, hi₂r])

/-- **C1′, in full.** Under `DoSValid` with self-parents, an author
contributes at most `c(f) = (3f+2)^(3f+1)` blocks per round to any history —
a constant in `r`, for every `f`. Compounding is impossible. -/
theorem card_historyBlocksOf_le (hdos : DoSValid U) {b : BlockId} (hb : b ∈ U.ids)
    (X : Validator) (n : ℕ) :
    (historyBlocksOf U b X n).card ≤ ((Fintype.card Validator + 1)) ^ (Fintype.card Validator) :=
  le_trans (card_historyBlocksOf_le_card_topsOf hdos hb X n)
    (card_topsOf_le_pow hdos hb X)

/-- **The general bound.** Every DoS-valid history is linear in its
round, at every fault budget: `|H(b)| ≤ (3f+1) · (3f+2)^(3f+1) · (r+1)`. -/
theorem card_history_le (hdos : DoSValid U) {b : BlockId} (hb : b ∈ U.ids) :
    (history U b).card
      ≤ (Fintype.card Validator) * ((Fintype.card Validator + 1)) ^ (Fintype.card Validator) * ((U.block b).round + 1) := by
  classical
  calc (history U b).card
      = ∑ W ∈ Finset.univ,
          ((history U b).filter fun i => (U.block i).creator = W).card :=
        Finset.card_eq_sum_card_fiberwise (fun i _ => Finset.mem_univ _)
    _ ≤ ∑ _W ∈ (Finset.univ : Finset Validator),
          ((Fintype.card Validator + 1)) ^ (Fintype.card Validator) * ((U.block b).round + 1) := by
        refine Finset.sum_le_sum ?_
        intro W _
        calc ((history U b).filter fun i => (U.block i).creator = W).card
            ≤ (topsOf U b W).card * ((U.block b).round + 1) :=
              card_filter_creator_le_card_topsOf hdos hb W
          _ ≤ ((Fintype.card Validator + 1)) ^ (Fintype.card Validator) * ((U.block b).round + 1) :=
              Nat.mul_le_mul_right _ (card_topsOf_le_pow hdos hb W)
    _ = (Fintype.card Validator) * (((Fintype.card Validator + 1)) ^ (Fintype.card Validator) * ((U.block b).round + 1)) := by
        rw [Finset.sum_const_nat (fun _ _ => rfl), Finset.card_univ]
    _ = (Fintype.card Validator) * ((Fintype.card Validator + 1)) ^ (Fintype.card Validator) * ((U.block b).round + 1) := by
        rw [Nat.mul_assoc]

/-! ## Tightening the constant: an author with two chains is exposed, so
only exposed authors branch, and a pedigree can stop at its first
unexposed-author adopter (`PedigreeVia`). The refined count is
`|topsOf U b X| ≤ (3f+1-e) · e^(e-1)` where `e := |exposedTo U b| ≤ f`
(`card_topsOf_le_of_exposed`), giving `|H(b)| ≤ (3f+1 + 3f^(f+1))·(r+1)`
(`card_history_le'`), which matches the adoption theorem's `7(r+1)` at
`f = 1`. -/

/-- **An unexposed author has at most one chain.** Two tops would be
chain-related, and the lower would have a child. Contrapositive: branching
proves equivocation — only exposed authors, at most `f`, can branch. -/
theorem card_topsOf_le_one_of_not_exposedIn (hdos : DoSValid U) {b : BlockId}
    (hb : b ∈ U.ids) {X : Validator} (hX : ¬ ExposedIn U b X) :
    (topsOf U b X).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro t₁ h₁ t₂ h₂
  by_contra hne
  obtain ⟨h₁b, h₁c, h₁top⟩ := mem_topsOf.mp h₁
  obtain ⟨h₂b, h₂c, h₂top⟩ := mem_topsOf.mp h₂
  rcases le_total (U.block t₁).round (U.block t₂).round with hle | hle
  · have hmem : t₁ ∈ history U t₂ :=
      mem_history_of_creator_eq_of_not_exposedIn hb hX h₁b h₂b h₁c h₂c hle
    have h₂ids : t₂ ∈ U.ids := history_subset_ids hb h₂b
    obtain ⟨q, hq, hqc, htq⟩ :=
      exists_child_of_mem_history_of_creator_eq hdos h₂ids hmem (h₁c.trans h₂c.symm) hne
    exact h₁top q (history_subset_of_reaches hb ((mem_history_iff hb).mp h₂b) hq)
      (hqc.trans h₂c) htq
  · have hmem : t₂ ∈ history U t₁ :=
      mem_history_of_creator_eq_of_not_exposedIn hb hX h₂b h₁b h₂c h₁c hle
    have h₁ids : t₁ ∈ U.ids := history_subset_ids hb h₁b
    obtain ⟨q, hq, hqc, htq⟩ :=
      exists_child_of_mem_history_of_creator_eq hdos h₁ids hmem (h₂c.trans h₁c.symm)
        (Ne.symm hne)
    exact h₂top q (history_subset_of_reaches hb ((mem_history_iff hb).mp h₁b) hq)
      (hqc.trans h₁c) htq

/-- The adoption collapse, packaged: one adopted top per (adopter, author). -/
theorem adoptedUnder_unique (hdos : DoSValid U) {b : BlockId} (hb : b ∈ U.ids)
    {t₁ t₂ T : BlockId} (hT : T ∈ history U b)
    (htop₁ : t₁ ∈ topsOf U b (U.block t₁).creator)
    (htop₂ : t₂ ∈ topsOf U b (U.block t₂).creator)
    (hc : (U.block t₁).creator = (U.block t₂).creator)
    (ha₁ : AdoptedUnder U b t₁ T) (ha₂ : AdoptedUnder U b t₂ T) : t₁ = t₂ := by
  obtain ⟨j₁, hj₁b, hj₁T, hj₁c, ht₁ref⟩ := ha₁
  obtain ⟨j₂, hj₂b, hj₂T, hj₂c, ht₂ref⟩ := ha₂
  have hT_ids : T ∈ U.ids := history_subset_ids hb hT
  have hXexp : ¬ ExposedIn U T (U.block T).creator :=
    not_exposedIn_self_creator hdos hT_ids
  have htop₂' : t₂ ∈ topsOf U b (U.block t₁).creator := by
    rw [hc]; exact htop₂
  rcases le_total (U.block j₁).round (U.block j₂).round with hle | hle
  · have hchain : j₁ ∈ history U j₂ :=
      mem_history_of_creator_eq_of_not_exposedIn hT_ids hXexp hj₁T hj₂T hj₁c hj₂c hle
    have hj₂_ids : j₂ ∈ U.ids := history_subset_ids hb hj₂b
    have ht₁j₂ : t₁ ∈ history U j₂ :=
      history_subset_of_reaches hj₂_ids ((mem_history_iff hj₂_ids).mp hchain)
        (mem_history_of_mem_refs (history_subset_ids hb hj₁b) ht₁ref)
    exact top_eq_of_mem_namer_history hdos hb htop₁ htop₂' hj₂b ht₂ref ht₁j₂
  · have hchain : j₂ ∈ history U j₁ :=
      mem_history_of_creator_eq_of_not_exposedIn hT_ids hXexp hj₂T hj₁T hj₂c hj₁c hle
    have hj₁_ids : j₁ ∈ U.ids := history_subset_ids hb hj₁b
    have ht₂j₁ : t₂ ∈ history U j₁ :=
      history_subset_of_reaches hj₁_ids ((mem_history_iff hj₁_ids).mp hchain)
        (mem_history_of_mem_refs (history_subset_ids hb hj₂b) ht₂ref)
    exact (top_eq_of_mem_namer_history hdos hb htop₂' htop₁ hj₁b ht₁ref ht₂j₁).symm

/-- A pedigree anchored at an arbitrary block `T` rather than at `b`,
recording only the *intermediate* adopters' authors. -/
inductive PedigreeVia (U : BlockUniverse Validator BlockId Payload) (b : BlockId) :
    BlockId → BlockId → List Validator → Prop
  | base {t T : BlockId} :
      t ∈ topsOf U b (U.block t).creator → AdoptedUnder U b t T →
      PedigreeVia U b t T []
  | step {t T₁ T : BlockId} {l : List Validator} :
      t ∈ topsOf U b (U.block t).creator → AdoptedUnder U b t T₁ →
      PedigreeVia U b T₁ T l →
      PedigreeVia U b t T ((U.block T₁).creator :: l)

theorem pedigreeVia_top {b t T : BlockId} {l : List Validator}
    (h : PedigreeVia U b t T l) : t ∈ topsOf U b (U.block t).creator := by
  cases h with
  | base htop _ => exact htop
  | step htop _ _ => exact htop

theorem pedigreeVia_nil_inv {b t T : BlockId} (h : PedigreeVia U b t T []) :
    AdoptedUnder U b t T := by
  cases h with
  | base _ ha => exact ha

theorem pedigreeVia_cons_inv {b t T : BlockId} {W : Validator} {l : List Validator}
    (h : PedigreeVia U b t T (W :: l)) :
    ∃ T₁, (U.block T₁).creator = W ∧ AdoptedUnder U b t T₁ ∧ PedigreeVia U b T₁ T l := by
  cases h with
  | step htop ha hrest => exact ⟨_, rfl, ha, hrest⟩

/-- Every recorded author is realised by a top strictly above the subject,
containing it — the nesting that keeps pedigree authors fresh. -/
theorem pedigreeVia_spec {b : BlockId} (hb : b ∈ U.ids) {s T : BlockId}
    {l : List Validator} (hped : PedigreeVia U b s T l) :
    ∀ W ∈ l, ∃ s', s' ∈ history U b ∧ (U.block s').creator = W ∧
      s' ∈ topsOf U b (U.block s').creator ∧ s ∈ history U s' ∧
      (U.block s).round < (U.block s').round := by
  induction hped with
  | base _ _ => intro W hW; simp at hW
  | @step t T₁ T l htop hadopt hrest ih =>
      obtain ⟨j, hjb, hjT, hjc, htref⟩ := hadopt
      have hT₁top := pedigreeVia_top hrest
      have hT₁b : T₁ ∈ history U b := (mem_topsOf.mp hT₁top).1
      have hT₁_ids : T₁ ∈ U.ids := history_subset_ids hb hT₁b
      have hj_ids : j ∈ U.ids := history_subset_ids hb hjb
      have htT₁ : t ∈ history U T₁ :=
        history_subset_of_reaches hT₁_ids ((mem_history_iff hT₁_ids).mp hjT)
          (mem_history_of_mem_refs hj_ids htref)
      have hround_tj := U.round_of_mem_refs hj_ids htref
      have hround_jT := round_le_of_mem_history hT₁_ids hjT
      intro W hW
      rcases List.mem_cons.mp hW with rfl | hWl
      · exact ⟨T₁, hT₁b, rfl, hT₁top, htT₁, by omega⟩
      · obtain ⟨s', hs'b, hs'c, hs'top, hTs', hTr⟩ := ih W hWl
        have hs'_ids : s' ∈ U.ids := history_subset_ids hb hs'b
        exact ⟨s', hs'b, hs'c, hs'top,
          history_subset_of_reaches hs'_ids ((mem_history_iff hs'_ids).mp hTs') htT₁,
          by omega⟩

/-- Anchored determinism: given the anchor and the intermediate author list,
the top is unique. -/
theorem pedigreeVia_deterministic (hdos : DoSValid U) {b : BlockId} (hb : b ∈ U.ids)
    {T : BlockId} (hT : T ∈ history U b) :
    ∀ {l : List Validator} {t₁ t₂ : BlockId},
      PedigreeVia U b t₁ T l → PedigreeVia U b t₂ T l →
      (U.block t₁).creator = (U.block t₂).creator → t₁ = t₂ := by
  intro l
  induction l with
  | nil =>
      intro t₁ t₂ h₁ h₂ hc
      exact adoptedUnder_unique hdos hb hT (pedigreeVia_top h₁) (pedigreeVia_top h₂) hc
        (pedigreeVia_nil_inv h₁) (pedigreeVia_nil_inv h₂)
  | cons W l ih =>
      intro t₁ t₂ h₁ h₂ hc
      obtain ⟨T₁, hW₁, ha₁, hrest₁⟩ := pedigreeVia_cons_inv h₁
      obtain ⟨T₂, hW₂, ha₂, hrest₂⟩ := pedigreeVia_cons_inv h₂
      have hTT : T₂ = T₁ := ih hrest₂ hrest₁ (hW₂.trans hW₁.symm)
      subst hTT
      have hT₂b : T₂ ∈ history U b := (mem_topsOf.mp (pedigreeVia_top hrest₁)).1
      exact adoptedUnder_unique hdos hb hT₂b (pedigreeVia_top h₁) (pedigreeVia_top h₂)
        hc ha₁ ha₂

/-- **Anchored pedigrees exist.** The top of an *exposed* author climbs
through exposed-author adopters to the first unexposed-author top — with the
subject's author fresh throughout, and every recorded author exposed. -/
theorem exists_pedigreeVia (hdos : DoSValid U) {b : BlockId} (hb : b ∈ U.ids) :
    ∀ (n : ℕ) (t : BlockId), (U.block b).round - (U.block t).round ≤ n →
      t ∈ topsOf U b (U.block t).creator → ExposedIn U b (U.block t).creator →
      ∃ T l, T ∈ topsOf U b (U.block T).creator ∧
        ¬ ExposedIn U b (U.block T).creator ∧
        PedigreeVia U b t T l ∧ ((U.block t).creator :: l).Nodup ∧
        ∀ W ∈ l, ExposedIn U b W := by
  intro n
  induction n with
  | zero =>
      intro t hfuel htop hexp
      obtain ⟨htb, -, -⟩ := mem_topsOf.mp htop
      have hle := round_le_of_mem_history hb htb
      have heq : t = b := eq_of_mem_history_of_round_eq hb htb (by omega)
      subst heq
      exact absurd hexp (not_exposedIn_self_creator hdos hb)
  | succ n ih =>
      intro t hfuel htop hexp
      have hbt : t ≠ b := by
        intro h
        subst h
        exact not_exposedIn_self_creator hdos hb hexp
      obtain ⟨htb, -, httop⟩ := mem_topsOf.mp htop
      obtain ⟨j, hjb, htref⟩ := exists_referencer hb htb hbt
      have hj_ids : j ∈ U.ids := history_subset_ids hb hjb
      obtain ⟨T₁, hT₁top, hjT₁⟩ := exists_top_of_mem_history hb hjb rfl
      have hT₁c : (U.block T₁).creator = (U.block j).creator := (mem_topsOf.mp hT₁top).2.1
      have hT₁b : T₁ ∈ history U b := (mem_topsOf.mp hT₁top).1
      have hT₁_ids := history_subset_ids hb hT₁b
      have hround_tj := U.round_of_mem_refs hj_ids htref
      have hround_jT := round_le_of_mem_history hT₁_ids hjT₁
      have hround_Tb := round_le_of_mem_history hb hT₁b
      have hT₁top' : T₁ ∈ topsOf U b (U.block T₁).creator := by
        rw [hT₁c]; exact hT₁top
      have hadopt : AdoptedUnder U b t T₁ := ⟨j, hjb, hjT₁, hT₁c.symm, htref⟩
      by_cases hexp₁ : ExposedIn U b (U.block T₁).creator
      · obtain ⟨T, l, hTtop, hTunexp, hped, hnodup, hexps⟩ :=
          ih T₁ (by omega) hT₁top' hexp₁
        have hfull : PedigreeVia U b t T ((U.block T₁).creator :: l) :=
          .step htop hadopt hped
        refine ⟨T, (U.block T₁).creator :: l, hTtop, hTunexp, hfull, ?_, ?_⟩
        · rw [List.nodup_cons]
          refine ⟨?_, hnodup⟩
          intro hmem
          obtain ⟨s', hs'b, hs'c, -, hts', hround⟩ := pedigreeVia_spec hb hfull _ hmem
          have hs'_ids := history_subset_ids hb hs'b
          have hne : t ≠ s' := by intro h; rw [h] at hround; omega
          obtain ⟨q, hq, hqc, htq⟩ :=
            exists_child_of_mem_history_of_creator_eq hdos hs'_ids hts' hs'c.symm hne
          exact httop q
            (history_subset_of_reaches hb ((mem_history_iff hb).mp hs'b) hq)
            (hqc.trans hs'c) htq
        · intro W hW
          rcases List.mem_cons.mp hW with rfl | hWl
          · exact hexp₁
          · exact hexps W hWl
      · exact ⟨T₁, [], hT₁top', hexp₁, .base htop hadopt, List.nodup_singleton _,
          fun W hW => by simp at hW⟩

/-- The padded encoding of a list of at most `m` members of `E'`: entry
`k` is the `k`-th element when there is one, and `none` past the end. -/
def encodeList (E' : Finset Validator) (m : ℕ) (l : List Validator) :
    Fin m → Option {W // W ∈ E'} :=
  fun k => if hk : (k : ℕ) < l.length then
      if hmem : l[(k : ℕ)] ∈ E' then some ⟨l[(k : ℕ)], hmem⟩ else none
    else none

/-- **The encoding is faithful.** Two lists over `E'` of length at most
`m` with the same encoding are equal. -/
theorem encodeList_injOn {E' : Finset Validator} {m : ℕ} {l₁ l₂ : List Validator}
    (h₁ : l₁.length ≤ m) (h₂ : l₂.length ≤ m)
    (he₁ : ∀ W ∈ l₁, W ∈ E') (he₂ : ∀ W ∈ l₂, W ∈ E')
    (hfun : encodeList E' m l₁ = encodeList E' m l₂) : l₁ = l₂ := by
  have hleneq : l₁.length = l₂.length := by
    by_contra hne
    rcases Nat.lt_or_ge l₁.length l₂.length with hlt | hge
    · have hk : l₁.length < m := by omega
      have hthis := congrFun hfun ⟨l₁.length, hk⟩
      simp only [encodeList, Fin.val_mk] at hthis
      rw [dif_neg (lt_irrefl _), dif_pos hlt,
        dif_pos (he₂ _ (List.getElem_mem _))] at hthis
      simp at hthis
    · have hlt : l₂.length < l₁.length := by omega
      have hk : l₂.length < m := by omega
      have hthis := congrFun hfun ⟨l₂.length, hk⟩
      simp only [encodeList, Fin.val_mk] at hthis
      rw [dif_pos hlt, dif_neg (lt_irrefl _),
        dif_pos (he₁ _ (List.getElem_mem _))] at hthis
      simp at hthis
  refine List.ext_getElem hleneq ?_
  intro k hk₁ hk₂
  have hkm : k < m := by omega
  have hthis := congrFun hfun ⟨k, hkm⟩
  simp only [encodeList, Fin.val_mk] at hthis
  rw [dif_pos hk₁, dif_pos hk₂,
    dif_pos (he₁ _ (List.getElem_mem _)), dif_pos (he₂ _ (List.getElem_mem _))] at hthis
  exact congrArg Subtype.val (Option.some_injective _ hthis)

/-- **Every top has an anchored pedigree, in totalised form**, so that
`choose` applies. -/
theorem exists_pedigree_data (hdos : DoSValid U) {b : BlockId} (hb : b ∈ U.ids)
    {X : Validator} (hX : ExposedIn U b X) :
    ∀ t : BlockId, ∃ p : BlockId × List Validator,
      t ∈ topsOf U b X →
        p.1 ∈ topsOf U b (U.block p.1).creator ∧
        ¬ ExposedIn U b (U.block p.1).creator ∧
        PedigreeVia U b t p.1 p.2 ∧ p.2.Nodup ∧
        ∀ W ∈ p.2, W ∈ (exposedTo U b).erase X := by
  intro t
  by_cases ht : t ∈ topsOf U b X
  · have htc : (U.block t).creator = X := (mem_topsOf.mp ht).2.1
    obtain ⟨T, l, hTtop, hTunexp, hped, hnodup, hexps⟩ :=
      exists_pedigreeVia hdos hb _ t (le_refl _) (by rw [htc]; exact ht)
        (by rw [htc]; exact hX)
    rw [List.nodup_cons] at hnodup
    refine ⟨(T, l), fun _ => ⟨hTtop, hTunexp, hped, hnodup.2, ?_⟩⟩
    intro W hW
    rw [Finset.mem_erase]
    refine ⟨?_, mem_exposedTo.mpr (hexps W hW)⟩
    intro h
    exact hnodup.1 (htc ▸ h ▸ hW)
  · exact ⟨(b, []), fun h => absurd h ht⟩

/-- **The tightened top count.** With `e := |exposedTo U b|`, an exposed
author has at most `(3f+1-e) · e^(e-1)` chains: one anchor per unexposed
author, and intermediate authors drawn without repetition from the other
exposed authors. -/
theorem card_topsOf_le_of_exposed (hdos : DoSValid U) {b : BlockId} (hb : b ∈ U.ids)
    {X : Validator} (hX : ExposedIn U b X) :
    (topsOf U b X).card ≤
      (Fintype.card Validator - (exposedTo U b).card) *
        (exposedTo U b).card ^ ((exposedTo U b).erase X).card := by
  classical
  set E' := (exposedTo U b).erase X with hE'
  set m := E'.card with hm
  have hdata := exists_pedigree_data hdos hb hX
  choose dataP hdataP using hdata
  have hlen : ∀ t, t ∈ topsOf U b X → (dataP t).2.length ≤ m := by
    intro t ht
    obtain ⟨-, -, -, hnd, hent⟩ := hdataP t ht
    have hsub : (dataP t).2.toFinset ⊆ E' := by
      intro W hW
      exact hent W (List.mem_toFinset.mp hW)
    have := Finset.card_le_card hsub
    rwa [List.toFinset_card_of_nodup hnd] at this
  -- injection: anchor author × entry encoding
  have hinj : (topsOf U b X).card ≤
      ((Finset.univ.filter fun W => ¬ ExposedIn U b W) ×ˢ
        (Finset.univ : Finset (Fin m → Option {W // W ∈ E'}))).card := by
    refine Finset.card_le_card_of_injOn
      (fun t => ((U.block (dataP t).1).creator, encodeList E' m (dataP t).2)) ?_ ?_
    · intro t ht
      rw [Finset.mem_coe] at ht
      refine Finset.mem_coe.mpr (Finset.mem_product.mpr ⟨?_, Finset.mem_univ _⟩)
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hdataP t ht).2.1⟩
    · intro t₁ h₁ t₂ h₂ heq
      rw [Finset.mem_coe] at h₁ h₂
      obtain ⟨hA₁top, hA₁unexp, hped₁, hnd₁, hent₁⟩ := hdataP t₁ h₁
      obtain ⟨hA₂top, hA₂unexp, hped₂, hnd₂, hent₂⟩ := hdataP t₂ h₂
      rw [Prod.mk.injEq] at heq
      obtain ⟨hanchor, hfun⟩ := heq
      -- anchors coincide: same unexposed author, one top each
      have hA : (dataP t₁).1 = (dataP t₂).1 := by
        have hA₂top' : (dataP t₂).1 ∈ topsOf U b (U.block (dataP t₁).1).creator := by
          rw [hanchor]; exact hA₂top
        have hcard := card_topsOf_le_one_of_not_exposedIn hdos hb hA₁unexp
        rw [Finset.card_le_one] at hcard
        exact hcard _ hA₁top _ hA₂top'
      -- lists coincide: the encoding is faithful
      have hlists : (dataP t₁).2 = (dataP t₂).2 :=
        encodeList_injOn (hlen t₁ h₁) (hlen t₂ h₂) hent₁ hent₂ hfun
      -- determinism closes it
      have hcreator : (U.block t₁).creator = (U.block t₂).creator :=
        ((mem_topsOf.mp h₁).2.1).trans ((mem_topsOf.mp h₂).2.1).symm
      have hped₂' : PedigreeVia U b t₂ (dataP t₁).1 (dataP t₁).2 := by
        rw [hA, hlists]; exact hped₂
      exact pedigreeVia_deterministic hdos hb (mem_topsOf.mp hA₁top).1
        hped₁ hped₂' hcreator
  -- count the target
  have hfilter : (Finset.univ.filter fun W => ¬ ExposedIn U b W).card
      = Fintype.card Validator - (exposedTo U b).card := by
    have hcompl : (Finset.univ.filter fun W => ¬ ExposedIn U b W)
        = (exposedTo U b)ᶜ := by
      ext W
      simp [exposedTo, Finset.mem_compl]
    rw [hcompl, Finset.card_compl]
  have hbase : m + 1 = (exposedTo U b).card := by
    rw [hm, hE', Finset.card_erase_of_mem (mem_exposedTo.mpr hX)]
    have : 0 < (exposedTo U b).card :=
      Finset.card_pos.mpr ⟨X, mem_exposedTo.mpr hX⟩
    omega
  calc (topsOf U b X).card
      ≤ ((Finset.univ.filter fun W => ¬ ExposedIn U b W) ×ˢ
          (Finset.univ : Finset (Fin m → Option {W // W ∈ E'}))).card := hinj
    _ = (Fintype.card Validator - (exposedTo U b).card) *
          (exposedTo U b).card ^ ((exposedTo U b).erase X).card := by
        rw [Finset.card_product, Finset.card_univ, Fintype.card_fun,
          Fintype.card_option, Fintype.card_coe, Fintype.card_fin, hfilter,
          ← hE', ← hm, hbase]

/-- **C1′, tightened.** The per-round contribution of any author to any
history is at most `1 + 3f·f^(f-1)` — down from `(3f+2)^(3f+1)`. -/
theorem card_historyBlocksOf_le' (hdos : DoSValid U) {b : BlockId} (hb : b ∈ U.ids)
    (X : Validator) (n : ℕ) :
    (historyBlocksOf U b X n).card ≤ 1 + (Fintype.card Validator - 1) * F.f ^ (F.f - 1) := by
  refine le_trans (card_historyBlocksOf_le_card_topsOf hdos hb X n) ?_
  by_cases hX : ExposedIn U b X
  · refine le_trans (card_topsOf_le_of_exposed hdos hb hX) ?_
    have he : 1 ≤ (exposedTo U b).card :=
      Finset.card_pos.mpr ⟨X, mem_exposedTo.mpr hX⟩
    have hef : (exposedTo U b).card ≤ F.f := card_exposedTo_le hb
    have hf1 : 1 ≤ F.f := le_trans he hef
    have h1 : Fintype.card Validator - (exposedTo U b).card ≤ (Fintype.card Validator - 1) := by omega
    have h2 : (exposedTo U b).card ^ ((exposedTo U b).erase X).card
        ≤ F.f ^ (F.f - 1) := by
      have herase : ((exposedTo U b).erase X).card ≤ F.f - 1 := by
        rw [Finset.card_erase_of_mem (mem_exposedTo.mpr hX)]
        omega
      calc (exposedTo U b).card ^ ((exposedTo U b).erase X).card
          ≤ F.f ^ ((exposedTo U b).erase X).card := Nat.pow_le_pow_left hef _
        _ ≤ F.f ^ (F.f - 1) := Nat.pow_le_pow_right hf1 herase
    calc (Fintype.card Validator - (exposedTo U b).card) *
          (exposedTo U b).card ^ ((exposedTo U b).erase X).card
        ≤ (Fintype.card Validator - 1) * (F.f ^ (F.f - 1)) := Nat.mul_le_mul h1 h2
      _ ≤ 1 + (Fintype.card Validator - 1) * F.f ^ (F.f - 1) := by omega
  · have := card_topsOf_le_one_of_not_exposedIn hdos hb hX
    omega

/-- **The tightened total.** `|H(b)| ≤ (3f+1 + 3f^(f+1))·(r+1)`: the
unexposed authors contribute one chain each, the at-most-`f` exposed ones at
most `3f·f^(f-1)` chains each. At `f = 1` this is `7(r+1)`, recovering the
adoption theorem's constant exactly. -/
theorem card_history_le' (hdos : DoSValid U) {b : BlockId} (hb : b ∈ U.ids) :
    (history U b).card
      ≤ (Fintype.card Validator + (Fintype.card Validator - 1) * F.f ^ F.f) * ((U.block b).round + 1) := by
  classical
  set e := (exposedTo U b).card with he
  have hef : e ≤ F.f := card_exposedTo_le hb
  calc (history U b).card
      = ∑ W ∈ Finset.univ,
          ((history U b).filter fun i => (U.block i).creator = W).card :=
        Finset.card_eq_sum_card_fiberwise (fun i _ => Finset.mem_univ _)
    _ = (∑ W ∈ exposedTo U b,
          ((history U b).filter fun i => (U.block i).creator = W).card)
        + ∑ W ∈ (exposedTo U b)ᶜ,
            ((history U b).filter fun i => (U.block i).creator = W).card :=
        (Finset.sum_add_sum_compl _ _).symm
    _ ≤ (∑ _W ∈ exposedTo U b, (Fintype.card Validator - 1) * F.f ^ (F.f - 1) * ((U.block b).round + 1))
        + ∑ _W ∈ (exposedTo U b)ᶜ, ((U.block b).round + 1) := by
        refine Nat.add_le_add (Finset.sum_le_sum ?_) (Finset.sum_le_sum ?_)
        · intro W hW
          have hWexp : ExposedIn U b W := mem_exposedTo.mp hW
          have hf1 : 1 ≤ F.f :=
            le_trans (Finset.card_pos.mpr ⟨W, hW⟩) (card_exposedTo_le hb)
          refine le_trans (card_filter_creator_le_card_topsOf hdos hb W) ?_
          refine Nat.mul_le_mul_right _ ?_
          refine le_trans (card_topsOf_le_of_exposed hdos hb hWexp) ?_
          have h1 : Fintype.card Validator - (exposedTo U b).card ≤ (Fintype.card Validator - 1) := by
            have : 1 ≤ (exposedTo U b).card := Finset.card_pos.mpr ⟨W, hW⟩
            omega
          have h2 : (exposedTo U b).card ^ ((exposedTo U b).erase W).card
              ≤ F.f ^ (F.f - 1) := by
            have herase : ((exposedTo U b).erase W).card ≤ F.f - 1 := by
              rw [Finset.card_erase_of_mem hW]
              omega
            calc (exposedTo U b).card ^ ((exposedTo U b).erase W).card
                ≤ F.f ^ ((exposedTo U b).erase W).card :=
                  Nat.pow_le_pow_left (card_exposedTo_le hb) _
              _ ≤ F.f ^ (F.f - 1) := Nat.pow_le_pow_right hf1 herase
          exact Nat.mul_le_mul h1 h2
        · intro W hW
          rw [Finset.mem_compl, mem_exposedTo] at hW
          exact card_filter_creator_le hb hW
    _ ≤ ((Fintype.card Validator - 1) * F.f ^ F.f) * ((U.block b).round + 1)
        + (Fintype.card Validator) * ((U.block b).round + 1) := by
        refine Nat.add_le_add ?_ ?_
        · rw [Finset.sum_const_nat (fun _ _ => rfl)]
          rcases Nat.eq_zero_or_pos F.f with hf0 | hf1
          · have he0 : e = 0 := by omega
            rw [← he, he0]
            simp
          · calc e * ((Fintype.card Validator - 1) * F.f ^ (F.f - 1) * ((U.block b).round + 1))
                ≤ F.f * ((Fintype.card Validator - 1) * F.f ^ (F.f - 1) * ((U.block b).round + 1)) :=
                  Nat.mul_le_mul_right _ hef
              _ = ((Fintype.card Validator - 1) * F.f ^ F.f) * ((U.block b).round + 1) := by
                  have hpow : F.f * F.f ^ (F.f - 1) = F.f ^ F.f := by
                    have hsub : F.f - 1 + 1 = F.f := by omega
                    calc F.f * F.f ^ (F.f - 1)
                        = F.f ^ (F.f - 1) * F.f := by ring
                      _ = F.f ^ (F.f - 1 + 1) := (pow_succ F.f (F.f - 1)).symm
                      _ = F.f ^ F.f := by rw [hsub]
                  calc F.f * ((Fintype.card Validator - 1) * F.f ^ (F.f - 1) * ((U.block b).round + 1))
                      = (Fintype.card Validator - 1) * (F.f * F.f ^ (F.f - 1)) * ((U.block b).round + 1) := by
                        ring
                    _ = ((Fintype.card Validator - 1) * F.f ^ F.f) * ((U.block b).round + 1) := by
                        rw [hpow]
        · rw [Finset.sum_const_nat (fun _ _ => rfl), Finset.card_compl]
          refine Nat.mul_le_mul_right _ ?_
          omega
    _ = (Fintype.card Validator + (Fintype.card Validator - 1) * F.f ^ F.f) * ((U.block b).round + 1) := by
        rw [← Nat.add_mul]
        congr 1
        omega

end LeanDag
