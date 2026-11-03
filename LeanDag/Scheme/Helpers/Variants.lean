import LeanDag.Scheme.Model.Variants
import LeanDag.Scheme.Helpers.Rows
/-!
# Cordial Miners PS and the scheme's Nemo-Nemo: laws and readings

`cordialAnchored` takes the core's laws, the skip cases being empty.
`nemoBlameAnchored` takes Nemo's, and its skip cases are one fact: a
vote-round block of every validator references no candidate, and no
validator has two blocks at a round, so no vote for the candidate exists
for a commit or a link to read. Each is read by its row of the scheme.
-/

namespace LeanDag

namespace Scheme

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [LinearOrder BlockId] {Payload : Type}
variable [S : Slots Validator]

omit S in
/-- Every validator among a set's held authors: each has a block in it. -/
theorem exists_mem_of_card {P : Validity Validator BlockId Payload}
    {honest : Finset Validator} {U : BlockRecord Validator BlockId Payload P honest}
    {V : U.View} {s : Finset BlockId} (hs : HoldsAtLeast U V (Fintype.card Validator) s)
    (v : Validator) : ∃ b ∈ s, (U.block b).creator = v := by
  have huniv : heldAuthors U V s = Finset.univ :=
    Finset.eq_univ_of_card _ (le_antisymm (Finset.card_le_univ _) hs)
  obtain ⟨b, hb, -, hbc⟩ := mem_heldAuthors.mp (huniv ▸ Finset.mem_univ v)
  exact ⟨b, hb, hbc⟩

omit [Fintype Validator] S in
/-- **A rule without its direct skip keeps its laws**: the skip cases are
empty. -/
theorem laws_dropSkip {P : Validity Validator BlockId Payload} {honest : Finset Validator}
    {R : AnchoredRule Validator BlockId Payload P honest}
    {I : Slots Validator → BlockRecord Validator BlockId Payload P honest → Prop}
    (hl : R.Laws I) : ({ R with Skip := fun _ _ _ _ => False } :
      AnchoredRule Validator BlockId Payload P honest).Laws I where
  commit_unique := hl.commit_unique
  commit_skip := fun _ _ _ h => h.elim
  commit_link := hl.commit_link
  commit_link_unique := hl.commit_link_unique
  skip_link := fun _ h _ _ _ => h.elim
  link_unique := hl.link_unique
  commit_mono := hl.commit_mono
  skip_mono := fun _ _ h => h
  skip_congr := fun _ _ _ _ h => h
  link_congr := hl.link_congr
  anchor_commit := hl.anchor_commit
  anchor_link := hl.anchor_link

section Cordial

variable [F : Faults Validator]

/-- **On the core's universe no slot is blamed by every validator**: the
leader's own vote-round block references its previous block. -/
theorem not_holdsAtLeast_card_slotBlamers (U : BlockUniverse Validator BlockId Payload)
    (V : U.View) (k : ℕ) :
    ¬ HoldsAtLeast U V (Fintype.card Validator) (slotBlamers U k) := by
  intro h
  obtain ⟨b, hb, hbc⟩ := exists_mem_of_card h (S.leader k)
  obtain ⟨hbU, hbr, hbl⟩ := mem_slotBlamers.mp hb
  obtain ⟨i, hi, hic⟩ := (U.valid b hbU).self_parent (by omega)
  have hir := (U.valid b hbU).predecessor i hi
  exact hbl i hi ⟨U.complete b hbU i hi, by omega, by rw [hic, hbc]⟩

omit S in
/-- **Cordial Miners PS has the core's laws.** -/
theorem cordialLaws : (cordialAnchored Validator BlockId Payload).Laws :=
  laws_dropSkip coreLaws

/-- **The Cordial Miners PS row reads as `cordialAnchored`**: its skip
threshold `n` is never met on the core's universe. -/
theorem readAlike_cordial (σ : VoteSel Validator BlockId Payload ValidWrt Correct)
    (U : BlockUniverse Validator BlockId Payload) :
    ReadAlike (schemeAnchored (Params.cordialMinersPS (Fintype.card Validator) F.f) σ)
      (cordialAnchored Validator BlockId Payload) U where
  waveAt := fun _ => rfl
  rungs := rfl
  commit := fun V k L hL => by
    change HoldsAtLeast U V _ (certsAt _ σ U L _) ↔ HoldsAtLeast U V _ _
    rw [certsAt_eq_certificatesAt σ _ rfl rfl distinctRefs hL.2.1]
    rfl
  skip := fun V k => by
    change HoldsAtLeast U V _ (blamersAt _ σ U k) ↔ False
    rw [blamersAt_eq σ _ rfl k]
    exact iff_false_intro (not_holdsAtLeast_card_slotBlamers U V k)
  link := fun {i k j A L} _ hL hA _ => by
    change _ ≤ (creatorsOf U.block ((certsAt _ σ U L _).filter _)).card ↔ LinkedVia U A _
    rw [certsAt_eq_certificatesAt σ _ rfl rfl distinctRefs hL.2.1]
    exact one_le_card_iff_linkedVia hA.1 _
  least := fun {i k j A L} hi hL hA he hl => by
    have hi0 : i = 0 := by simp only [schemeAnchored] at hi; omega
    subst hi0
    have hlink : ∀ {L'}, IsLeaderBlock U k L' →
        ((schemeAnchored (Params.cordialMinersPS (Fintype.card Validator) F.f) σ).Link 0 U A L'
          S k ↔ (coreAnchored Validator BlockId Payload).Link 0 U A L' S k) := fun hL' => by
      change _ ≤ (creatorsOf U.block ((certsAt _ σ U _ _).filter _)).card ↔ LinkedVia U A _
      rw [certsAt_eq_certificatesAt σ _ rfl rfl distinctRefs hL'.2.1]
      exact one_le_card_iff_linkedVia hA.1 _
    constructor
    · exact fun _ _ _ _ h => h
    · intro _ L' hL' hl' hlt
      have heq := (coreLaws (Validator := Validator) (BlockId := BlockId)
        (Payload := Payload)).link_unique (S := S) (U := U) (i := 0) trivial hL hL' hA trivial he
        Nat.one_pos (fun _ h => absurd h (Nat.not_lt_zero _)) ((hlink hL).mp hl)
        ((hlink hL').mp hl') (fun _ _ _ h => h) (fun _ _ _ h => h)
      exact lt_irrefl L (heq ▸ hlt)

end Cordial

section Nemo

/-- Nemo's universe: no validator has two blocks at a round, so references
name distinct authors. -/
theorem distinctRefs_nemo {U : Nemo.Universe Validator BlockId Payload} :
    ∀ b ∈ U.ids, DistinctRefs U b := fun b hb i hi j hj hc =>
  U.no_equivocation i (U.complete b hb i hi) j (U.complete b hb j hj) (Finset.mem_univ _) hc
    (by have := (U.valid b hb).predecessor i hi; have := (U.valid b hb).predecessor j hj; omega)

/-- **A blame from every validator leaves no vote**: any round-`r + 1` block
referencing a candidate shares its author with a blaming block, and so is
that block. -/
theorem not_vote_of_card_blame {U : Nemo.Universe Validator BlockId Payload}
    {V : U.View} {k : ℕ} {L q : BlockId}
    (hs : HoldsAtLeast U V (Fintype.card Validator) (slotBlamers U k))
    (hL : IsLeaderBlock U k L) (hq : q ∈ U.ids) (hqr : (U.block q).round = S.slotRound k + 1)
    (hqL : L ∈ (U.block q).refs) : False := by
  obtain ⟨b, hb, hbc⟩ := exists_mem_of_card hs (U.block q).creator
  obtain ⟨hbU, hbr, hbl⟩ := mem_slotBlamers.mp hb
  have : b = q := U.no_equivocation b hbU q hq (Finset.mem_univ _) hbc (by omega)
  subst this
  exact hbl L hqL hL

omit S in
/-- **The scheme's Nemo-Nemo has Nemo's laws**, with its direct skip. -/
theorem nemoBlameLaws : (nemoBlameAnchored Validator BlockId Payload).Laws where
  commit_unique := fun _ hL₁ hL₂ _ _ =>
    isLeaderBlock_unique_of_honest (Finset.mem_univ _) hL₁ hL₂
  commit_skip := by
    intro S U V₁ V₂ k L _ hL hc hs
    obtain ⟨v, hv⟩ : (heldAuthors U V₁ (votesFor U L (S.slotRound k + 1))).Nonempty := by
      rw [← Finset.card_pos]
      exact lt_of_lt_of_le (Nat.succ_pos _) hc
    obtain ⟨q, hq, -, -⟩ := mem_heldAuthors.mp hv
    obtain ⟨hqU, hqr, hqL⟩ := mem_votesFor.mp hq
    exact not_vote_of_card_blame hs hL hqU hqr hqL
  commit_link := fun hI hL h hA _ helig =>
    (Nemo.nemoLaws (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload)).commit_link hI hL h hA trivial helig
  commit_link_unique := fun _ hL₁ hL₂ _ _ _ _ _ _ _ _ =>
    isLeaderBlock_unique_of_honest (Finset.mem_univ _) hL₁ hL₂
  skip_link := by
    intro S U V k i L A _ hs hL _ hA hl
    obtain ⟨q, hq, hqr, hqL⟩ := hl
    exact not_vote_of_card_blame hs hL (history_subset_ids hA hq) hqr hqL
  link_unique := fun _ hL₁ hL₂ _ _ _ _ _ _ _ _ _ =>
    isLeaderBlock_unique_of_honest (Finset.mem_univ _) hL₁ hL₂
  commit_mono := fun _ hsub h => HoldsAtLeast.mono hsub h
  skip_mono := fun _ hsub h => HoldsAtLeast.mono hsub h
  skip_congr := by
    intro S₁ S₂ U V k _ hround hk _ h
    change HoldsAtLeast U V _ (slotBlamers (S := S₂) U k)
    rwa [← slotBlamers_congr hround hk]
  link_congr := (nemoBlameAnchored Validator BlockId Payload).linkCongr_of_round
    (fun _ U A L r => Nemo.CertifiedIn U A L r) fun _ _ _ _ _ _ => rfl
  anchor_commit := fun _ hL _ => hL.1
  anchor_link := fun _ _ _ _ hL _ _ => hL.1

/-- **The Nemo-Nemo row reads as `nemoBlameAnchored`** at `n = 2c + 1`,
where its commit threshold `n − c` is Nemo's majority. -/
theorem readAlike_nemo (σ : VoteSel Validator BlockId Payload Nemo.ValidWrt Finset.univ)
    (U : Nemo.Universe Validator BlockId Payload) {c : ℕ}
    (hn : Fintype.card Validator = 2 * c + 1) :
    ReadAlike (schemeAnchored (Params.nemoNemo (Fintype.card Validator) c) σ)
      (nemoBlameAnchored Validator BlockId Payload) U where
  waveAt := fun _ => rfl
  rungs := rfl
  commit := fun V k L hL => by
    change HoldsAtLeast U V _ (certsAt _ σ U L _) ↔ HoldsAtLeast U V _ _
    rw [certsAt_eq_votesFor σ _ rfl rfl distinctRefs_nemo hL.2.1]
    change HoldsAtLeast U V (Fintype.card Validator - c) _ ↔
      HoldsAtLeast U V (Fintype.card Validator / 2 + 1) _
    rw [show Fintype.card Validator - c = Fintype.card Validator / 2 + 1 by omega]
  skip := fun V k => by
    change HoldsAtLeast U V _ (blamersAt _ σ U k) ↔ HoldsAtLeast U V _ _
    rw [blamersAt_eq σ _ rfl k]
    rfl
  link := fun {i k j A L} _ hL hA _ => by
    change _ ≤ (creatorsOf U.block ((certsAt _ σ U L _).filter _)).card ↔
      ∃ p ∈ history U A, (U.block p).round = S.slotRound k + 1 ∧ L ∈ (U.block p).refs
    rw [certsAt_eq_votesFor σ _ rfl rfl distinctRefs_nemo hL.2.1]
    change 1 ≤ _ ↔ _
    rw [Nat.one_le_iff_ne_zero, Ne,
      Finset.card_eq_zero, ← Ne, ← Finset.nonempty_iff_ne_empty, creatorsOf,
      Finset.image_nonempty]
    constructor
    · rintro ⟨q, hq⟩
      obtain ⟨hqv, hqh⟩ := Finset.mem_filter.mp hq
      obtain ⟨-, hqr, hqL⟩ := mem_votesFor.mp hqv
      exact ⟨q, hqh, hqr, hqL⟩
    · rintro ⟨q, hqh, hqr, hqL⟩
      exact ⟨q, Finset.mem_filter.mpr
        ⟨mem_votesFor.mpr ⟨history_subset_ids hA.1 hqh, hqr, hqL⟩, hqh⟩⟩
  least := fun {i k j A L} _ hL _ _ _ =>
    ⟨fun _ _ _ _ h => h, fun _ L' hL' _ hlt =>
      lt_irrefl L ((isLeaderBlock_unique_of_honest (Finset.mem_univ _) hL hL') ▸ hlt)⟩

end Nemo

end Scheme

end LeanDag
