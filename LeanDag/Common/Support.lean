import LeanDag.Common.CausalHistory
/-!
# Support and coverage

The common foundation under both persistence (T3) and the common-ancestor
result (T3c). Both rest on one principle:

> If a block is referenced by the round-`(r+1)` blocks of enough **correct**
> validators, every round-`(r+2)` block reaches it.

"Enough" admits two thresholds, and the difference is the only thing
separating the two theorems downstream.

* `reaches_of_honest_support` — threshold `p - 2f`, where `p` is the number
  of validators holding a round-`(r+1)` block. A round-`(r+2)` block draws
  its n−f referenced creators from those same `p`, so it misses exactly
  `p - (n−f)` of them and cannot dodge `p + f + 1 - n` supporters.

* `reaches_of_honest_support_of_card` — threshold `f+1`, uniform. Since
  `p ≤ n` always, this is the corollary: a round-`(r+2)` block names n−f
  of the `n` validators, so it misses at most `f`.

The `f+1` form is the one to reach for when supporters are *assumed* (T3
gets them free: a quorum of n−f distinct creators contains at least `f+1`
correct ones). The `p` form is needed when supporters are *counted* (T3a can
only guarantee `p - 2f`, which is strictly less than `f+1` when `p < 3f+1`).

The two agree: `p - 2f` is `f+1` net of the validators that never produced a
round-`(r+1)` block. Absentees shrink the requirement exactly as fast as they
shrink what counting can deliver, which is why no progress assumption
appears anywhere.

Correctness of the *supporters* is what makes this work: a correct validator
has one round-`(r+1)` block, so naming it is enough to reach what it
references. A Byzantine supporter could hold two, only one of which
references the target.
-/

namespace LeanDag

variable {Validator : Type*} [DecidableEq Validator]
variable {BlockId : Type*} {Payload : Type*}

/-! ## Counting, at any block record -/

section Generic

variable {P : Validity Validator BlockId Payload} {honest : Finset Validator}
variable {U : BlockRecord Validator BlockId Payload P honest}

/-- The ids present at a given round. -/
def blocksAt (U : BlockRecord Validator BlockId Payload P honest) (n : ℕ) : Finset BlockId :=
  U.ids.filter (fun i => (U.block i).round = n)

/-- The distinct authors of the round-`n` blocks in a set of ids — an
image, so an equivocator's duplicates collapse: this counts validators,
not blocks, which is what makes a quorum of it a real quorum. Over
`U.ids` it is `authorsAt`; over a validator's holdings it is the trigger
of the pacemaker's progress rule (`PaceCore.advances`). -/
def authorsIn (U : BlockRecord Validator BlockId Payload P honest)
    (s : Finset BlockId) (n : ℕ) : Finset Validator :=
  creatorsOf U.block (s.filter fun b => (U.block b).round = n)

/-- Membership in `authorsIn`, unfolded. -/
theorem mem_authorsIn {s : Finset BlockId} {v : Validator} {n : ℕ} :
    v ∈ authorsIn U s n ↔ ∃ b ∈ s, (U.block b).round = n ∧ (U.block b).creator = v := by
  simp [authorsIn, mem_creatorsOf]
  tauto

/-- The validators holding a block at a given round — the pool `p`. -/
def authorsAt (U : BlockRecord Validator BlockId Payload P honest) (n : ℕ) : Finset Validator :=
  creatorsOf U.block (blocksAt U n)

/-- `authorsAt` is `authorsIn` over the whole universe: L0's density and
the progress rule's trigger are one measure, read off `U.ids` there and
off a validator's holdings here. -/
theorem authorsAt_eq_authorsIn (U : BlockRecord Validator BlockId Payload P honest) (n : ℕ) :
    authorsAt U n = authorsIn U U.ids n := rfl

/-- Membership in `blocksAt`, unfolded. -/
@[simp]
theorem mem_blocksAt {i : BlockId} {n : ℕ} :
    i ∈ blocksAt U n ↔ i ∈ U.ids ∧ (U.block i).round = n := by
  simp [blocksAt]

/-- Membership in `authorsAt`, unfolded: an author of a round is anyone with a block there. -/
theorem mem_authorsAt {v : Validator} {n : ℕ} :
    v ∈ authorsAt U n ↔ ∃ i ∈ U.ids, (U.block i).round = n ∧ (U.block i).creator = v := by
  simp [authorsAt, mem_creatorsOf]
  tauto

/-- The author pool never exceeds the validator set. This is what turns the
`p - 2f` threshold into the uniform `f+1` one. -/
theorem card_authorsAt_le_univ [Fintype Validator] {n : ℕ} : (authorsAt U n).card ≤ Fintype.card Validator :=
  Finset.card_le_univ (authorsAt U n)

/-- The creators of a round-`(n+1)` block's references all hold round-`n`
blocks. This is what confines a round-`(r+2)` block's choices to the same
pool the threshold is measured against. -/
theorem creators_refs_subset_authorsAt [P.Mechanised] {c : BlockId} {n : ℕ}
    (hc : c ∈ U.ids) (hcr : (U.block c).round = n + 1) :
    creatorsOf U.block (U.block c).refs ⊆ authorsAt U n := by
  intro v hv
  rw [mem_creatorsOf] at hv
  obtain ⟨i, hi_mem, hi_creator⟩ := hv
  rw [mem_authorsAt]
  refine ⟨i, U.complete c hc i hi_mem, ?_, hi_creator⟩
  have := Validity.Mechanised.pred U.block (U.block c) (U.valid c hc) i hi_mem
  omega

variable [DecidableEq BlockId]

/-! ### Votes and omissions -/

/-- The round-`n` blocks that reference `b`: the votes for `b`. -/
def votesFor (U : BlockRecord Validator BlockId Payload P honest) (b : BlockId) (n : ℕ) :
    Finset BlockId :=
  (blocksAt U n).filter (fun q => b ∈ (U.block q).refs)

/-- The round-`n` blocks that do not reference `L`. -/
def omissionsOf (U : BlockRecord Validator BlockId Payload P honest) (L : BlockId) (n : ℕ) :
    Finset BlockId :=
  (blocksAt U n).filter (fun q => L ∉ (U.block q).refs)

theorem mem_votesFor {b q : BlockId} {n : ℕ} :
    q ∈ votesFor U b n ↔ q ∈ U.ids ∧ (U.block q).round = n ∧ b ∈ (U.block q).refs := by
  simp only [votesFor, Finset.mem_filter, mem_blocksAt, and_assoc]

theorem mem_omissionsOf {L q : BlockId} {n : ℕ} :
    q ∈ omissionsOf U L n ↔ q ∈ U.ids ∧ (U.block q).round = n ∧ L ∉ (U.block q).refs := by
  simp only [omissionsOf, Finset.mem_filter, mem_blocksAt, and_assoc]

/-- The validators whose round-`n` block references `b`. -/
def supporters (U : BlockRecord Validator BlockId Payload P honest) (b : BlockId) (n : ℕ) :
    Finset Validator :=
  creatorsOf U.block (votesFor U b n)

/-- Membership in `supporters`, unfolded: a supporter has a round-`n` block referencing `b`. -/
theorem mem_supporters {b : BlockId} {n : ℕ} {v : Validator} :
    v ∈ supporters U b n ↔
      ∃ q ∈ U.ids, (U.block q).round = n ∧ b ∈ (U.block q).refs ∧ (U.block q).creator = v := by
  simp [supporters, votesFor, mem_creatorsOf]
  tauto

theorem supporters_subset_authorsAt {b : BlockId} {n : ℕ} :
    supporters U b n ⊆ authorsAt U n :=
  Finset.image_subset_image (Finset.filter_subset _ _)

/-- The validators whose round-`n` block declines to reference `L`.

The complement of `supporters U L n` *within the round-`n` author pool* —
but only for correct validators. A Byzantine author can appear in both, by
publishing one round-`n` block that votes and another that does not; ruling
that out for correct validators is exactly what
`blames_inter_supporters_subset_byzantine`
does, and is the whole content of M3. -/
def blames (U : BlockRecord Validator BlockId Payload P honest) (L : BlockId) (n : ℕ) :
    Finset Validator :=
  creatorsOf U.block (omissionsOf U L n)

/-- Membership in `blames`, unfolded: a blamer has a round-`n` block that omits `L`. -/
theorem mem_blames {L : BlockId} {n : ℕ} {v : Validator} :
    v ∈ blames U L n ↔
      ∃ q ∈ U.ids, (U.block q).round = n ∧ L ∉ (U.block q).refs ∧ (U.block q).creator = v := by
  simp [blames, omissionsOf, mem_creatorsOf]
  tauto

/-! ### What a view holds

What a validator holds is a view, and a rule judges from it. Every direct
rule of every protocol has one shape: the view holds blocks of some set
from at least `t` distinct authors — the supporters, certifiers or
blamers the validator has actually seen. `heldAuthors` is that count and
`HoldsAtLeast` that predicate. A rule names its set and its threshold;
that the count only grows with the view, that the full view holds
everything, and that a view covering the set's rounds holds all of it
are settled here once. -/

/-- The authors of the blocks of `s` that a view holds. -/
def heldAuthors (U : BlockRecord Validator BlockId Payload P honest) (V : U.View)
    (s : Finset BlockId) : Finset Validator :=
  creatorsOf U.block (s ∩ V.ids)

theorem mem_heldAuthors {V : U.View} {s : Finset BlockId} {v : Validator} :
    v ∈ heldAuthors U V s ↔ ∃ b ∈ s, b ∈ V.ids ∧ (U.block b).creator = v := by
  simp only [heldAuthors, mem_creatorsOf, Finset.mem_inter, and_assoc]

/-- A view can only under-report. -/
theorem heldAuthors_subset {V : U.View} {s : Finset BlockId} :
    heldAuthors U V s ⊆ creatorsOf U.block s :=
  Finset.image_subset_image Finset.inter_subset_left

/-- A larger view holds more. -/
theorem heldAuthors_mono {V V' : U.View} (h : V.ids ⊆ V'.ids) {s : Finset BlockId} :
    heldAuthors U V s ⊆ heldAuthors U V' s :=
  Finset.image_subset_image (Finset.inter_subset_inter_left h)

theorem heldAuthors_mono_set {V : U.View} {s s' : Finset BlockId} (h : s ⊆ s') :
    heldAuthors U V s ⊆ heldAuthors U V s' :=
  Finset.image_subset_image (Finset.inter_subset_inter_right h)

/-- The full view holds everything. -/
theorem heldAuthors_full {s : Finset BlockId} (hs : s ⊆ U.ids) :
    heldAuthors U (View.full U) s = creatorsOf U.block s := by
  unfold heldAuthors
  rw [View.full_ids, Finset.inter_eq_left.mpr hs]

/-- A view covering the rounds of `s` holds all of `s`. -/
theorem heldAuthors_of_coversUpto {V : U.View} {s : Finset BlockId} {N : ℕ}
    (hs : ∀ b ∈ s, b ∈ U.ids ∧ (U.block b).round ≤ N) (hcov : V.CoversUpto N) :
    heldAuthors U V s = creatorsOf U.block s := by
  unfold heldAuthors
  rw [Finset.inter_eq_left.mpr fun b hb => hcov b (hs b hb).1 (hs b hb).2]

/-- **A view holds blocks of `s` from at least `t` distinct authors.** -/
def HoldsAtLeast (U : BlockRecord Validator BlockId Payload P honest) (V : U.View)
    (t : ℕ) (s : Finset BlockId) : Prop :=
  t ≤ (heldAuthors U V s).card

instance decidableHoldsAtLeast (V : U.View) (t : ℕ) (s : Finset BlockId) :
    Decidable (HoldsAtLeast U V t s) :=
  inferInstanceAs (Decidable (t ≤ (heldAuthors U V s).card))

namespace HoldsAtLeast

variable {V V' : U.View} {t t' : ℕ} {s s' : Finset BlockId}

/-- What a view holds, the record has: the rule at the record follows. -/
theorem le (h : HoldsAtLeast U V t s) : t ≤ (creatorsOf U.block s).card :=
  le_trans h (Finset.card_le_card heldAuthors_subset)

/-- A larger view holds it still. -/
theorem mono (hV : V.ids ⊆ V'.ids) (h : HoldsAtLeast U V t s) : HoldsAtLeast U V' t s :=
  le_trans h (Finset.card_le_card (heldAuthors_mono hV))

theorem of_subset (hs : s ⊆ s') (h : HoldsAtLeast U V t s) : HoldsAtLeast U V t s' :=
  le_trans h (Finset.card_le_card (heldAuthors_mono_set hs))

theorem of_le (ht : t' ≤ t) (h : HoldsAtLeast U V t s) : HoldsAtLeast U V t' s :=
  le_trans ht h

/-- The full view holds it exactly when the record does. -/
theorem full (hs : s ⊆ U.ids) :
    HoldsAtLeast U (View.full U) t s ↔ t ≤ (creatorsOf U.block s).card := by
  unfold HoldsAtLeast; rw [heldAuthors_full hs]

/-- A view covering the rounds of `s` holds what the record does. -/
theorem of_coversUpto {N : ℕ} (hs : ∀ b ∈ s, b ∈ U.ids ∧ (U.block b).round ≤ N)
    (hcov : V.CoversUpto N) (h : t ≤ (creatorsOf U.block s).card) : HoldsAtLeast U V t s := by
  unfold HoldsAtLeast; rwa [heldAuthors_of_coversUpto hs hcov]

end HoldsAtLeast

/-! ### Counted in a view

The supporters and blamers a view holds: the record's counts at the view
read as a record (`supportersIn_eq_toRecord`). -/

/-- The supporters of `b` at round `n` that a view holds. -/
def supportersIn (U : BlockRecord Validator BlockId Payload P honest) (V : U.View)
    (b : BlockId) (n : ℕ) : Finset Validator :=
  heldAuthors U V (votesFor U b n)

/-- The blamers of `L` at round `n` that a view holds. -/
def blamesIn (U : BlockRecord Validator BlockId Payload P honest) (V : U.View)
    (L : BlockId) (n : ℕ) : Finset Validator :=
  heldAuthors U V (omissionsOf U L n)

theorem mem_supportersIn {V : U.View} {b : BlockId} {n : ℕ} {v : Validator} :
    v ∈ supportersIn U V b n ↔
      ∃ q ∈ V.ids, (U.block q).round = n ∧ b ∈ (U.block q).refs ∧ (U.block q).creator = v := by
  simp only [supportersIn, mem_heldAuthors, mem_votesFor]
  constructor
  · rintro ⟨q, ⟨_, hr, hb⟩, hV, hc⟩; exact ⟨q, hV, hr, hb, hc⟩
  · rintro ⟨q, hV, hr, hb, hc⟩; exact ⟨q, ⟨V.subset_ids hV, hr, hb⟩, hV, hc⟩

theorem mem_blamesIn {V : U.View} {L : BlockId} {n : ℕ} {v : Validator} :
    v ∈ blamesIn U V L n ↔
      ∃ q ∈ V.ids, (U.block q).round = n ∧ L ∉ (U.block q).refs ∧ (U.block q).creator = v := by
  simp only [blamesIn, mem_heldAuthors, mem_omissionsOf]
  constructor
  · rintro ⟨q, ⟨_, hr, hb⟩, hV, hc⟩; exact ⟨q, hV, hr, hb, hc⟩
  · rintro ⟨q, hV, hr, hb, hc⟩; exact ⟨q, ⟨V.subset_ids hV, hr, hb⟩, hV, hc⟩

/-- The view's count is the record's count at the view as a record. -/
theorem supportersIn_eq_toRecord {V : U.View} {b : BlockId} {n : ℕ} :
    supportersIn U V b n = supporters V.toRecord b n := by
  ext v
  rw [mem_supportersIn, mem_supporters]
  rfl

theorem blamesIn_eq_toRecord {V : U.View} {L : BlockId} {n : ℕ} :
    blamesIn U V L n = blames V.toRecord L n := by
  ext v
  rw [mem_blamesIn, mem_blames]
  rfl

end Generic

/-! ## The hitting lemma, and coverage

At any quorate record. Both rest on one principle:

> If a block is referenced by the round-`(r+1)` blocks of enough
> **honest** validators, every round-`(r+2)` block reaches it.

"Enough" admits two thresholds. The participation-sensitive form counts
against the round-`(r+1)` author pool `p`: a round-`(r+2)` block draws
its `q` referenced creators from that pool, so it misses at most `p − q`
of them and cannot dodge `p − q + 1` backers. The uniform form is its
corollary at `p ≤ n`: more than `n − q` backers always suffice, which
for the core's `q = n − f` is the familiar `f + 1`.

Honesty of the *supporters* is what makes this work: an honest validator
has one round-`(r+1)` block, so naming it is enough to reach what it
references. A Byzantine supporter could hold two, only one of which
references the target. -/

section Quorate

variable {P : Validity Validator BlockId Payload} {honest : Finset Validator}
variable {q : ℕ} [P.Quorate q] [P.Mechanised]
variable {U : BlockRecord Validator BlockId Payload P honest}

/-- **The hitting lemma.** A round-`(n+1)` block cannot avoid referencing a
block satisfying `Q`, once enough honest validators have published
round-`n` blocks satisfying it.

This is the primitive under both coverage and M2. It is stated with `Q` a
bare predicate rather than a `Finset BlockId` because nothing here takes the
cardinality of the target set — only of `T`, the validators backing it —
which keeps the whole file free of `DecidableEq BlockId`. -/
theorem exists_mem_refs_of_honest_support
    {Q : BlockId → Prop} {n : ℕ} {T : Finset Validator}
    (hT : ∀ v ∈ T, ∃ b ∈ U.ids, (U.block b).round = n ∧ Q b ∧ (U.block b).creator = v)
    (hT_honest : ∀ v ∈ T, v ∈ honest)
    (hp : (authorsAt U n).card + 1 ≤ T.card + q)
    {c : BlockId} (hc : c ∈ U.ids) (hcr : (U.block c).round = n + 1) :
    ∃ b ∈ (U.block c).refs, Q b := by
  set A := creatorsOf U.block (U.block c).refs with hA
  have hA_quorum : q ≤ A.card := U.creators_quorum hc (by omega)
  have hA_sub : A ⊆ authorsAt U n := creators_refs_subset_authorsAt hc hcr
  have hT_auth : T ⊆ authorsAt U n := by
    intro v hv
    obtain ⟨b, hb_ids, hb_round, _, hb_creator⟩ := hT v hv
    rw [mem_authorsAt]
    exact ⟨b, hb_ids, hb_round, hb_creator⟩
  have hunion : (A ∪ T).card ≤ (authorsAt U n).card :=
    Finset.card_le_card (Finset.union_subset hA_sub hT_auth)
  have hadd := Finset.card_union_add_card_inter A T
  have hinter : 0 < (A ∩ T).card := by omega
  obtain ⟨v, hv⟩ := Finset.card_pos.mp hinter
  rw [Finset.mem_inter] at hv
  obtain ⟨hv_A, hv_T⟩ := hv
  rw [hA, mem_creatorsOf] at hv_A
  obtain ⟨i, hi_mem, hi_creator⟩ := hv_A
  obtain ⟨b, hb_ids, hb_round, hb_Q, hb_creator⟩ := hT v hv_T
  have hi_ids : i ∈ U.ids := U.complete c hc i hi_mem
  have hi_round : (U.block i).round = n := by
    have := U.round_of_mem_refs hc hi_mem
    omega
  have hib : i = b :=
    U.eq_of_creator_eq hi_ids hb_ids (hT_honest v hv_T) hi_creator hb_creator
      (by rw [hi_round, hb_round])
  exact ⟨i, hi_mem, hib ▸ hb_Q⟩

/-- **The hitting lemma, uniform form.** More than `n − q` honest backers
always suffice: a round-`(n+1)` block names `q` of at most `n`
participating authors, so it misses at most `n − q`. -/
theorem exists_mem_refs_of_honest_support_of_card [Fintype Validator]
    {Q : BlockId → Prop} {n : ℕ} {T : Finset Validator}
    (hT : ∀ v ∈ T, ∃ b ∈ U.ids, (U.block b).round = n ∧ Q b ∧ (U.block b).creator = v)
    (hT_honest : ∀ v ∈ T, v ∈ honest)
    (hcard : Fintype.card Validator < T.card + q)
    {c : BlockId} (hc : c ∈ U.ids) (hcr : (U.block c).round = n + 1) :
    ∃ b ∈ (U.block c).refs, Q b := by
  refine exists_mem_refs_of_honest_support hT hT_honest ?_ hc hcr
  have := card_authorsAt_le_univ (U := U) (n := n)
  omega

/-- **Propagation.** Reaching something is inherited upward: if every block
at round `N` reaches a `Q`-block, so does every block above `N`.

Shared by T3 and M2, both of which are otherwise just a base case. The step
needs nothing but nonempty references and transitivity — height is carried
by `Reaches` alone. -/
theorem reaches_pred_of_round_le {q : ℕ} [P.Quorate q] {Q : BlockId → Prop} {N : ℕ}
    (hbase : ∀ c ∈ U.ids, (U.block c).round = N → ∃ b, Q b ∧ Reaches U c b)
    {c : BlockId} (hc : c ∈ U.ids) (hcr : N ≤ (U.block c).round) :
    ∃ b, Q b ∧ Reaches U c b := by
  suffices H : ∀ m, ∀ c ∈ U.ids, (U.block c).round = m → N ≤ m → ∃ b, Q b ∧ Reaches U c b by
    exact H _ c hc rfl hcr
  clear hcr hc c
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro c hc hcm hNm
    rcases eq_or_lt_of_le hNm with heq | hlt
    · exact hbase c hc (by omega)
    · obtain ⟨i, hi_mem⟩ := U.refs_nonempty hc (by omega)
      have hi_ids : i ∈ U.ids := U.complete c hc i hi_mem
      have hi_round := U.round_of_mem_refs hc hi_mem
      obtain ⟨b, hQb, hreach⟩ := ih (U.block i).round (by omega) i hi_ids rfl (by omega)
      exact ⟨b, hQb, Reaches.of_mem_refs hi_mem hreach⟩

/-- **Coverage, participation-sensitive form.** A block backed by
`p − q + 1` honest round-`(r+1)` validators is reached by every
round-`(r+2)` block. The `Q`-instance of the hitting lemma where every
target references `b`. -/
theorem reaches_of_honest_support
    {b : BlockId} {r : ℕ} {S : Finset Validator}
    (hS_support : ∀ v ∈ S, ∃ b' ∈ U.ids,
      (U.block b').round = r + 1 ∧ b ∈ (U.block b').refs ∧ (U.block b').creator = v)
    (hS_honest : ∀ v ∈ S, v ∈ honest)
    (hp : (authorsAt U (r + 1)).card + 1 ≤ S.card + q)
    {c : BlockId} (hc : c ∈ U.ids) (hcr : (U.block c).round = r + 2) :
    Reaches U c b := by
  obtain ⟨b', hb'_mem, hb'_ref⟩ :=
    exists_mem_refs_of_honest_support (Q := fun b' => b ∈ (U.block b').refs)
      hS_support hS_honest hp hc (by omega)
  exact Reaches.of_mem_refs hb'_mem (Reaches.single hb'_ref)

/-- **Coverage, uniform form.** More than `n − q` honest supporters
always suffice. This is the form to use when supporters come from a
quorum rather than from counting — see T3, where `n − f` distinct
creators contain `f + 1` correct ones by `card_inter_correct_of_quorum`. -/
theorem reaches_of_honest_support_of_card [Fintype Validator]
    {b : BlockId} {r : ℕ} {S : Finset Validator}
    (hS_support : ∀ v ∈ S, ∃ b' ∈ U.ids,
      (U.block b').round = r + 1 ∧ b ∈ (U.block b').refs ∧ (U.block b').creator = v)
    (hS_honest : ∀ v ∈ S, v ∈ honest)
    (hcard : Fintype.card Validator < S.card + q)
    {c : BlockId} (hc : c ∈ U.ids) (hcr : (U.block c).round = r + 2) :
    Reaches U c b := by
  refine reaches_of_honest_support hS_support hS_honest ?_ hc hcr
  have := card_authorsAt_le_univ (U := U) (n := r + 1)
  omega

end Quorate

section Core

variable [Fintype Validator] [F : Faults Validator]
variable {U : BlockUniverse Validator BlockId Payload}

/-! ## Support sets

The coverage lemmas above take their support set as a bare `Finset Validator`
so they stay instance-free. These are the concrete sets callers build, and
forming them needs decidable equality on ids.

Mysticeti's *voters* for a leader block are exactly `supporters` at the
following round, which is why these sit here rather than beside the counting
argument that first used them. -/

variable [DecidableEq BlockId]

/-- Validators that are both correct and back `b` with their round-`n`
block. This is exactly what the coverage lemmas consume. -/
def correctSupporters (U : BlockUniverse Validator BlockId Payload) (b : BlockId) (n : ℕ) :
    Finset Validator :=
  supporters U b n ∩ (Correct : Finset Validator)

/-- Correct supporters are supporters. -/
theorem correctSupporters_subset {b : BlockId} {n : ℕ} :
    correctSupporters U b n ⊆ supporters U b n := Finset.inter_subset_left

/-- And they are correct. -/
theorem correctSupporters_correct {b : BlockId} {n : ℕ} {v : Validator}
    (hv : v ∈ correctSupporters U b n) : v ∈ (Correct : Finset Validator) :=
  Finset.mem_of_mem_inter_right hv


/-- A correct validator cannot both vote for `L` and blame it: that would be
two distinct round-`n` blocks by one correct author. So the overlap between
blamers and supporters is confined to the Byzantine set.

This is the only place non-equivocation enters M3, and it is what stops a
Byzantine author from being counted on both sides of the ledger. -/
theorem blames_inter_supporters_subset_byzantine {L : BlockId} {n : ℕ} :
    blames U L n ∩ supporters U L n ⊆ F.byzantine := by
  intro v hv
  rw [Finset.mem_inter] at hv
  obtain ⟨hb, hs⟩ := hv
  obtain ⟨q, hq_ids, hq_round, hq_noref, hq_creator⟩ := mem_blames.mp hb
  obtain ⟨q', hq'_ids, hq'_round, hq'_ref, hq'_creator⟩ := mem_supporters.mp hs
  by_contra hcorrect
  -- If `v` were correct, `q` and `q'` would be the same block — but one
  -- references `L` and the other does not.
  have hv_correct : v ∈ (Correct : Finset Validator) := by simpa using hcorrect
  have : q = q' :=
    U.eq_of_creator_eq hq_ids hq'_ids hv_correct hq_creator hq'_creator
      (by rw [hq_round, hq'_round])
  exact hq_noref (this ▸ hq'_ref)

/-- **The counting core of M3.** A quorum of blamers caps the supporters at
`2f`, one short of a quorum.

A correct validator sits on at most one side, so the overlap is confined to
the Byzantine set: `|supporters| ≤ (3f+1) − (2f+1) + f = 2f`. Nothing about
certificates enters, which is why this belongs here rather than beside the
commit rules that consume it. -/
theorem card_supporters_le_of_card_blames {L : BlockId} {n : ℕ}
    (h : quorumCard Validator ≤ (blames U L n).card) :
    (supporters U L n).card ≤ 2 * F.f := by
  have hunion : (blames U L n ∪ supporters U L n).card ≤ Fintype.card Validator := by
    have := Finset.card_le_univ (blames U L n ∪ supporters U L n)
    have := F.card_validators
    omega
  have hinter : (blames U L n ∩ supporters U L n).card ≤ F.f :=
    le_trans (Finset.card_le_card blames_inter_supporters_subset_byzantine) F.card_byzantine
  have hadd := Finset.card_union_add_card_inter (blames U L n) (supporters U L n)
  omega

end Core

end LeanDag
