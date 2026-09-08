import LeanDag.SafeSkip.Basic
/-!
# Round jumping: the fill is derived, not transmitted

A slow validator at round `r` that sights a quorum at round `R ≫ r`
wants its next block at `R + 1` without first authoring one block per
gap round. The pacemaker already permits the jump (P11, report §6.11),
but P3′ pins the DAG: a block at `R + 1` must reference a block by its
own creator at round `R`, and the laggard has none. Safe Skip closes
that gap, and report §12.5 claims its message "needs to carry nothing
but the target's name" — this file makes the claim a theorem, in three
steps.

SS8 says the donor line is not free data: P2 makes the self-parent a
function, so the chain pinned by the message's target block is the
only line satisfying a `SkipMsg`'s clauses. SS9 says the denotation is
a function of the compact core: two messages naming the same anchor and
target, drawing fresh identifiers from the same supply, denote
observationally equal universes. SS10 says every receiver derives the
same fill locally, since views are closed downward and share
`U.block` — the pattern of I11 (report §16.6), where a re-genesis block
is derived rather than transmitted, priced here for the whole fill.

`JumpMsg` is the compact message — `(v1, B1, v2, B2)` plus the
fresh-identifier supply — and `JumpMsg.denote` is the round jump:
elaborate the line, fill the gap, produce at `R + 1`. Everything proved
of a fill (SS1–SS6) applies to it verbatim, since `denote` *is* a
`skipFill`.

What is not claimed: the logical universe still grows by one block per
gap round, so the counting results of report §8 and §9 read unchanged.
The theorems price the wire and the derivation, not the denotation.
-/

namespace LeanDag

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type*} {Payload : Type*}
variable {U : BlockUniverse Validator BlockId Payload}

/-! ## The self-parent function

P3′ supplies a reference by the block's own creator; P2 forbids a
second one, making "the self-parent" well defined, extracted here as a
function total with junk off the good case. -/

/-- The self-parent of a block: its unique reference by its own
creator. Total, with the block itself as junk value when no such
reference exists (a genesis block, or an identifier outside the
universe); every lemma below assumes the good case. -/
noncomputable def selfParent (U : BlockUniverse Validator BlockId Payload)
    (b : BlockId) : BlockId :=
  if h : ∃ i ∈ (U.block b).refs, (U.block i).creator = (U.block b).creator then
    h.choose
  else b

section SelfParent

variable {b : BlockId}

private theorem selfParent_spec (hb : b ∈ U.ids) (h0 : 0 < (U.block b).round) :
    selfParent U b ∈ (U.block b).refs ∧
      (U.block (selfParent U b)).creator = (U.block b).creator := by
  have h := (U.valid b hb).self_parent h0
  rw [selfParent, dif_pos h]
  exact h.choose_spec

/-- The self-parent is a reference of its block. -/
theorem selfParent_mem_refs (hb : b ∈ U.ids) (h0 : 0 < (U.block b).round) :
    selfParent U b ∈ (U.block b).refs :=
  (selfParent_spec hb h0).1

/-- The self-parent carries the block's own creator. -/
theorem selfParent_creator (hb : b ∈ U.ids) (h0 : 0 < (U.block b).round) :
    (U.block (selfParent U b)).creator = (U.block b).creator :=
  (selfParent_spec hb h0).2

/-- The self-parent is in the universe. -/
theorem selfParent_mem_ids (hb : b ∈ U.ids) (h0 : 0 < (U.block b).round) :
    selfParent U b ∈ U.ids :=
  U.complete b hb _ (selfParent_mem_refs hb h0)

/-- The self-parent sits one round below its block. -/
theorem selfParent_round (hb : b ∈ U.ids) (h0 : 0 < (U.block b).round) :
    (U.block (selfParent U b)).round + 1 = (U.block b).round :=
  (U.valid b hb).predecessor _ (selfParent_mem_refs hb h0)

/-- **The crux: the self-parent is unique.** P2 collapses any reference
carrying the block's own creator onto `selfParent`. This is what turns
a `SkipMsg`'s donor line from data into a derived object. -/
theorem eq_selfParent_of_mem (hb : b ∈ U.ids) (h0 : 0 < (U.block b).round)
    {j : BlockId} (hj : j ∈ (U.block b).refs)
    (hjc : (U.block j).creator = (U.block b).creator) : j = selfParent U b :=
  (U.valid b hb).distinct_creators j hj _ (selfParent_mem_refs hb h0)
    (hjc.trans (selfParent_creator hb h0).symm)

end SelfParent

/-! ## The derived line -/

/-- The self-parent chain below `B2`, indexed by round: `lineOf U B2 k`
is the ancestor of `B2` at round `k` on its self-parent line. Junk
above `B2`'s round or off a valid chain, as usual. -/
noncomputable def lineOf (U : BlockUniverse Validator BlockId Payload)
    (B2 : BlockId) (k : ℕ) : BlockId :=
  (selfParent U)^[(U.block B2).round - k] B2

section LineOf

variable {B2 : BlockId} {k : ℕ}

private theorem lineOf_aux (hB2 : B2 ∈ U.ids) :
    ∀ d, d ≤ (U.block B2).round →
      (selfParent U)^[d] B2 ∈ U.ids ∧
        (U.block ((selfParent U)^[d] B2)).creator = (U.block B2).creator ∧
        (U.block ((selfParent U)^[d] B2)).round + d = (U.block B2).round := by
  intro d
  induction d with
  | zero => intro _; exact ⟨hB2, rfl, rfl⟩
  | succ n ih =>
      intro hd
      obtain ⟨hmem, hcr, hrd⟩ := ih (by omega)
      have h0 : 0 < (U.block ((selfParent U)^[n] B2)).round := by omega
      rw [Function.iterate_succ_apply']
      refine ⟨selfParent_mem_ids hmem h0,
        (selfParent_creator hmem h0).trans hcr, ?_⟩
      have := selfParent_round hmem h0
      omega

/-- The derived line stays in the universe. -/
theorem lineOf_mem (hB2 : B2 ∈ U.ids) (hk : k ≤ (U.block B2).round) :
    lineOf U B2 k ∈ U.ids :=
  (lineOf_aux hB2 ((U.block B2).round - k) (by omega)).1

/-- The derived line carries `B2`'s creator throughout. -/
theorem lineOf_creator (hB2 : B2 ∈ U.ids) (hk : k ≤ (U.block B2).round) :
    (U.block (lineOf U B2 k)).creator = (U.block B2).creator :=
  (lineOf_aux hB2 ((U.block B2).round - k) (by omega)).2.1

/-- The derived line's block at index `k` sits at round `k`. -/
theorem lineOf_round (hB2 : B2 ∈ U.ids) (hk : k ≤ (U.block B2).round) :
    (U.block (lineOf U B2 k)).round = k := by
  have := (lineOf_aux hB2 ((U.block B2).round - k) (by omega)).2.2
  unfold lineOf
  omega

/-- The line tops out at `B2` itself. -/
@[simp] theorem lineOf_top : lineOf U B2 (U.block B2).round = B2 := by
  simp [lineOf]

/-- Peeling one step: the line at `k - 1` is the self-parent of the
line at `k`. -/
theorem lineOf_pred (hk : k ≤ (U.block B2).round) (hk1 : 0 < k) :
    lineOf U B2 (k - 1) = selfParent U (lineOf U B2 k) := by
  unfold lineOf
  have h : (U.block B2).round - (k - 1) = ((U.block B2).round - k) + 1 := by omega
  rw [h, Function.iterate_succ_apply']

/-- The derived line is a chain: each block references the one below. -/
theorem lineOf_chain (hB2 : B2 ∈ U.ids) (hk : k ≤ (U.block B2).round) (hk1 : 0 < k) :
    lineOf U B2 (k - 1) ∈ (U.block (lineOf U B2 k)).refs := by
  rw [lineOf_pred hk hk1]
  exact selfParent_mem_refs (lineOf_mem hB2 hk) (by rw [lineOf_round hB2 hk]; omega)

end LineOf

/-! ## SS8 — the donor line is unique given its tip -/

/-- **SS8.** A `SkipMsg`'s donor line is determined by its top block:
on the interval its clauses govern, `line` coincides with the chain
derived by following self-parents down from `line r`, by P2's
uniqueness of the own-creator reference. -/
theorem SkipMsg.line_eq_lineOf (sk : SkipMsg U) :
    ∀ k, sk.r0 ≤ k → k ≤ sk.r → sk.line k = lineOf U (sk.line sk.r) k := by
  have hR0 : sk.r0 = (U.block sk.B1).round := rfl
  -- downward induction, phrased on the distance from the top
  have haux : ∀ d, sk.r0 + d ≤ sk.r →
      sk.line (sk.r - d) = lineOf U (sk.line sk.r) (sk.r - d) := by
    intro d
    induction d with
    | zero =>
        intro hd
        have htop : (U.block (sk.line sk.r)).round = sk.r :=
          sk.hline_round sk.r (by omega) le_rfl
        have h : lineOf U (sk.line sk.r) ((U.block (sk.line sk.r)).round)
            = sk.line sk.r := lineOf_top
        rw [htop] at h
        rw [Nat.sub_zero, h]
    | succ n ih =>
        intro hd
        have ihn := ih (by omega)
        have htop : (U.block (sk.line sk.r)).round = sk.r :=
          sk.hline_round sk.r (by omega) le_rfl
        have hmem : sk.line (sk.r - n) ∈ U.ids :=
          sk.hline_mem _ (by omega) (by omega)
        have h0 : 0 < (U.block (sk.line (sk.r - n))).round := by
          rw [sk.hline_round _ (by omega) (by omega)]
          omega
        -- the message's next block down is an own-creator reference…
        have hchain : sk.line (sk.r - n - 1) ∈ (U.block (sk.line (sk.r - n))).refs := by
          have := sk.hline_chain (sk.r - n) (by omega) (by omega)
          exact this
        have hcr : (U.block (sk.line (sk.r - n - 1))).creator
            = (U.block (sk.line (sk.r - n))).creator := by
          rw [sk.hline_creator _ (by omega) (by omega),
            sk.hline_creator _ (by omega) (by omega)]
        -- …so it is the self-parent, which is the derived line's next block
        have hstep : sk.line (sk.r - n - 1) = selfParent U (sk.line (sk.r - n)) :=
          eq_selfParent_of_mem hmem h0 hchain hcr
        have hpred : lineOf U (sk.line sk.r) (sk.r - n - 1)
            = selfParent U (lineOf U (sk.line sk.r) (sk.r - n)) :=
          lineOf_pred (by rw [htop]; omega) (by omega)
        have : sk.r - (n + 1) = sk.r - n - 1 := by omega
        rw [this, hstep, hpred, ihn]
  intro k hk1 hk2
  have := haux (sk.r - k) (by omega)
  have hks : sk.r - (sk.r - k) = k := by omega
  rwa [hks] at this

/-! ## SS9 — the denotation is a function of the compact core -/

/-- The recovering validator is determined by the anchor: it is the
anchor's creator. -/
theorem SkipMsg.v1_eq_of_B1 (sk₁ sk₂ : SkipMsg U) (hB1 : sk₁.B1 = sk₂.B1) :
    sk₁.v1 = sk₂.v1 := by
  have h₁ := sk₁.hB1c
  have h₂ := sk₂.hB1c
  rw [hB1] at h₁
  rw [← h₁, ← h₂]

/-- **SS9.** Two messages naming the same anchor and the same target,
drawing fresh identifiers from the same supply, denote observationally
equal universes: the identifier sets are equal and the blocks agree at
every member, differing only on junk outside their identifiers. The
decoder needs no hypothesis, since `block` consults `idx` only at fresh
identifiers, where `hidx` pins both to the same index. -/
theorem SkipMsg.skipFill_eq_of_core [DecidableEq BlockId] (sk₁ sk₂ : SkipMsg U)
    (hB1 : sk₁.B1 = sk₂.B1) (hr : sk₁.r = sk₂.r)
    (htop : sk₁.line sk₁.r = sk₂.line sk₂.r) (hfresh : sk₁.fresh = sk₂.fresh) :
    sk₁.skipFill.ids = sk₂.skipFill.ids
      ∧ ∀ b ∈ sk₁.skipFill.ids, sk₁.skipFill.block b = sk₂.skipFill.block b := by
  have hr0 : sk₁.r0 = sk₂.r0 := by
    unfold SkipData.r0
    rw [hB1]
  have hv1 : sk₁.v1 = sk₂.v1 := sk₁.v1_eq_of_B1 sk₂ hB1
  -- the lines agree on the interval, both being the derived chain
  have hline : ∀ k, sk₁.r0 ≤ k → k ≤ sk₁.r → sk₁.line k = sk₂.line k := by
    intro k h1 h2
    rw [sk₁.line_eq_lineOf k h1 h2,
      sk₂.line_eq_lineOf k (by omega) (by omega), htop]
  have hgap : sk₁.gap = sk₂.gap := by
    unfold SkipData.gap
    rw [hr, hr0]
  have hfreshIds : sk₁.freshIds = sk₂.freshIds := by
    unfold SkipData.freshIds
    rw [hgap, hfresh]
  have hids : sk₁.skipFill.ids = sk₂.skipFill.ids := by
    change U.ids ∪ sk₁.freshIds = U.ids ∪ sk₂.freshIds
    rw [hfreshIds]
  refine ⟨hids, ?_⟩
  intro b hb
  rcases Finset.mem_union.mp hb with ho | hf
  · rw [sk₁.skipFill_block_old ho, sk₂.skipFill_block_old ho]
  · obtain ⟨k, hk1, hk2, rfl⟩ := sk₁.mem_freshIds.mp hf
    have hfk : sk₁.fresh k = sk₂.fresh k := by rw [hfresh]
    have hfill : sk₁.fillBlock k = sk₂.fillBlock k := by
      unfold SkipData.fillBlock SkipData.prev
      rw [hline k (by omega) hk2, hv1, hr0, hB1, hfresh]
    calc sk₁.skipFill.block (sk₁.fresh k)
        = sk₁.fillBlock k := sk₁.skipFill_block_fresh
      _ = sk₂.fillBlock k := hfill
      _ = sk₂.skipFill.block (sk₂.fresh k) := sk₂.skipFill_block_fresh.symm
      _ = sk₂.skipFill.block (sk₁.fresh k) := by rw [hfk]

/-! ## The compact message, and its elaboration -/

/-- **The jump message**: the compact core a recovering validator
actually sends — its own name and anchor, the target block and its
author — with the fresh-identifier supply and a `SkipMsg`'s semantic
clauses about them, but no line: the line is derived. -/
structure JumpMsg (U : BlockUniverse Validator BlockId Payload) where
  /-- The recovering validator. -/
  v1 : Validator
  /-- Its last block before the crash — the anchor. -/
  B1 : BlockId
  /-- The donor of the reference structure. -/
  v2 : Validator
  /-- The pinned target block on the donor's line. -/
  B2 : BlockId
  /-- Fresh ids for the filled blocks, and their decoder. -/
  fresh : ℕ → BlockId
  idx : BlockId → ℕ
  /-- The anchor is `v1`'s only block at its round (see
  `SkipData.hB1uniq` for why this is a field rather than derived from
  correctness). -/
  hB1uniq : ∀ j ∈ U.ids, (U.block j).creator = v1 →
    (U.block j).round = (U.block B1).round → j = B1
  hv12 : v1 ≠ v2
  hB1 : B1 ∈ U.ids
  hB1c : (U.block B1).creator = v1
  hB2 : B2 ∈ U.ids
  hB2c : (U.block B2).creator = v2
  hB2r : (U.block B1).round ≤ (U.block B2).round
  hfresh_new : ∀ k, fresh k ∉ U.ids
  hidx : ∀ k, idx (fresh k) = k
  /-- The crash: `v1` authored nothing in the gap. -/
  hgap : ∀ b ∈ U.ids, (U.block b).creator = v1 →
    (U.block B1).round < (U.block b).round →
    (U.block b).round ≤ (U.block B2).round → False

namespace JumpMsg

variable (j : JumpMsg U)

/-- **The elaboration.** The `SkipMsg` a jump message denotes: target
round the target's round, line the derived chain. Every line clause is
discharged by the `lineOf` lemmas — the receiver holds no data the
sender chose. -/
noncomputable def toSkipMsg : SkipMsg U where
  v1 := j.v1
  B1 := j.B1
  v2 := j.v2
  r := (U.block j.B2).round
  line := lineOf U j.B2
  fresh := j.fresh
  idx := j.idx
  hB1uniq := j.hB1uniq
  hv12 := j.hv12
  hB1 := j.hB1
  hB1c := j.hB1c
  hline_mem := fun _ _ hk2 => lineOf_mem j.hB2 hk2
  hline_creator := fun _ _ hk2 => (lineOf_creator j.hB2 hk2).trans j.hB2c
  hline_round := fun _ _ hk2 => lineOf_round j.hB2 hk2
  hline_chain := fun _ hk1 hk2 =>
    lineOf_chain j.hB2 hk2 (by omega)
  hfresh_new := j.hfresh_new
  hidx := j.hidx
  hgap := j.hgap

/-- **The round jump.** The universe in which the sender produces at
the round above the target: the fill, elaborated from the compact
message. Being a `skipFill`, everything proved of the fill — SS1
through SS6 — applies to it verbatim. -/
noncomputable def denote [DecidableEq BlockId] : BlockUniverse Validator BlockId Payload :=
  j.toSkipMsg.skipFill

@[simp] theorem toSkipMsg_r : j.toSkipMsg.r = (U.block j.B2).round := rfl

@[simp] theorem toSkipMsg_line : j.toSkipMsg.line = lineOf U j.B2 := rfl

@[simp] theorem toSkipMsg_top : j.toSkipMsg.line j.toSkipMsg.r = j.B2 :=
  lineOf_top

end JumpMsg

/-! ## SS10 — receivers derive, and derivations converge -/

/-- **SS10a: the receiver holds everything the elaboration reads.**
Views are closed downward, so a view holding the target holds the whole
derived line — the sender's message points at nothing a receiver
lacks. -/
theorem lineOf_mem_view (V : View Validator BlockId Payload U) {B2 : BlockId}
    (hB2 : B2 ∈ U.ids) (hB2V : B2 ∈ V.ids) :
    ∀ k, k ≤ (U.block B2).round → lineOf U B2 k ∈ V.ids := by
  have haux : ∀ d, d ≤ (U.block B2).round → (selfParent U)^[d] B2 ∈ V.ids := by
    intro d
    induction d with
    | zero => intro _; exact hB2V
    | succ n ih =>
        intro hd
        obtain ⟨hmem, _, hrd⟩ := lineOf_aux hB2 n (by omega)
        have h0 : 0 < (U.block ((selfParent U)^[n] B2)).round := by omega
        rw [Function.iterate_succ_apply']
        exact V.complete _ (ih (by omega)) _ (selfParent_mem_refs hmem h0)
  intro k hk
  exact haux _ (by omega)

/-- **SS10b: derivations converge.** Two jump messages with the same
compact core denote observationally equal universes — since views share
`U.block`, every receiver elaborating the message arrives at this one
object. The elaborated lines both being the derived chain, this is SS9
applied to the elaborations. -/
theorem JumpMsg.denote_eq_of_core [DecidableEq BlockId] (j₁ j₂ : JumpMsg U)
    (hB1 : j₁.B1 = j₂.B1) (hB2 : j₁.B2 = j₂.B2) (hfresh : j₁.fresh = j₂.fresh) :
    j₁.denote.ids = j₂.denote.ids
      ∧ ∀ b ∈ j₁.denote.ids, j₁.denote.block b = j₂.denote.block b :=
  SkipMsg.skipFill_eq_of_core j₁.toSkipMsg j₂.toSkipMsg hB1
    (by simp [hB2]) (by simp [hB2]) hfresh

end LeanDag
