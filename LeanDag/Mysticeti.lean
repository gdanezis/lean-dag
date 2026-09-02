import LeanDag.Support

/-!
# Uncertified DAGs: the Mysticeti commit rules

`spec.md` §4, Phase 2 — Stage A.

A certified DAG (DAG-Rider, Bullshark, Narwhal) admits a block only once
2f+1 validators have signed it, so the block *is* a certificate and
"referenced by 2f+1 validators next round" is the whole commit rule.
Mysticeti drops that round for latency, so blocks carry no authority of
their own and it has to be rebuilt inside the DAG, one round further on:

* a round-`(r+1)` block **votes** for a round-`r` block `L` when `L ∈ refs`,
  and **blames** otherwise;
* a round-`(r+2)` block **certifies** `L` when its own references include
  votes for `L` from 2f+1 *distinct* validators;
* `L` is **directly committed** when certificates for it come from 2f+1
  distinct validators, and **directly skipped** when blames do.

This file is Stage A: everything here is universe-level, so it needs neither
views nor a leader schedule. `L` is an arbitrary block — nothing in M1–M3
cares that it is a leader — and M5 is stated as *same round, same creator*
rather than *same slot*, which is what "same slot" means operationally.
Views, the slot schedule, and the indirect rule arrive in Stages B and C.
-/

namespace LeanDag

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {U : BlockUniverse Validator BlockId Payload}

/-- The references of `C` that vote for `L`. -/
def votesIn (U : BlockUniverse Validator BlockId Payload) (C L : BlockId) : Finset BlockId :=
  (U.block C).refs.filter (fun q => L ∈ (U.block q).refs)

/-- A round-`(r+2)` block certifies `L` when its votes for `L` come from a
quorum of distinct validators. -/
def Certifies (U : BlockUniverse Validator BlockId Payload) (C L : BlockId) : Prop :=
  quorumCard Validator ≤ (creatorsOf U.block (votesIn U C L)).card

/-- All three rule predicates are cardinality comparisons and so decidable,
but as `Prop`-valued `def`s Lean will not see that unaided. `certificates`
needs this to filter on `Certifies`, and concrete models need it to settle
the rules by `decide`. -/
instance decidableCertifies (C L : BlockId) : Decidable (Certifies U C L) :=
  inferInstanceAs (Decidable (quorumCard Validator ≤ (creatorsOf U.block (votesIn U C L)).card))

/-- The certificates for a round-`r` block `L`: the round-`(r+2)` blocks that
certify it. -/
def certificates (U : BlockUniverse Validator BlockId Payload) (L : BlockId) (r : ℕ) :
    Finset BlockId :=
  (blocksAt U (r + 2)).filter (fun C => Certifies U C L)

/-- Membership in `certificates`, unfolded: a round-`r+2` block that certifies `L`. -/
@[simp]
theorem mem_certificates {C L : BlockId} {r : ℕ} :
    C ∈ certificates U L r ↔ C ∈ U.ids ∧ (U.block C).round = r + 2 ∧ Certifies U C L := by
  simp [certificates, and_assoc]

/-- A vote counted by a round-`(r+2)` certificate really is a round-`(r+1)`
block of the universe that references `L`. Used wherever a certificate has to
be turned back into the supporters behind it. -/
theorem mem_votesIn_spec {C L q : BlockId} {r : ℕ}
    (hC : C ∈ U.ids) (hCr : (U.block C).round = r + 2) (hq : q ∈ votesIn U C L) :
    q ∈ U.ids ∧ (U.block q).round = r + 1 ∧ L ∈ (U.block q).refs := by
  rw [votesIn, Finset.mem_filter] at hq
  refine ⟨U.complete C hC q hq.1, ?_, hq.2⟩
  have := U.round_of_mem_refs hC hq.1
  omega

/-- `L` is directly committed when its certificates come from a quorum of
distinct validators. -/
def DirectCommit (U : BlockUniverse Validator BlockId Payload) (L : BlockId) (r : ℕ) : Prop :=
  quorumCard Validator ≤ (creatorsOf U.block (certificates U L r)).card

/-- `L` is directly skipped when a quorum of distinct validators declined to
vote for it. -/
def DirectSkip (U : BlockUniverse Validator BlockId Payload) (L : BlockId) (r : ℕ) : Prop :=
  quorumCard Validator ≤ (blames U L (r + 1)).card

instance decidableDirectCommit (L : BlockId) (r : ℕ) : Decidable (DirectCommit U L r) :=
  inferInstanceAs (Decidable (quorumCard Validator ≤ (creatorsOf U.block (certificates U L r)).card))

instance decidableDirectSkip (L : BlockId) (r : ℕ) : Decidable (DirectSkip U L r) :=
  inferInstanceAs (Decidable (quorumCard Validator ≤ (blames U L (r + 1)).card))

/-- **M3.** A directly skipped block has **no certificate anywhere** in the
universe — not merely none in some view.

With `2f+1` blamers, and correct validators unable to sit on both sides, the
supporters number at most `(3f+1) - (2f+1) + f = 2f`. A certificate needs
`2f+1` distinct vote-creators, and every voter among a round-`(r+2)` block's
references is a genuine supporter, so no such block can exist.

Universe-wide is the right strength: it is why a skip needs no anchor to
justify it, and it is what makes the indirect rule agree with the direct one
(M4). -/
theorem certificates_eq_empty_of_directSkip {L : BlockId} {r : ℕ}
    (h : DirectSkip U L r) : certificates U L r = ∅ := by
  -- A quorum of blamers caps the supporters below a quorum (Support.lean) ...
  have hcap := card_supporters_le_of_card_blames (U := U) (L := L) (n := r + 1) h
  rw [Finset.eq_empty_iff_forall_notMem]
  intro C hC
  rw [mem_certificates] at hC
  obtain ⟨hC_ids, hC_round, hCert⟩ := hC
  rw [Certifies] at hCert
  -- ... and every vote a certificate counts is a genuine supporter.
  have hsub : creatorsOf U.block (votesIn U C L) ⊆ supporters U L (r + 1) := by
    intro v hv
    rw [mem_creatorsOf] at hv
    obtain ⟨q, hq, hq_creator⟩ := hv
    obtain ⟨hq_ids, hq_round, hq_ref⟩ := mem_votesIn_spec hC_ids hC_round hq
    exact mem_supporters.mpr ⟨q, hq_ids, hq_round, hq_ref, hq_creator⟩
  have := Finset.card_le_card hsub
  have := F.card_validators
  omega

/-- **M1.** No block is both directly committed and directly skipped.

Immediate from M3: a skip leaves no certificates at all, and a commit needs
`2f+1` distinct certificate authors. -/
theorem not_directCommit_of_directSkip {L : BlockId} {r : ℕ}
    (h : DirectSkip U L r) : ¬ DirectCommit U L r := by
  rw [DirectCommit, certificates_eq_empty_of_directSkip h]
  simp only [creatorsOf, Finset.image_empty, Finset.card_empty]
  have := F.card_validators
  omega

/-- **M2.** Once a block is directly committed, its certificate becomes
unavoidable: every block from round `r+3` on has one in its causal history.

The bound is `r+3` and it is **tight**. Certificates sit at round `r+2`, and
a round-`(r+2)` block's own references sit at `r+1`, so a round-`(r+2)` block
that is not itself a certificate reaches none. One round above the
certificates is needed before the intersection argument bites — the same
phenomenon as T3's `r+2`.

This is what makes the indirect rule agree with the direct one, and it is
why the slot schedule must space leaders at least 3 rounds apart: that is
exactly what puts every anchor at round `≥ r+3`. -/
theorem exists_certificate_reaches_of_directCommit {L : BlockId} {r : ℕ}
    (h : DirectCommit U L r)
    {c : BlockId} (hc : c ∈ U.ids) (hcr : r + 3 ≤ (U.block c).round) :
    ∃ C ∈ certificates U L r, Reaches U c C := by
  -- Base case at `r+3`: the certificates' correct authors cannot be dodged.
  have hbase : ∀ c' ∈ U.ids, (U.block c').round = r + 3 →
      ∃ C, C ∈ certificates U L r ∧ Reaches U c' C := by
    intro c' hc' hc'r
    set T := creatorsOf U.block (certificates U L r) ∩ (Correct : Finset Validator) with hT_def
    have hT : ∀ v ∈ T, ∃ q ∈ U.ids,
        (U.block q).round = r + 2 ∧ q ∈ certificates U L r ∧ (U.block q).creator = v := by
      intro v hv
      rw [hT_def, Finset.mem_inter, mem_creatorsOf] at hv
      obtain ⟨⟨q, hq_cert, hq_creator⟩, _⟩ := hv
      obtain ⟨hq_ids, hq_round, -⟩ := mem_certificates.mp hq_cert
      exact ⟨q, hq_ids, hq_round, hq_cert, hq_creator⟩
    have hTc : ∀ v ∈ T, v ∈ (Correct : Finset Validator) :=
      fun _ hv => Finset.mem_of_mem_inter_right hv
    have hcard : F.f + 1 ≤ T.card := card_inter_correct_of_quorum h
    obtain ⟨C, hC_mem, hC_cert⟩ :=
      exists_mem_refs_of_correct_support_of_card
        (P := fun q => q ∈ certificates U L r) hT hTc hcard hc' (by omega)
    exact ⟨C, hC_cert, Reaches.single hC_mem⟩
  exact reaches_pred_of_round_le hbase hc hcr

/-- A direct commit needs `2f+1` distinct certificate authors, so in
particular at least one certificate. -/
theorem certificates_nonempty_of_directCommit {L : BlockId} {r : ℕ}
    (h : DirectCommit U L r) : (certificates U L r).Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  rintro hempty
  rw [DirectCommit, hempty] at h
  simp only [creatorsOf, Finset.image_empty, Finset.card_empty] at h
  have := F.card_validators
  omega

/-- **M5′ (certificate uniqueness).** A slot admits at most one *certifiable*
block: if certificates exist for two round-`r` blocks by the same author,
those blocks coincide.

Stronger than M5, and the form the indirect rule needs — the indirect rule
commits on the strength of a *single* certificate lying in reach, not on a
quorum of them.

The proof needs no relationship between the two certificates. Each names
n−f distinct voters, so the two voter sets intersect in a correct `w` (T0');
`w`'s single round-`(r+1)` block votes for both (T1); and **distinctness**
forbids one block referencing two round-`r` blocks by one author. That last
step is the one place in the development where distinctness is indispensable.

The rounds need no hypothesis: a voter for `L₁` sits at round `r+1` and
references it, which pins `L₁` to round `r`, and likewise for `L₂`. -/
theorem eq_of_certificates_nonempty {L₁ L₂ : BlockId} {r : ℕ}
    (h₁ : (certificates U L₁ r).Nonempty) (h₂ : (certificates U L₂ r).Nonempty)
    (hcreator : (U.block L₁).creator = (U.block L₂).creator) :
    L₁ = L₂ := by
  obtain ⟨C₁, hC₁⟩ := h₁
  obtain ⟨C₂, hC₂⟩ := h₂
  rw [mem_certificates] at hC₁ hC₂
  obtain ⟨hC₁_ids, hC₁_round, hC₁_cert⟩ := hC₁
  obtain ⟨hC₂_ids, hC₂_round, hC₂_cert⟩ := hC₂
  -- The two vote quorums share a block: one round-`(r+1)` block votes for
  -- both candidates.
  obtain ⟨q, hq₁, hq₂⟩ :=
    U.exists_common_mem_of_quorums (n := r + 1)
      (fun _ hq => ⟨(mem_votesIn_spec hC₁_ids hC₁_round hq).1,
        (mem_votesIn_spec hC₁_ids hC₁_round hq).2.1⟩)
      (fun _ hq => ⟨(mem_votesIn_spec hC₂_ids hC₂_round hq).1,
        (mem_votesIn_spec hC₂_ids hC₂_round hq).2.1⟩)
      hC₁_cert hC₂_cert
  -- Distinctness forbids it referencing two round-`r` blocks by one author.
  exact (U.valid q (mem_votesIn_spec hC₁_ids hC₁_round hq₁).1).distinct_creators
    L₁ (mem_votesIn_spec hC₁_ids hC₁_round hq₁).2.2
    L₂ (mem_votesIn_spec hC₂_ids hC₂_round hq₂).2.2 hcreator

/-- **M5.** At most one block per slot is directly committed.

Now a corollary of M5′: a direct commit implies a certificate exists. Note
the outer certificate-quorum intersection this proof used to perform is not
needed — M5′ never requires the two certificates to be the same block. -/
theorem eq_of_directCommit_of_creator_eq {L₁ L₂ : BlockId} {r : ℕ}
    (h₁ : DirectCommit U L₁ r) (h₂ : DirectCommit U L₂ r)
    (hcreator : (U.block L₁).creator = (U.block L₂).creator) :
    L₁ = L₂ :=
  eq_of_certificates_nonempty (certificates_nonempty_of_directCommit h₁)
    (certificates_nonempty_of_directCommit h₂) hcreator

/-! ## The indirect rule's test

An undecided slot is settled by looking into the causal history of a later,
directly committed *anchor*: commit if a certificate for the slot lies in
that subgraph, skip otherwise. M4 is the statement that this never
contradicts the direct rule. -/

/-- The indirect rule's test: does a certificate for `L` lie in the causal
history of the anchor block `A`? -/
def CertifiedIn (U : BlockUniverse Validator BlockId Payload) (A L : BlockId) (r : ℕ) : Prop :=
  ∃ C ∈ certificates U L r, Reaches U A C

/-- A certificate in reach is, in particular, a certificate that exists. This
is what lets M5′ compare an *indirect* commit against anything else. -/
theorem certificates_nonempty_of_certifiedIn {A L : BlockId} {r : ℕ}
    (h : CertifiedIn U A L r) : (certificates U L r).Nonempty := by
  obtain ⟨C, hC, -⟩ := h
  exact ⟨C, hC⟩

/-- **M4, commit half.** A directly committed block is found by *every*
anchor from round `r+3` on. This is M2 restated as the indirect rule's test,
and it is why the slot schedule must space leaders at least three rounds
apart — that spacing is exactly what puts every anchor in range. -/
theorem certifiedIn_of_directCommit {L : BlockId} {r : ℕ} (h : DirectCommit U L r)
    {A : BlockId} (hA : A ∈ U.ids) (hAr : r + 3 ≤ (U.block A).round) :
    CertifiedIn U A L r :=
  exists_certificate_reaches_of_directCommit h hA hAr

/-- **M4, skip half.** A directly skipped block is found by *no* anchor
whatsoever — no round hypothesis needed, because M3 rules out the
certificate universe-wide rather than merely out of reach. -/
theorem not_certifiedIn_of_directSkip {L : BlockId} {r : ℕ} (h : DirectSkip U L r)
    {A : BlockId} : ¬ CertifiedIn U A L r := by
  rintro ⟨C, hC, -⟩
  rw [certificates_eq_empty_of_directSkip h] at hC
  exact absurd hC (Finset.notMem_empty C)

/-- **M4.** Where the direct rule decides, the indirect rule agrees.

The asymmetry between the halves is worth noting. Commit needs the anchor to
be far enough along (`r+3`), since the certificate must be *reachable*. Skip
needs nothing at all, since there is no certificate anywhere to reach. -/
theorem indirect_agrees_with_direct {L : BlockId} {r : ℕ}
    {A : BlockId} (hA : A ∈ U.ids) (hAr : r + 3 ≤ (U.block A).round) :
    (DirectCommit U L r → CertifiedIn U A L r) ∧
      (DirectSkip U L r → ¬ CertifiedIn U A L r) :=
  ⟨fun h => certifiedIn_of_directCommit h hA hAr, fun h => not_certifiedIn_of_directSkip h⟩

/-- The indirect test is **view-independent**: a validator holding the anchor
computes the same verdict from its own local DAG as from the whole universe.

T6a in action — the certificate could never have lain outside the view, so
confining the search to it changes nothing. This is what stops two validators
with different views but the same anchor from disagreeing. -/
theorem certifiedIn_iff_of_view {V : View Validator BlockId Payload U} {A L : BlockId} {r : ℕ}
    (hA : A ∈ V.ids) :
    (∃ C, C ∈ V.ids ∧ C ∈ certificates U L r ∧ Reaches U A C) ↔ CertifiedIn U A L r :=
  View.exists_reaches_iff hA

/-! ## Stage C1 — the slot schedule and the decision relation -/

/-- The leader schedule: which validator proposes at which round, as a
sequence of slots.

Slots need **not** be three rounds apart. Under pipelining consecutive slots
are one round apart, and under multiple leaders per round they share a round,
so all that is required of `slotRound` is that it be monotone. The three-round
separation M4's commit half needs is no longer a property of *consecutive*
slots and is therefore not derivable here; it is required instead of the
particular pairs that use it, by `Eligible` below.

`unbounded` was a theorem under three-round spacing (`3 * k ≤
slotRound k`) and is underivable from `mono` alone — a schedule parking every
slot at one round is monotone. Liveness needs it, so it is assumed.

`keyed` says distinct slots differ in round or in leader. It too held under three-round spacing, which makes `slotRound` injective outright. Under
multiple leaders it is a real condition on the schedule: the proposers of a
round must be distinct validators. Without it one block would be the candidate
for two slots, and the ledger would deliver it twice. -/
class Slots (Validator : Type*) where
  /-- The round at which slot `k` is proposed. -/
  slotRound : ℕ → ℕ
  /-- The validator whose block is the slot-`k` candidate. -/
  leader : ℕ → Validator
  /-- Slots are enumerated in round order. -/
  mono : Monotone slotRound
  /-- Slot rounds are unbounded. -/
  unbounded : ∀ n, ∃ k, n ≤ slotRound k
  /-- Distinct slots differ in round or in leader. -/
  keyed : Function.Injective (fun k => (slotRound k, leader k))

variable [S : Slots Validator]

variable (Validator) in
/-- The round at which slot `k`'s direct rules are settled: its certificates
live here. Algorithm 2's `DecisionRound`.

`Validator` is explicit because the result is a bare `ℕ`, so nothing else
would fix it — the same reason the three-round spacing lemma is written
`S.slotRound`. -/
def decisionRound (k : ℕ) : ℕ := S.slotRound k + 2

variable (Validator) in
/-- **`j` may anchor `k`.** Its proposal lies past `k`'s decision round, so a
block at `j`'s round can reach a certificate for `k`'s — which is exactly M4's
`r + 3` hypothesis. Algorithm 3's anchor filter `r_decision < s.round`.

Stated through `decisionRound` rather than as a bare `+ 3` so that a later
wavelength parameter is a change to one definition.

It is a predicate on the **pair of slots alone** — not on any view. That is
what makes agreement go through: two validators deciding the same slot `k`
agree on which slots may anchor it, so each one's eligibility premise is the
side condition the other's intermediate-skip premise requires. -/
def Eligible (k j : ℕ) : Prop := decisionRound Validator k < S.slotRound j

omit [Fintype Validator] [DecidableEq Validator] F in
/-- Eligibility, unfolded: an anchor must sit three rounds above the slot it decides — one for votes, one for certificates, one to separate them. -/
theorem eligible_iff {k j : ℕ} :
    Eligible Validator k j ↔ S.slotRound k + 3 ≤ S.slotRound j := by
  simp [Eligible, decisionRound]
  omega

instance decidableEligible (k j : ℕ) : Decidable (Eligible Validator k j) :=
  inferInstanceAs (Decidable (decisionRound Validator k < S.slotRound j))

omit [Fintype Validator] [DecidableEq Validator] F in
/-- An eligible anchor is a later slot. Monotonicity is what carries it: were
`j ≤ k`, the anchor's round could not exceed `k`'s, let alone clear its
decision round.

This makes the `k < j` premises of `Decided` redundant. They are kept anyway:
`decided_unique` recurses on them and hands them to `lt_trichotomy`, and
re-deriving them at each use would be noise. -/
theorem lt_of_eligible {k j : ℕ} (h : Eligible Validator k j) : k < j := by
  by_contra hle
  have : S.slotRound j ≤ S.slotRound k := S.mono (by omega)
  rw [eligible_iff] at h
  omega

omit [Fintype Validator] [DecidableEq Validator] F in
/-- **Conservativity.** Under a schedule whose consecutive slots are three
rounds apart — the `spacing` field this class used to carry — *every* later
slot is eligible to anchor an earlier one, and the generalised premise implies the three-round one.

So the generalised `Decided` has exactly the constructors the three-round form has
whenever three-round spacing holds: no derivation available before the
change is unavailable after it. This is the three-round spacing bound,
demoted from a consequence of the class to a consequence of a hypothesis. -/
theorem eligible_of_lt_of_spacing (hsp : ∀ k, S.slotRound k + 3 ≤ S.slotRound (k + 1))
    {k j : ℕ} (h : k < j) : Eligible Validator k j := by
  rw [eligible_iff]
  induction j with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with hlt | heq
    · have := ih hlt
      have := hsp n
      omega
    · subst heq
      exact hsp k

/-- `L` is a candidate block for slot `k`: the right round, the right author.

A *correct* leader has at most one such block (T1); a Byzantine one may have
several, which is why the definitions below quantify over candidates rather
than selecting one. M5 supplies uniqueness where it is needed. -/
def IsLeaderBlock (U : BlockUniverse Validator BlockId Payload) (k : ℕ) (L : BlockId) : Prop :=
  L ∈ U.ids ∧ (U.block L).round = S.slotRound k ∧ (U.block L).creator = S.leader k

/-- As with the Stage A predicates, these are decidable but Lean needs
telling, so concrete models can settle them by `decide`. -/
instance decidableIsLeaderBlock (k : ℕ) (L : BlockId) : Decidable (IsLeaderBlock U k L) :=
  inferInstanceAs (Decidable (L ∈ U.ids ∧ (U.block L).round = S.slotRound k ∧
    (U.block L).creator = S.leader k))

/-! ### View-relative direct rules

A validator applies the direct rules to what it can actually see. These are
monotone into the universe-level versions of Stage A, so M4 and M5 lift to
views without redoing any counting. -/

/-- The certificates for `L` that a view actually holds. -/
def certificatesIn (U : BlockUniverse Validator BlockId Payload)
    (V : View Validator BlockId Payload U) (L : BlockId) (r : ℕ) : Finset BlockId :=
  certificates U L r ∩ V.ids

/-- Direct commit, as judged from a single view. -/
def DirectCommitIn (U : BlockUniverse Validator BlockId Payload)
    (V : View Validator BlockId Payload U) (L : BlockId) (r : ℕ) : Prop :=
  quorumCard Validator ≤ (creatorsOf U.block (certificatesIn U V L r)).card

/-- Direct skip, as judged from a single view. -/
def DirectSkipIn (U : BlockUniverse Validator BlockId Payload)
    (V : View Validator BlockId Payload U) (L : BlockId) (r : ℕ) : Prop :=
  quorumCard Validator ≤
    (creatorsOf U.block
      (((blocksAt U (r + 1)).filter (fun q => L ∉ (U.block q).refs)) ∩ V.ids)).card

omit S in
instance decidableDirectCommitIn (V : View Validator BlockId Payload U) (L : BlockId) (r : ℕ) :
    Decidable (DirectCommitIn U V L r) :=
  inferInstanceAs (Decidable (quorumCard Validator ≤ (creatorsOf U.block (certificatesIn U V L r)).card))

instance decidableDirectSkipIn (V : View Validator BlockId Payload U) (L : BlockId) (r : ℕ) :
    Decidable (DirectSkipIn U V L r) :=
  inferInstanceAs (Decidable (quorumCard Validator ≤
    (creatorsOf U.block
      (((blocksAt U (r + 1)).filter (fun q => L ∉ (U.block q).refs)) ∩ V.ids)).card))

omit S in
/-- **A view can only under-report.** Everything it sees is real, so a
view-relative direct commit is a genuine one.

This one line is what lets all of Stage A be reused unchanged: M2, M4 and M5
are stated universe-level, and a validator's local judgement feeds straight
into them. -/
theorem directCommit_of_directCommitIn {V : View Validator BlockId Payload U}
    {L : BlockId} {r : ℕ} (h : DirectCommitIn U V L r) : DirectCommit U L r :=
  le_trans h (Finset.card_le_card (Finset.image_subset_image Finset.inter_subset_left))

omit S in
theorem directSkip_of_directSkipIn {V : View Validator BlockId Payload U}
    {L : BlockId} {r : ℕ} (h : DirectSkipIn U V L r) : DirectSkip U L r :=
  le_trans h (Finset.card_le_card (Finset.image_subset_image Finset.inter_subset_left))

/-! ### The decision relation

`Decided U V k v` — a validator holding `V` has settled slot `k`, with `v`
naming the committed block or `none` for a skip.

A **relation**, not a function: a `decide` function would recurse upward in
slot index with no a-priori bound, needing fuel or partiality for nothing,
since none of this needs to compute.

The indirect cases anchor on the nearest **eligible** committed slot after
`k` — not simply the nearest one. Under pipelining slots `k+1` and `k+2` sit
at rounds `r+1` and `r+2`, where no certificate for `k` is reachable, and
anchoring there would turn one validator's direct commit into another's
indirect skip. The anchor must clear `k`'s decision round, which is Algorithm
3's filter `anchors ← [s ∈ sequence s.t. r_decision < s.round]`.

For the same reason the intermediate premise quantifies over the **eligible**
slots between `k` and the anchor only. The ineligible ones are routinely
committed, so requiring them to be skipped would leave `k` undecidable
forever.

"Nearest" is stated positively — every eligible slot strictly between is
decided `none` — rather than as *no eligible slot between is committed*. The
negative reading is a negative premise, which an inductive definition cannot
carry; the positive one is equivalent, since the sweep decides every slot it
passes, and keeps every recursive occurrence strictly positive. Guarding the
occurrence behind `Eligible` preserves that: `Eligible` is a predicate on two
naturals and does not mention `Decided`. -/
/-- **The decision relation.** `Decided U V k v` — a validator holding the
view `V` has settled slot `k`, committing the block `v = some L` or
skipping it, `v = none`.

Four rules, in two pairs. The *direct* pair reads the slot's own
certificates: a candidate carrying `n−f` of them is committed, and a slot
whose every candidate is blamed by `n−f` is skipped. The *indirect* pair
applies when the direct evidence is inconclusive, and decides `k` by
looking up to an **anchor** — the nearest eligible slot above `k` that is
itself committed — and asking whether a certificate for a candidate of
`k` is reachable from the anchor's block.

"Nearest" is stated positively: every eligible slot strictly between `k`
and the anchor is decided `none`. The negative reading — *no eligible
slot between is committed* — would be a negative premise, which an
inductive definition cannot carry; the positive form is equivalent, since
the sweep decides every slot it passes, and it keeps every recursive
occurrence strictly positive. The occurrence sits behind `Eligible`,
which is a predicate on two naturals and does not mention `Decided`.

The relation is indexed by a view, so two validators may reach different
verdicts by the letter of the definition; M6 (`decided_unique`) is the
theorem that they cannot. -/
inductive Decided (U : BlockUniverse Validator BlockId Payload)
    (V : View Validator BlockId Payload U) : ℕ → Option BlockId → Prop
  /-- The direct rule commits a candidate outright. -/
  | directCommit {k : ℕ} {L : BlockId} :
      IsLeaderBlock U k L → DirectCommitIn U V L (S.slotRound k) →
      Decided U V k (some L)
  /-- The direct rule blames every candidate — including vacuously, when the
  leader produced no block at all. -/
  | directSkip {k : ℕ} :
      (∀ L, IsLeaderBlock U k L → DirectSkipIn U V L (S.slotRound k)) →
      Decided U V k none
  /-- Anchored on the nearest eligible committed slot, a certificate is in
  reach. -/
  | indirectCommit {k j : ℕ} {A L : BlockId} :
      k < j → Eligible Validator k j → Decided U V j (some A) →
      (∀ i, k < i → i < j → Eligible Validator k i → Decided U V i none) →
      IsLeaderBlock U k L → CertifiedIn U A L (S.slotRound k) →
      Decided U V k (some L)
  /-- Anchored on the nearest eligible committed slot, no candidate is in
  reach. -/
  | indirectSkip {k j : ℕ} {A : BlockId} :
      k < j → Eligible Validator k j → Decided U V j (some A) →
      (∀ i, k < i → i < j → Eligible Validator k i → Decided U V i none) →
      (∀ L, IsLeaderBlock U k L → ¬ CertifiedIn U A L (S.slotRound k)) →
      Decided U V k none

/-! ## Stage C2 — the direct rules, lifted to views

Everything here is a corollary of Stage A composed with monotonicity. No
counting is redone: a view can only under-report, so its verdicts are
genuine universe-level ones and the Stage A theorems apply directly. -/

omit S in
/-- Cross-view M1: one validator cannot directly commit what another
directly skips. -/
theorem not_directSkipIn_of_directCommitIn {V₁ V₂ : View Validator BlockId Payload U}
    {L : BlockId} {r : ℕ} (h₁ : DirectCommitIn U V₁ L r) (h₂ : DirectSkipIn U V₂ L r) :
    False :=
  not_directCommit_of_directSkip (directSkip_of_directSkipIn h₂)
    (directCommit_of_directCommitIn h₁)

/-- Cross-view M5: two validators cannot directly commit *different* blocks
for one slot. Both candidates are authored by `leader k`, which is the
same-creator hypothesis M5 needs. -/
theorem eq_of_directCommitIn {V₁ V₂ : View Validator BlockId Payload U}
    {k : ℕ} {L₁ L₂ : BlockId}
    (hL₁ : IsLeaderBlock U k L₁) (hL₂ : IsLeaderBlock U k L₂)
    (h₁ : DirectCommitIn U V₁ L₁ (S.slotRound k))
    (h₂ : DirectCommitIn U V₂ L₂ (S.slotRound k)) :
    L₁ = L₂ :=
  eq_of_directCommit_of_creator_eq (directCommit_of_directCommitIn h₁)
    (directCommit_of_directCommitIn h₂) (by rw [hL₁.2.2, hL₂.2.2])

/-- **The engine of M6.** A direct commit made in *any* view is visible from
*every* later slot's leader block. A validator that missed the direct commit
therefore recovers it indirectly, which is what stops anchors from
diverging.

Eligibility is what discharges the round hypothesis, and it is now taken as a
premise rather than derived from `k < j`: under pipelining the next slot is
one round on, not three, and a block there reaches no certificate for `k`. -/
theorem certifiedIn_of_directCommitIn {V : View Validator BlockId Payload U}
    {k j : ℕ} {L A : BlockId}
    (h : DirectCommitIn U V L (S.slotRound k))
    (hA : A ∈ U.ids) (hAr : (U.block A).round = S.slotRound j)
    (helig : Eligible Validator k j) :
    CertifiedIn U A L (S.slotRound k) := by
  refine certifiedIn_of_directCommit (directCommit_of_directCommitIn h) hA ?_
  rw [eligible_iff] at helig
  omega

omit S in
/-- A direct skip made in any view is invisible from every anchor — no round
hypothesis needed, since M3 rules the certificate out universe-wide. -/
theorem not_certifiedIn_of_directSkipIn {V : View Validator BlockId Payload U}
    {L : BlockId} {r : ℕ} (h : DirectSkipIn U V L r) {A : BlockId} :
    ¬ CertifiedIn U A L r :=
  not_certifiedIn_of_directSkip (directSkip_of_directSkipIn h)

/-- **Direct decisions agree across views.** If one validator directly
commits a slot, no other validator can directly skip it — the `∀`-form here
being exactly the premise of `Decided.directSkip`. -/
theorem not_directSkip_of_directCommitIn {V₁ V₂ : View Validator BlockId Payload U}
    {k : ℕ} {L : BlockId} (hL : IsLeaderBlock U k L)
    (h₁ : DirectCommitIn U V₁ L (S.slotRound k))
    (h₂ : ∀ L', IsLeaderBlock U k L' → DirectSkipIn U V₂ L' (S.slotRound k)) :
    False :=
  not_directSkipIn_of_directCommitIn h₁ (h₂ L hL)

/-! ## Stage C3 — agreement -/

/-- Whatever route it took, a committed verdict names a genuine candidate for
that slot. Needed because the agreement proof must feed another validator's
anchor into the visibility lemma, which wants its round. -/
theorem isLeaderBlock_of_decided {V : View Validator BlockId Payload U} {j : ℕ} {A : BlockId}
    (h : Decided U V j (some A)) : IsLeaderBlock U j A := by
  cases h with
  | directCommit hL _ => exact hL
  | indirectCommit _ _ _ _ hL _ => exact hL

omit [DecidableEq BlockId] in
/-- **A block is the candidate of at most one slot.**

Under the old three-round spacing this was free: `slotRound` was injective, so
distinct slots sat at distinct rounds and a block's round named its slot.
Under multiple leaders per round it is exactly what `Slots.keyed` yields — two
slots sharing a round are told apart by their leaders, and a schedule that
gave one validator two slots in a round would make one block the candidate for
both. -/
theorem slot_eq_of_isLeaderBlock {k₁ k₂ : ℕ} {L : BlockId}
    (h₁ : IsLeaderBlock U k₁ L) (h₂ : IsLeaderBlock U k₂ L) : k₁ = k₂ :=
  S.keyed (by simp only [← h₁.2.1, ← h₂.2.1, ← h₁.2.2, ← h₂.2.2])

/-- **And so a committed block belongs to one slot.** The ledger reads
verdicts off in slot order, so without this a single block could be delivered
twice — a total-order defect that `commitSeq` alone would not notice. -/
theorem slot_eq_of_decided_commit {V₁ V₂ : View Validator BlockId Payload U}
    {k₁ k₂ : ℕ} {L : BlockId}
    (h₁ : Decided U V₁ k₁ (some L)) (h₂ : Decided U V₂ k₂ (some L)) : k₁ = k₂ :=
  slot_eq_of_isLeaderBlock (isLeaderBlock_of_decided h₁) (isLeaderBlock_of_decided h₂)

/-- Two commits for one slot agree, however each was reached. Both routes
yield a certificate, so this is M5′ with the plumbing done. -/
theorem eq_of_hasCertificate {k : ℕ} {L₁ L₂ : BlockId}
    (hL₁ : IsLeaderBlock U k L₁) (hL₂ : IsLeaderBlock U k L₂)
    (h₁ : (certificates U L₁ (S.slotRound k)).Nonempty)
    (h₂ : (certificates U L₂ (S.slotRound k)).Nonempty) :
    L₁ = L₂ :=
  eq_of_certificates_nonempty h₁ h₂ (by rw [hL₁.2.2, hL₂.2.2])

/-- **Visibility from an anchor.** A slot committed directly is certified
at any eligible anchor above it: the anchor is a real block whose round
the eligibility premise places far enough above the slot.

The companion to `anchor_eq`, and the second of the two ideas in the
agreement proof. Both rules use it to rule out the mixed cases, where one
validator commits directly and the other skips indirectly: the skipper's
own anchor is where the commit becomes visible, so its
no-certificate premise cannot hold. -/
theorem certifiedIn_of_directCommitIn_at_anchor
    {V W : View Validator BlockId Payload U} {k j : ℕ} {L A : BlockId}
    (h : DirectCommitIn U V L (S.slotRound k))
    (hj : Decided U W j (some A)) (helig : Eligible Validator k j) :
    CertifiedIn U A L (S.slotRound k) :=
  certifiedIn_of_directCommitIn h (isLeaderBlock_of_decided hj).1
    (isLeaderBlock_of_decided hj).2.1 helig

/-- **The anchor comparison.** Two indirect decisions for one slot each
name an anchor, together with the premise that every eligible slot
strictly between the slot and that anchor was decided `none`. Whichever
anchor is the earlier is then decided `none` by the other side and
`some` by its own, so the anchors coincide — and with them the blocks
they name.

The statement carries no consensus content: `Dec` and `Elig` are
arbitrary predicates, and the argument is only that two searches for the
first decided slot above `k` cannot disagree when each certifies that
nothing eligible below its own find was decided. Both commit rules
consume it, five times between them, and stating it separately is what
keeps their case analyses to one line per case. -/
theorem anchor_eq {W : Type*} {Dec : W → ℕ → Option BlockId → Prop}
    {Elig : ℕ → Prop} {k j j₂ : ℕ} {A A₂ : BlockId} {V₂ : W}
    (hkj : k < j) (helig : Elig j) (hkj₂ : k < j₂) (helig₂ : Elig j₂)
    (hj₂ : Dec V₂ j₂ (some A₂))
    (hmid₂ : ∀ i, k < i → i < j₂ → Elig i → Dec V₂ i none)
    (ihj : ∀ V v, Dec V j v → some A = v)
    (ihmid : ∀ i, k < i → i < j → Elig i → ∀ V v, Dec V i v → none = v) :
    j = j₂ ∧ A = A₂ := by
  rcases lt_trichotomy j j₂ with hlt | heq | hgt
  · exact absurd (ihj V₂ none (hmid₂ j hkj hlt helig)) (by simp)
  · subst heq
    exact ⟨rfl, Option.some.inj (ihj V₂ (some A₂) hj₂)⟩
  · exact absurd (ihmid j₂ hkj₂ hgt helig₂ V₂ (some A₂) hj₂) (by simp)

/-- **M6 (agreement).** No two validators reach conflicting decisions for a
slot, whatever views they hold and whichever routes they took.

As with T5 this is *no-conflicting-decision*: a validator that has not yet
decided is not in disagreement.

Structural induction on the first derivation. Of the sixteen constructor
pairings, fifteen close outright — every commit-versus-commit case by M5′,
and the direct-versus-indirect crossings by cross-view M1, the visibility lemma,
or M3. The one real case is *indirect commit against indirect skip*, settled
by comparing the two anchors: if they coincide the IH forces the same anchor
block, and otherwise the earlier anchor is covered by the *other* validator's
intermediate-skip premise, which is exactly the sub-derivation the IH needs.

That is why "nearest anchor" had to be stated positively. The negative
reading would carry no sub-derivation here, and the induction would have
nothing to stand on.

**Why eligibility may not be view-relative.** Since the intermediate premise
now ranges over eligible slots only, invoking the other validator's copy of it
needs `Eligible k j` as a side condition — and what discharges it is *this*
validator's own eligibility premise for the same pair. The two match because
`Eligible` is a predicate on the slot pair alone: both derivations concern the
same `k`, so they agree on which slots may anchor it. Were eligibility indexed
by the decider — "an anchor far enough ahead *as far as I can see*" — the
premises would not meet and this case would not close. -/
theorem decided_unique {V₁ : View Validator BlockId Payload U} {k : ℕ} {v₁ : Option BlockId}
    (h₁ : Decided U V₁ k v₁) :
    ∀ (V₂ : View Validator BlockId Payload U) (v₂ : Option BlockId),
      Decided U V₂ k v₂ → v₁ = v₂ := by
  induction h₁ with
  | @directCommit k L hL h =>
    intro V₂ v₂ h₂
    cases h₂ with
    | directCommit hL₂ h₂ => exact congrArg some (eq_of_directCommitIn hL hL₂ h h₂)
    | directSkip hskip => exact absurd (not_directSkip_of_directCommitIn hL h hskip) not_false
    | indirectCommit _ _ _ _ hL₂ hcert₂ =>
      exact congrArg some (eq_of_hasCertificate hL hL₂
        (certificates_nonempty_of_directCommit (directCommit_of_directCommitIn h))
        (certificates_nonempty_of_certifiedIn hcert₂))
    | @indirectSkip _ j A _ helig hj _ hnone =>
      -- Visibility: this commit is seen from the other validator's anchor.
      -- Their own eligibility premise is what puts it in range.
      exact absurd (certifiedIn_of_directCommitIn_at_anchor h hj helig) (hnone _ hL)
  | @directSkip k hskip =>
    intro V₂ v₂ h₂
    cases h₂ with
    | directCommit hL₂ h₂ => exact absurd (not_directSkip_of_directCommitIn hL₂ h₂ hskip) not_false
    | directSkip _ => rfl
    | indirectCommit _ _ _ _ hL₂ hcert₂ =>
      exact absurd hcert₂ (not_certifiedIn_of_directSkipIn (hskip _ hL₂))
    | indirectSkip _ _ _ _ _ => rfl
  | @indirectCommit k j A L hkj helig hj hmid hL hcert ihj ihmid =>
    intro V₂ v₂ h₂
    cases h₂ with
    | directCommit hL₂ h₂ =>
      exact congrArg some (eq_of_hasCertificate hL hL₂
        (certificates_nonempty_of_certifiedIn hcert)
        (certificates_nonempty_of_directCommit (directCommit_of_directCommitIn h₂)))
    | directSkip hskip₂ =>
      exact absurd hcert (not_certifiedIn_of_directSkipIn (hskip₂ _ hL))
    | indirectCommit _ _ _ _ hL₂ hcert₂ =>
      exact congrArg some (eq_of_hasCertificate hL hL₂
        (certificates_nonempty_of_certifiedIn hcert)
        (certificates_nonempty_of_certifiedIn hcert₂))
    | @indirectSkip _ j₂ A₂ hkj₂ helig₂ hj₂ hmid₂ hnone₂ =>
      -- The one real case: compare the two anchors. Each side's eligibility
      -- premise is exactly the side condition the other's intermediate-skip
      -- premise asks for — which is why `Eligible` may not depend on the view.
      obtain ⟨rfl, rfl⟩ := anchor_eq hkj helig hkj₂ helig₂ hj₂ hmid₂ ihj ihmid
      exact absurd hcert (hnone₂ _ hL)
  | @indirectSkip k j A hkj helig hj hmid hnone ihj ihmid =>
    intro V₂ v₂ h₂
    cases h₂ with
    | directCommit hL₂ h₂ =>
      exact absurd (certifiedIn_of_directCommitIn_at_anchor h₂ hj helig) (hnone _ hL₂)
    | directSkip _ => rfl
    | @indirectCommit _ j₂ A₂ L₂ hkj₂ helig₂ hj₂ hmid₂ hL₂ hcert₂ =>
      obtain ⟨rfl, rfl⟩ := anchor_eq hkj helig hkj₂ helig₂ hj₂ hmid₂ ihj ihmid
      exact absurd hcert₂ (hnone _ hL₂)
    | indirectSkip _ _ _ _ _ => rfl

/-- **M6**, in the shape callers want: two validators' verdicts for a slot
agree. -/
theorem decided_agree {V₁ V₂ : View Validator BlockId Payload U} {k : ℕ}
    {v₁ v₂ : Option BlockId} (h₁ : Decided U V₁ k v₁) (h₂ : Decided U V₂ k v₂) :
    v₁ = v₂ :=
  decided_unique h₁ V₂ v₂ h₂

/-- No two validators commit *different* blocks for one slot. -/
theorem eq_of_decided_commit {V₁ V₂ : View Validator BlockId Payload U} {k : ℕ}
    {L₁ L₂ : BlockId} (h₁ : Decided U V₁ k (some L₁)) (h₂ : Decided U V₂ k (some L₂)) :
    L₁ = L₂ :=
  Option.some.inj (decided_agree h₁ h₂)

/-- No validator commits a slot another has skipped. This is the shape that
matters operationally: a committed block never has to be retracted. -/
theorem not_decided_skip_of_decided_commit {V₁ V₂ : View Validator BlockId Payload U}
    {k : ℕ} {L : BlockId} (h₁ : Decided U V₁ k (some L)) (h₂ : Decided U V₂ k none) :
    False := by
  simpa using decided_agree h₁ h₂

/-! ## The committed-leader sequence

M6 settles each slot in isolation. Because slots are indexed by `ℕ`, that is
already enough to fix the *sequence*: reading verdicts off in slot order and
dropping the skips gives a list, and pointwise agreement makes the lists
equal.

This is the leader half of total-order safety, and it is a corollary rather
than a theorem. The block half — flushing each committed leader's causal
history into a ledger — needs a deterministic order *within* each flush, and
so a `LinearOrder` on ids or an equivalent tie-break, which the development
deliberately does not assume. -/

/-- The blocks committed at slots `0, …, n-1`, in slot order, with skipped
slots dropped. `g` is a validator's verdict assignment. -/
def commitSeq (g : ℕ → Option BlockId) (n : ℕ) : List BlockId :=
  (List.range n).filterMap g

/-- **The committed-leader sequence is agreed.** Two validators that have
settled the first `n` slots — on whatever views, by whatever mix of direct
and indirect routes — read off the same list of committed blocks. -/
theorem commitSeq_agree {V₁ V₂ : View Validator BlockId Payload U} {n : ℕ}
    {g₁ g₂ : ℕ → Option BlockId}
    (h₁ : ∀ k, k < n → Decided U V₁ k (g₁ k))
    (h₂ : ∀ k, k < n → Decided U V₂ k (g₂ k)) :
    commitSeq g₁ n = commitSeq g₂ n := by
  have h : ∀ k ∈ List.range n, g₁ k = g₂ k := by
    intro k hk
    rw [List.mem_range] at hk
    exact decided_agree (h₁ k hk) (h₂ k hk)
  simp only [commitSeq]
  exact List.filterMap_congr h

/-! ## No retraction

A ledger holds every block, not just leaders: committing the leader of slot
`k` outputs everything in its causal history. Ordering *within* one such
flush needs a tie-break the development deliberately does not assume, but
**whether** and **when** a block is output needs no order at all — and that
is what retraction would violate.

Three statements, none of which mentions an order on ids:

* `ledgerSet_mono` — nothing already output is ever dropped;
* `ledgerSet_agree` — two validators output the same blocks;
* `OutputAt` is unique and agreed — each block enters at exactly one slot,
  and validators concur on which.

Together: a block, once written, stays written, in the same place. -/

/-- The blocks output after settling slots `0, …, n-1`: everything in the
causal history of a committed leader. -/
def ledgerSet (U : BlockUniverse Validator BlockId Payload)
    (g : ℕ → Option BlockId) (n : ℕ) : Set BlockId :=
  {b | ∃ k, k < n ∧ ∃ L, g k = some L ∧ Reaches U L b}

omit [DecidableEq BlockId] S in
/-- **Nothing is ever dropped.** The ledger only grows as more slots settle. -/
theorem ledgerSet_mono {g : ℕ → Option BlockId} {n m : ℕ} (h : n ≤ m) :
    ledgerSet U g n ⊆ ledgerSet U g m := by
  rintro b ⟨k, hk, hrest⟩
  exact ⟨k, by omega, hrest⟩

/-- **Two validators output the same blocks.** -/
theorem ledgerSet_agree {V₁ V₂ : View Validator BlockId Payload U} {n : ℕ}
    {g₁ g₂ : ℕ → Option BlockId}
    (h₁ : ∀ k, k < n → Decided U V₁ k (g₁ k))
    (h₂ : ∀ k, k < n → Decided U V₂ k (g₂ k)) :
    ledgerSet U g₁ n = ledgerSet U g₂ n := by
  have hg : ∀ k, k < n → g₁ k = g₂ k := fun k hk => decided_agree (h₁ k hk) (h₂ k hk)
  ext b
  constructor
  · rintro ⟨k, hk, L, hL, hr⟩
    exact ⟨k, hk, L, (hg k hk) ▸ hL, hr⟩
  · rintro ⟨k, hk, L, hL, hr⟩
    exact ⟨k, hk, L, (hg k hk).symm ▸ hL, hr⟩

/-- `b` enters the ledger at slot `k`: the first committed slot whose leader
reaches it. -/
def OutputAt (U : BlockUniverse Validator BlockId Payload)
    (g : ℕ → Option BlockId) (b : BlockId) (k : ℕ) : Prop :=
  (∃ L, g k = some L ∧ Reaches U L b) ∧
    ∀ j, j < k → ∀ L, g j = some L → ¬ Reaches U L b

omit [DecidableEq BlockId] S in
/-- **A block enters the ledger once.** Its position is not merely stable
over time — there is no second slot it could have entered at. -/
theorem outputAt_unique {g : ℕ → Option BlockId} {b : BlockId} {k₁ k₂ : ℕ}
    (h₁ : OutputAt U g b k₁) (h₂ : OutputAt U g b k₂) : k₁ = k₂ := by
  rcases lt_trichotomy k₁ k₂ with h | h | h
  · obtain ⟨L, hL, hr⟩ := h₁.1
    exact absurd hr (h₂.2 k₁ h L hL)
  · exact h
  · obtain ⟨L, hL, hr⟩ := h₂.1
    exact absurd hr (h₁.2 k₂ h L hL)

/-- **And validators agree on which slot that is.** -/
theorem outputAt_agree {V₁ V₂ : View Validator BlockId Payload U} {n : ℕ}
    {g₁ g₂ : ℕ → Option BlockId} {b : BlockId} {k : ℕ}
    (h₁ : ∀ j, j < n → Decided U V₁ j (g₁ j))
    (h₂ : ∀ j, j < n → Decided U V₂ j (g₂ j))
    (hk : k < n) (ho : OutputAt U g₁ b k) : OutputAt U g₂ b k := by
  have hg : ∀ j, j < n → g₁ j = g₂ j := fun j hj => decided_agree (h₁ j hj) (h₂ j hj)
  refine ⟨?_, ?_⟩
  · obtain ⟨L, hL, hr⟩ := ho.1
    exact ⟨L, (hg k hk) ▸ hL, hr⟩
  · intro j hj L hL hr
    exact ho.2 j hj L ((hg j (by omega)).symm ▸ hL) hr

end LeanDag
