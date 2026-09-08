import LeanDag.Nemo.Basic
import LeanDag.Common.Support
import LeanDag.Common.History
/-!
# Nemo-Nemo: the commit rule

The crash commit rule at wave length two. Voting and decision share
round `r+1`, so a certificate for a leader block `L` is literally a
round-`(r+1)` block referencing `L`. Direct commit is a majority of
such voters — the existing `supporters` set — and the indirect test, at
link size one, asks for a single vote inside the anchor's cone.

Deliberately absent, compared to the Byzantine core and the hybrid arc:
no `DirectSkip`, since the implementation pins the direct-skip quorum
to the full stake, unreachable once a leader has crashed, so leaders
are skipped only indirectly; and no twin counting, since universal
`no_equivocation` makes the candidate leader block of a slot unique
outright.
-/

namespace LeanDag

namespace Nemo

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {U : Universe Validator BlockId Payload}

/-- **Direct commit**: a majority of round-`(r+1)` authors reference `L`. At
wave length two the votes are the certificates, so the rule counts
`supporters` directly. -/
def DirectCommit (U : Universe Validator BlockId Payload) (L : BlockId) (r : ℕ) : Prop :=
  majority Validator ≤ (supporters U L (r + 1)).card

instance decidableDirectCommit (L : BlockId) (r : ℕ) : Decidable (DirectCommit U L r) :=
  inferInstanceAs (Decidable (majority Validator ≤ (supporters U L (r + 1)).card))

/-- **The indirect test** (link size one): a round-`(r+1)` vote for `L` lies
in the anchor's cone. The name keeps the core's `CertifiedIn` — under crash
the vote block *is* the certificate. Stated over the `history` `Finset`
rather than `Reaches`, so it is decidable. -/
def CertifiedIn (U : Universe Validator BlockId Payload) (A L : BlockId) (r : ℕ) : Prop :=
  ∃ p ∈ history U A, (U.block p).round = r + 1 ∧ L ∈ (U.block p).refs

instance decidableCertifiedIn (A L : BlockId) (r : ℕ) : Decidable (CertifiedIn U A L r) :=
  inferInstanceAs
    (Decidable (∃ p ∈ history U A, (U.block p).round = r + 1 ∧ L ∈ (U.block p).refs))

/-- One hop suffices: a direct reference that votes for `L` certifies. -/
theorem certifiedIn_of_mem_refs {A p L : BlockId} {r : ℕ} (hA : A ∈ U.ids)
    (hp : p ∈ (U.block A).refs) (hr : (U.block p).round = r + 1)
    (hL : L ∈ (U.block p).refs) : CertifiedIn U A L r :=
  ⟨p, mem_history_of_mem_refs hA hp, hr, hL⟩

/-- Cone monotonicity: whatever an anchor certifies, everything above the
anchor certifies too. -/
theorem certifiedIn_of_reaches {B A L : BlockId} {r : ℕ} (hB : B ∈ U.ids)
    (h : Reaches U B A) (hcert : CertifiedIn U A L r) : CertifiedIn U B L r := by
  obtain ⟨p, hp, hr, hL⟩ := hcert
  exact ⟨p, history_subset_of_reaches hB h hp, hr, hL⟩

/-- **The base case.** A directly committed leader has a vote among the
references of every round-`(r+2)` block: the block's majority of referenced
round-`(r+1)` authors must meet the majority of supporters. -/
theorem exists_vote_ref_of_directCommit {L c : BlockId} {r : ℕ}
    (hdc : DirectCommit U L r) (hc : c ∈ U.ids) (hcr : (U.block c).round = r + 2) :
    ∃ p ∈ (U.block c).refs, (U.block p).round = r + 1 ∧ L ∈ (U.block p).refs := by
  obtain ⟨p, hp_mem, hp_P⟩ :=
    exists_mem_refs_of_honest_support_of_card (Q := fun q => L ∈ (U.block q).refs)
      (fun v hv => mem_supporters.mp hv) (fun _ _ => Finset.mem_univ _)
      (lt_card_add_majority hdc) hc (by omega)
  refine ⟨p, hp_mem, ?_, hp_P⟩
  have := U.round_of_mem_refs hc hp_mem
  omega

/-- **Link integrity.** A directly committed leader is certified in every
block at round `r+2` or above — in particular in every eligible anchor. The
depth induction is the generic propagation lemma; the quorum intersection
lives entirely in the base case. -/
theorem certifiedIn_of_directCommit {L A : BlockId} {r : ℕ}
    (hdc : DirectCommit U L r) (hA : A ∈ U.ids) (hAr : r + 2 ≤ (U.block A).round) :
    CertifiedIn U A L r := by
  obtain ⟨p, ⟨hp_ids, hp_round, hp_L⟩, hreach⟩ :=
    reaches_pred_of_round_le
      (Q := fun p => p ∈ U.ids ∧ (U.block p).round = r + 1 ∧ L ∈ (U.block p).refs)
      (fun c hc hcr => by
        obtain ⟨p, hp_mem, hp_round, hp_L⟩ := exists_vote_ref_of_directCommit hdc hc hcr
        exact ⟨p, ⟨U.complete c hc p hp_mem, hp_round, hp_L⟩, Reaches.single hp_mem⟩)
      hA hAr
  exact ⟨p, (mem_history_iff hA).mpr hreach, hp_round, hp_L⟩

end Nemo

end LeanDag
