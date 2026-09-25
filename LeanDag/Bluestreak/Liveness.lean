import LeanDag.Bluestreak.Safety
import LeanDag.Common.Participation
import LeanDag.Common.Anchored.Bounded
/-!
# Bluestreak: liveness above the claims

What a direct commit needs of the DAG, stated without time: the
`T`-authored blocks two rounds above a `T`-led slot claim its
candidate. Reference coverage is not available — a non-leader block
references two blocks — and is not needed: claims are what the rule
counts. A quorum-sized `T` then commits every `T`-led slot directly on
any view caught up to the decision round, three consecutive `T`-led
slots decide everything below them by the relation's descent, and a
fair schedule places such runs past every slot. Where the claims come
from is the reactive schedule's business (`Reactive.lean`).
-/

namespace LeanDag

namespace Bluestreak

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator] [F : Faults Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {U : Universe Validator BlockId Payload} [ClaimMap BlockId]
variable {T : Finset Validator} {R : ℕ} {L : BlockId}

/-- Every `T`-authored block at round `r + 2` claims `L`. -/
def ClaimsAt (U : Universe Validator BlockId Payload) (T : Finset Validator) (r : ℕ)
    (L : BlockId) : Prop :=
  ∀ v ∈ T, ∀ c ∈ U.ids, (U.block c).creator = v → (U.block c).round = r + 2 → Claims U c L

instance (T : Finset Validator) (r : ℕ) (L : BlockId) : Decidable (ClaimsAt U T r L) :=
  inferInstanceAs (Decidable (∀ v ∈ T, ∀ c ∈ U.ids, _ → _ → _))

variable [S : Slots Validator] {k : ℕ}

/-- From round `R` on, every `T`-led slot's candidate is claimed by every
`T`-authored block two rounds above it. -/
def ClaimsOn (U : Universe Validator BlockId Payload) (T : Finset Validator) (R : ℕ) : Prop :=
  ∀ k, R ≤ S.slotRound k → S.leader k ∈ T → ∀ L, IsLeaderBlock U k L →
    ClaimsAt U T (S.slotRound k) L

/-! ## A `T`-led slot commits directly -/

/-- A quorum-sized `T`, populated two rounds above the slot and claiming
its candidate, commits it on any view holding its blocks of that round. -/
theorem directCommitIn_of_claimsAt_held (hcard : quorumCard Validator ≤ T.card)
    (hL : IsLeaderBlock U k L) (hpop : PopulatedOn U T (S.slotRound k + 2))
    (hcl : ClaimsAt U T (S.slotRound k) L) {V : U.View}
    (hheld : ∀ c ∈ U.ids, (U.block c).creator ∈ T → (U.block c).round = S.slotRound k + 2 →
      c ∈ V.ids) :
    DirectCommitIn U V L := by
  refine le_trans hcard (Finset.card_le_card fun u hu => ?_)
  obtain ⟨c, hc, hcc, hcr⟩ := hpop u hu
  refine mem_heldAuthors.mpr ⟨c, Finset.mem_filter.mpr ⟨mem_blocksAt.mpr ⟨hc, ?_⟩, ?_⟩, ?_, hcc⟩
  · rw [hcr, hL.2.1]
  · exact hcl u hu c hc hcc hcr
  · exact hheld c hc (hcc ▸ hu) hcr

/-- The same, on any view caught up to that round. -/
theorem directCommitIn_of_claimsAt (hcard : quorumCard Validator ≤ T.card)
    (hL : IsLeaderBlock U k L) (hpop : PopulatedOn U T (S.slotRound k + 2))
    (hcl : ClaimsAt U T (S.slotRound k) L) {V : U.View}
    (hcov : V.CoversUpto (S.slotRound k + 2)) : DirectCommitIn U V L :=
  directCommitIn_of_claimsAt_held hcard hL hpop hcl fun c hc _ hcr => hcov c hc hcr.le

/-- **The commit half.** A `T`-led slot whose rounds `r` and `r + 2` are
populated and whose candidate is claimed is committed on any view caught
up to `r + 2`. -/
theorem decided_of_leader_mem (hcard : quorumCard Validator ≤ T.card)
    (hcl : ClaimsOn U T R) (hR : R ≤ S.slotRound k) (hlead : S.leader k ∈ T)
    (hpop0 : PopulatedOn U T (S.slotRound k))
    (hpop2 : PopulatedOn U T (S.slotRound k + 2))
    (V : U.View) (hcov : V.CoversUpto (S.slotRound k + 2)) :
    ∃ L, IsLeaderBlock U k L ∧ Decided U V k (some L) := by
  obtain ⟨L, hLm, hLc, hLr⟩ := hpop0 (S.leader k) hlead
  have hL : IsLeaderBlock U k L := ⟨hLm, hLr, hLc⟩
  exact ⟨L, hL, Decided.directCommit hL
    (directCommitIn_of_claimsAt hcard hL hpop2 (hcl k hR hlead L hL) hcov)⟩

/-! ## A run of three decides everything below -/

/-- **Three consecutive `T`-led slots decide every slot below them**, on a
view caught up to the last one's decision round, under a schedule whose
three consecutive slots span eligibility at wave two. -/
theorem decided_below_of_run (hcard : quorumCard Validator ≤ T.card)
    (hspan : (bluestreakAnchored Validator BlockId Payload).SpansEligible (S := S) 3)
    (hcl : ClaimsOn U T R) {b : ℕ} (hR : R ≤ S.slotRound b)
    (hrun : ∀ i, i < 3 → S.leader (b + i) ∈ T)
    (hpop : ∀ n, S.slotRound b ≤ n → n ≤ S.slotRound (b + 2) + 2 → PopulatedOn U T n)
    (V : U.View) (hcov : V.CoversUpto (S.slotRound (b + 2) + 2)) :
    ∀ i, i < b → ∃ v, Decided U V i v := by
  have hleast : ∀ {A : BlockId} {i k : ℕ}, i < (bluestreakAnchored Validator BlockId Payload).rungs →
      (∃ L, IsLeaderBlock U k L ∧ (bluestreakAnchored Validator BlockId Payload).Link i U A L S k) →
      ∃ L, IsLeaderBlock U k L ∧ (bluestreakAnchored Validator BlockId Payload).Link i U A L S k ∧
        (bluestreakAnchored Validator BlockId Payload).Least U A i k L :=
    fun _ ⟨L, hL, hl⟩ => ⟨L, hL, hl, AnchoredRule.least_of_no_tie fun _ _ h => h⟩
  refine AnchoredRule.decided_below_of_run hleast (by omega) hspan
    (Led := fun j => S.leader j ∈ T) hrun fun j h1 h2 hj => ?_
  have hmono : S.slotRound j ≤ S.slotRound (b + 2) := S.mono (by omega)
  have hb : S.slotRound b ≤ S.slotRound j := S.mono h1
  obtain ⟨L, _, hdec⟩ := decided_of_leader_mem hcard hcl (le_trans hR hb) hj
    (hpop _ hb (by omega)) (hpop _ (by omega) (by omega)) V (hcov.mono (by omega))
  exact ⟨L, hdec⟩

/-- **Every slot is decided, eventually**: a fair schedule places a run of
three `T`-led slots past any slot and any round, and a universe populated
and claiming from that round on decides everything below the run. -/
theorem all_decided_below_of_fairRun (hcard : quorumCard Validator ≤ T.card)
    (hspan : (bluestreakAnchored Validator BlockId Payload).SpansEligible (S := S) 3)
    (fair : FairRunOn T 3) (R k : ℕ) :
    ∃ b, k ≤ b ∧ R ≤ S.slotRound b ∧
      ∀ (U : Universe Validator BlockId Payload),
        ClaimsOn U T R → (∀ n, R ≤ n → n ≤ S.slotRound (b + 2) + 2 → PopulatedOn U T n) →
        ∀ i, i < b → ∃ v, Decided U (View.full U) i v := by
  obtain ⟨b, hkb, hRb, hrun⟩ := Slots.exists_run_past fair k R
  refine ⟨b, hkb, hRb, fun U hcl hpop => ?_⟩
  exact decided_below_of_run hcard hspan hcl hRb hrun
    (fun n h1 h2 => hpop n (le_trans hRb h1) h2) _ (View.coversUpto_full U _)

end Bluestreak

end LeanDag
