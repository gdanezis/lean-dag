import LeanDag.FinWhale.Pass
import LeanDag.FinWhale.Model.Liveness
import LeanDag.Mysticeti.ViewPace
/-!
# FinWhale — a validator's holdings are its view

This file ties the schedule-free `View.lean` and liveness results to the
pacing trunk. `PaceCore.holds` — a validator's holdings at a time — is a
view at every instant, since its store clauses are exactly what `IsView`
asks; `PaceCore.holds_roundBlocks` then gives an instant at which the
view holds every reliable block from the coverage round up, which is
what `all_decided_of_view` reads.
-/

namespace LeanDag

namespace FinWhale

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator] [P : Params Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {D : Dag Validator BlockId Payload} {S : Slots Validator}
variable {Elig : ℕ → ℕ → Prop} [DecidableRel Elig]
variable {U : BlockUniverse Validator BlockId Payload} {T : Finset Validator} {M : ℕ}

/-- **A validator's holdings are a view.** `holds_sub` is the subset
clause and `holds_closed` the closure clause. -/
def holdsView (pc : PaceCore U T M) (hids : D.ids = U.ids) (hblk : D.block = U.block)
    {v : Validator} (hv : v ∈ T) (t : ℕ) : D.View :=
  ⟨pc.holds v t, by rw [hids]; exact pc.holds_sub v t,
    by rw [hblk, hids] at *; exact pc.holds_closed v hv t⟩

@[simp] theorem holdsView_ids (pc : PaceCore U T M) (hids : D.ids = U.ids)
    (hblk : D.block = U.block) {v : Validator} (hv : v ∈ T) (t : ℕ) :
    (holdsView (D := D) pc hids hblk hv t).ids = pc.holds v t := rfl

/-- **And by then the view holds every reliable block from the coverage
round up.** Byzantine authors are not covered, and no schedule covers
them: nothing obliges a validator to receive what a faulty validator
never sent. -/
theorem held_of_pace (pc : PaceCore U T M) (hids : D.ids = U.ids) (hblk : D.block = U.block)
    (hle : ∀ u ∈ T, ∀ n ≤ pc.top u, n ≤ pc.built u n)
    (hcard : quorumCard Validator ≤ T.card) {R : ℕ} (hgst : pc.gst ≤ R)
    {v : Validator} (hv : v ∈ T) :
    ∀ n, R ≤ n → n ≤ M → ∀ b ∈ blocksAt D n, (D.block b).creator ∈ T →
      b ∈ pc.holds v (settled pc) := by
  intro n hR hM b hb hbT
  simp only [blocksAt, Finset.mem_filter, hids, hblk] at hb hbT ⊢
  have hg : ∀ u ∈ T, pc.gst ≤ pc.built u n :=
    fun u hu => le_trans (le_trans hgst hR) (hle u hu n (pc.reached hcard n hM u hu))
  have harrive := pc.holds_roundBlocks hM hg v hv b hb.1 hbT hb.2
  refine pc.holds_mono v _ _ ?_ harrive
  exact Finset.le_sup (f := fun m => pc.latest m + pc.delay) (Finset.mem_range.2 (by omega))

/-! ## The capstone: a validator, with nothing about it assumed -/

variable [LinearOrder BlockId]

/-- **Every slot below the horizon is decided**, by a validator whose
view is its own holdings and whose verdicts are the reverse pass. Nothing
about the validator itself is a hypothesis; what remains is about the
schedule and the DAG reaching the rounds. -/
theorem all_decided_of_pass (pc : PaceCore U (Correct : Finset Validator) M)
    (hids : D.ids = U.ids) (hblk : D.block = U.block)
    (hle : ∀ u ∈ (Correct : Finset Validator), ∀ n ≤ pc.top u, n ≤ pc.built u n)
    {R : ℕ} (hgst : pc.gst ≤ R) {v : Validator} (hv : v ∈ (Correct : Finset Validator))
    {choose : BlockId → ℕ → Option BlockId} {Np N r : ℕ}
    (hhorizon : ∀ b ∈ pc.holds v (settled pc), (D.block b).round ≤ Np)
    (hcommits : CommitsCorrectLeaders S D R N) (hrr : RoundRobin S.leader)
    (hEl : ∀ r a, Elig r a ↔ r + 2 < a) (hid : ∀ k, S.slotRound k = k) (hNM : N ≤ M)
    (hN : max r R + (3 * F.f + 5) ≤ N) :
    decOf S Elig (holdsView pc hids hblk hv (settled pc)).toRecord
      choose Np r ≠ Verdict.undecided := by
  have hlt : ∀ r a, Elig r a → r < a := fun r a h => by have := (hEl r a).1 h; omega
  have hrle : ∀ r, S.slotRound r ≤ Np → r ≤ Np := fun r h => by rwa [hid] at h
  exact all_decided_of_view (V := holdsView pc hids hblk hv (settled pc))
    (wellFormed_decOf hhorizon hlt hrle choose)
    (fun n hRn hnN b hb hbc =>
      held_of_pace pc hids hblk hle card_correct hgst hv n hRn (by omega) b hb hbc)
    hcommits hrr hEl hid hN

end FinWhale

end LeanDag
