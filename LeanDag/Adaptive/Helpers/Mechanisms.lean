import LeanDag.Adaptive.Helpers.Chop
import LeanDag.Adaptive.Model.Segment
import LeanDag.Adaptive.Score.Rule
import LeanDag.Properties.Arcs.Record
/-!
# The segmented arc across every mechanism

`Adaptive/Helpers/Chop.lean` composes the arc with one cut. This file
composes it with the rest, at **any carrier on the record** rather than
at a protocol: a rule that reads its universes as block records has the
cut, the fill and re-genesis for free (`Properties/Arcs/Record.lean`),
and what follows says what each does to a configuration and to a
segmented run.

Two shapes, because the mechanisms come in two:

* **A cut renumbers.** `Config.chop` is the configuration the cut leaves,
  and `truncates_chop_config` makes it a `Truncates` at the
  configuration's own schedule. Chained with the others through `Stack`,
  a validator that filled a gap and then pruned twice still reads one
  `Rebased`, so `Stack.safe_and_live` applies at an adaptive schedule.
* **A fill and a re-genesis only add blocks.** The schedule does not move
  and neither does the run: `SegRun.extend` carries a whole segmented run
  across, and its ledger is the same list. The one thing an extension can
  disturb is what the update rule *reads*, which is `UpdStable`.
-/

namespace LeanDag

namespace Adaptive

open Barnacle Properties

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}

/-! ## The cut, and stacks, at a configuration -/

section Cut

open BlockRecord

variable {R : DagRule Validator BlockId Payload}
variable {P : Validity Validator BlockId Payload} {honest : Finset Validator}
variable {I : BlockRecord Validator BlockId Payload P honest → Prop}
variable (c : R.OnRecord P honest I) [P.Mechanised] [Invariant.Mechanised I]
variable {U : R.Universe} {G : ℕ}

/-- **The cut is a truncation at a configuration's own schedule.** The
universe half is the carrier's, the schedule half is the
configuration's, and no fixed slot numbering enters — which is what lets
the cut be taken at a schedule whose rounds differ in width. -/
theorem truncates_chop_config (C : Config Validator) :
    Truncates R U (c.chop U G) C.sched (C.chop G).sched G (C.cum G) :=
  { c.sustains_chop U, C.rebases_chop G with }

/-- **A cut at a configuration is a stack step.** -/
theorem stack_chop_config (C : Config Validator) :
    Stack R U C.sched (c.chop U G) (C.chop G).sched G G (C.cum G) := by
  simpa using Stack.step (Rebased.of_truncates (truncates_chop_config c C)) Stack.nil

/-- **Two cuts at a configuration are one stack**, at the configuration
`Config.chop_chop` names: pruning to `G₁` and then to `G₂` leaves the
configuration of a single cut at `G₁ + G₂`. -/
theorem stack_chop_chop_config (C : Config Validator) (G₁ G₂ : ℕ) :
    Stack R U C.sched (c.chop (c.chop U G₁) G₂) (C.chop (G₁ + G₂)).sched
      (G₁ + G₂) (max G₁ (G₂ + G₁)) (C.cum G₁ + (C.chop G₁).cum G₂) := by
  have h := Stack.step (Rebased.of_truncates (truncates_chop_config c (G := G₁) C))
    (stack_chop_config c (U := c.chop U G₁) (G := G₂) (C.chop G₁))
  rwa [C.chop_chop G₁ G₂] at h

/-! ### The joiner, at any carrier

`Adaptive/Helpers/Chop.lean` states both halves against a `Truncates`
and a `ViewAgreeAbove`. The cut supplies both, so a rule that reads its
universes as records has the joiner and nothing further is asked of it.
-/

/-- **I5's verdict half, at any carrier**: the joiner and the network
give one verdict to every slot both hold, from an arbitrary view of the
truncation. -/
theorem joiner_decided_agree_chop (ha : Agree R) (hb : Banded R) (C : Config Validator)
    {V : R.View U} {W : R.View (c.chop U G)} {k : ℕ} {w v : Option BlockId}
    (hW : R.Decided (C.chop G).sched W k w)
    (hV : R.Decided C.sched V (C.cum G + k) v) : w = v :=
  Adaptive.joiner_decided_agree ha hb (truncates_chop_config c C)
    (c.viewAgreeAbove_chop (V := V)) hW hV

/-- **I5, whole, at any carrier.** A joiner that recomputed its
configuration from its own truncated view, under a horizon-stable score,
runs the network's leaders and derives the network's verdict at every
slot both hold: **pruning does not split the ledger, even when the
schedule is derived from it.** -/
theorem joiner_run_decided_agree (ha : Agree R) (hb : Banded R)
    {score : (U : R.Universe) → R.View U → Config Validator → Config Validator}
    (hs : HorizonStable score G) (C : Config Validator)
    {V : R.View U} {V' : R.View (c.chop U G)} (hv : ViewAgreeAbove R V V' G)
    {W : R.View (c.chop U G)} {k : ℕ} {w v : Option BlockId}
    (hW : R.Decided (score (c.chop U G) V' (C.chop G)).sched W k w)
    (hV : R.Decided (score U V C).sched V ((score U V C).cum G + k) v) : w = v := by
  rw [joiner_config_agree hs hv C] at hW
  exact joiner_decided_agree_chop c ha hb (score U V C) hW hV

section Fill

variable {sk : SkipData (c.toRec U).ids (c.toRec U).block} [P.CopyStable]

/-- **Fill then cut is a stack, at a configuration.** The composition
asks nothing of the rule and nothing of the score: the steps are the
witnesses the mechanisms already have, and `Stack.safe_and_live` reads
the result at the adaptive schedule. -/
theorem stack_copyFill_chop_config (C : Config Validator) :
    Stack R U C.sched (c.chop (c.copyFill U sk) G) (C.chop G).sched
      G (max (sk.r + 1) G) (C.cum G) := by
  simpa using Stack.step (Rebased.of_sustains (S := C.sched) (c.sustains_copyFill U sk))
    (stack_chop_config c (U := c.copyFill U sk) C)

end Fill

end Cut

/-! ## The mechanisms that only add blocks -/

section Extend

variable {R : BaseRule Validator BlockId Payload} {P : Params}

/-- **What an update rule owes a mechanism that adds blocks.** From a
view and any larger view of an extension, the rule installs the same
configuration — asked only at anchors the smaller universe already
holds, which is where a run ever applies it.

`Anchored` is the same independence across two views of **one**
universe; this is the counterpart across two universes, and a mechanism
that only adds blocks is what makes the second universe an extension. A
rule that read the *size* of the universe would fail it, and would
install a different configuration on a validator that had recovered a
crashed peer than on one that had not. -/
def UpdStable (upd : UpdateRule R) : Prop :=
  ∀ (U U' : R.Universe), Extends R.toDagRule U U' →
    ∀ (V : R.View U) (V' : R.View U'), R.toDagRule.viewIds V ⊆ R.toDagRule.viewIds V' →
      ∀ (C : Config Validator) (b : ℕ) (v : ℕ → Option BlockId) (A : BlockId), A ∈ R.ids U →
        upd C b U' V' v A = upd C b U V v A

/-- A rule that does not read the universe is stable. `constRule` is the
case AL15 turns on. -/
theorem updStable_constRule : UpdStable (constRule R) :=
  fun _ _ _ _ _ _ _ _ _ _ _ => rfl

/-- **What a score owes the same mechanisms.** On the anchor's history,
read in a universe and in an extension of it, the score returns one
configuration. The counterpart of `HorizonStable` for the mechanisms
that add blocks rather than remove them, and the reason it is an
obligation and not a theorem is that the two histories are views of
different universes: `Extends` makes them hold the same blocks, and a
score reading only what a block says has the equality, but the type does
not force it. -/
def Score.Stable (score : Score R) : Prop :=
  ∀ (U U' : R.Universe) (he : Extends R.toDagRule U U') (A : BlockId)
    (hA : A ∈ R.ids U) (v : ℕ → Option BlockId) (C : Config Validator),
      score U' (R.historyView U' A (he.subset A hA)) v C = score U (R.historyView U A hA) v C

/-- **A stable score gives a stable rule.** -/
theorem updStable_rule {score : Score R} (hs : score.Stable) : UpdStable (rule score) := by
  intro U U' he V V' _ C b v A hA
  simp only [rule, dif_pos hA, dif_pos (he.subset A hA)]
  rw [hs U U' he A hA v C]

/-- A score that does not read the history is stable: the constant score
and the permuting scores of AL11 are both of that shape. -/
theorem Score.stable_of_ignores {f : Config Validator → Config Validator}
    (score : Score R) (h : ∀ U V v C, score U V v C = f C) : score.Stable :=
  fun _ _ _ _ _ _ C => by rw [h, h]

@[simp] theorem Score.const_stable : (Score.const R).Stable :=
  Score.stable_of_ignores _ (fun _ _ _ _ => rfl)

@[simp] theorem Score.permute_stable (σ : Equiv.Perm Validator) :
    (Score.permute (R := R) σ).Stable :=
  Score.stable_of_ignores _ (fun _ _ _ _ => rfl)

variable {upd : UpdateRule R} {C₀ : Config Validator}

/-- **A segmented run survives any mechanism that only adds blocks.**
The configurations, anchors and verdicts are carried over unchanged —
only the view the decisions are read on moves — so the run on the
extended universe is the same run. -/
def SegRun.extend {U U' : R.Universe} {V : R.View U} {V' : R.View U'} {K : ℕ}
    (hp : Persist R.toDagRule) (hc : CommitsCandidate R.toDagRule)
    (he : Extends R.toDagRule U U')
    (hsub : R.toDagRule.viewIds V ⊆ R.toDagRule.viewIds V') (hu : UpdStable upd)
    (Rn : SegRun R P upd C₀ U V K) : SegRun R P upd C₀ U' V' K where
  start := Rn.start
  cfg := Rn.cfg
  backoff := Rn.backoff
  anchor := Rn.anchor
  vdct := Rn.vdct
  init := Rn.init
  bounds := Rn.bounds
  closed := fun k hk κ h1 h2 => hp _ U U' he V V' hsub _ _ (Rn.closed k hk κ h1 h2)
  anchor_commits := Rn.anchor_commits
  anchor_least := Rn.anchor_least
  start_succ := Rn.start_succ
  update := fun k hk A hA => by
    have hstart : Rn.start k < (Rn.cfg k).roundOf (Rn.anchor k) := by
      have := Rn.start_succ k hk
      have := (Rn.anchor_commits k hk).2
      omega
    have hd := Rn.closed k hk (Rn.anchor k) hstart le_rfl
    rw [hA] at hd
    rw [hu U U' he V V' hsub (Rn.cfg k) (Rn.backoff k) _ A (hc.mem hd)]
    exact Rn.update k hk A hA

/-- **And it outputs the same ledger.** The mechanism adds blocks to the
DAG and changes nothing a validator has already ordered — the claim a
recovery or a re-genesis has to make, now at a schedule the run itself
chose. -/
@[simp] theorem SegRun.extend_ledgerUpto {U U' : R.Universe} {V : R.View U} {V' : R.View U'}
    {K : ℕ} (hp : Persist R.toDagRule) (hc : CommitsCandidate R.toDagRule)
    (he : Extends R.toDagRule U U')
    (hsub : R.toDagRule.viewIds V ⊆ R.toDagRule.viewIds V') (hu : UpdStable upd)
    (Rn : SegRun R P upd C₀ U V K) (K' : ℕ) :
    (Rn.extend hp hc he hsub hu).ledgerUpto K' = Rn.ledgerUpto K' := rfl

end Extend

end Adaptive

end LeanDag
