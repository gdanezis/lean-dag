import LeanDag.Adaptive.Helpers.Mechanisms
import LeanDag.Integration.Joiner
/-!
# The segmented arc across the mechanisms, applied

What `Adaptive/Helpers/Mechanisms.lean` is for: a rule that reads its
universes as block records gets the cut, the fill and re-genesis under an
adaptive schedule with nothing left to state. The obligations are
discharged here at the scores AL11 names, and the composite is exhibited
at the core.

Everything below is an application of a proved statement, not a
restatement of one.
-/

namespace LeanDagTest

namespace Adaptive

open LeanDag LeanDag.Adaptive LeanDag.Barnacle LeanDag.Properties

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}

/-! ## The obligations, at the scores AL11 names -/

section Scores

variable {R : BaseRule Validator BlockId Payload}

/-- **A permuting score's rule is stable.** It reads the anchor's history
not at all, so a recovery or a re-genesis leaves the configuration it
installs alone. -/
example (σ : Equiv.Perm Validator) : UpdStable (rule (Score.permute (R := R) σ)) :=
  updStable_rule (Score.permute_stable σ)

/-- And so is the constant score's, which is `constRule`. -/
example : UpdStable (rule (Score.const R)) := updStable_rule Score.const_stable

/-- The constant score is horizon-stable at every cut, so the same score
discharges both obligations — the one for mechanisms that remove blocks
and the one for mechanisms that add them. -/
example (G : ℕ) (v : ℕ → Option BlockId) :
    HorizonStable (R := R.toDagRule) (fun U V C => Score.const R U V v C) G :=
  horizonStable_const G

/-- **And so is a permuting score**, which is the case worth having: it
moves the leaders, and a joiner running it still computes the network's
schedule whatever the horizon. Both obligations are discharged for
AL11's reassignment family, not only for the score that does nothing. -/
example (σ : Equiv.Perm Validator) (G : ℕ) (v : ℕ → Option BlockId) :
    HorizonStable (R := R.toDagRule) (fun U V C => Score.permute (R := R) σ U V v C) G :=
  horizonStable_relabel σ (fun C r i j hi hj h => C.keyed r i j hi hj (σ.injective h)) G

/-- **A score that reads the anchor's history is stable.** The obligation
`SegRun.extend` carries is met by the realistic rule and not only by the
degenerate ones: a reputation score reads what the anchor reaches, and a
fill or a re-genesis leaves that alone. -/
example (hL : R.Laws) (score : Score R)
    (h : ∀ (U U' : R.Universe) (V : R.View U) (V' : R.View U'),
      R.viewIds V = R.viewIds V' →
      (∀ b ∈ R.viewIds V, R.block U b = R.block U' b) →
      ∀ v C, score U V v C = score U' V' v C) :
    UpdStable (rule score) :=
  updStable_rule (Score.stable_of_readsHistory hL score h)

end Scores

/-! ## The mechanisms that add blocks, at any carrier -/

section OnRecord

open LeanDag.BlockRecord

variable {R : BaseRule Validator BlockId Payload} {P : Params}
variable {Pv : Validity Validator BlockId Payload} {honest : Finset Validator}
variable {I : BlockRecord Validator BlockId Payload Pv honest → Prop}
variable (c : R.toDagRule.OnRecord Pv honest I) [Pv.Mechanised] [BlockRecord.Invariant.Mechanised I]
variable {upd : UpdateRule R} {C₀ : Config Validator} {U : R.Universe}

/-- **A recovery does not change what a segmented run has ordered.** The
fill is the record's, the rule's only obligation is `UpdStable`, and the
ledger is the same list. -/
example [Pv.CopyStable] (ha : Properties.Banded R.toDagRule)
    (hc : Properties.CommitsCandidate R.toDagRule)
    (sk : SkipData (c.toRec U).ids (c.toRec U).block)
    (hu : UpdStable upd) {V : R.View U} {K : ℕ} (Rn : SegRun R P upd C₀ U V K) (K' : ℕ) :
    (Rn.extend (Persist.of_banded ha) hc (c.extends_copyFill U sk)
      (le_of_eq (c.viewIds_liftViewCopy sk V).symm) hu).ledgerUpto K' = Rn.ledgerUpto K' :=
  SegRun.extend_ledgerUpto _ _ _ _ _ _ _

/-- **Nor does a re-genesis**, on any view of it holding the old one. -/
example (ha : Properties.Banded R.toDagRule)
    (hc : Properties.CommitsCandidate R.toDagRule)
    {v : Validator} {g : BlockId} {p : Payload} {hg : g ∉ (c.toRec U).ids}
    {hsev : ∀ b ∈ (c.toRec U).ids, ((c.toRec U).block b).creator ≠ v}
    (hu : UpdStable upd) {V : R.View U}
    {V' : R.View (c.addGenesis U v g p hg hsev)}
    (hsub : R.toDagRule.viewIds V ⊆ R.toDagRule.viewIds V')
    {K : ℕ} (Rn : SegRun R P upd C₀ U V K) (K' : ℕ) :
    (Rn.extend (Persist.of_banded ha) hc c.extends_addGenesis hsub hu).ledgerUpto K'
      = Rn.ledgerUpto K' :=
  SegRun.extend_ledgerUpto _ _ _ _ _ _ _

end OnRecord

end Adaptive

end LeanDagTest
