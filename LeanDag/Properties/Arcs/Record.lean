import LeanDag.Properties.Record
import LeanDag.Properties.Derived.Truncate
import LeanDag.Properties.Derived.FromBand
import LeanDag.Properties.Arcs.GC
import LeanDag.Properties.Arcs.SafeSkip
import LeanDag.Properties.Arcs.Stack
/-!
# The verdict cells, at any carrier on the record

A carrier read as records with `Banded` and `Agree` has every verdict
cell of the cut, the fill and re-genesis for free: transport of a
verdict at the same validator, and agreement between a validator that
ran the mechanism and one that did not. A rule's mechanism cell is
therefore the `OnRecord` instance and nothing else;
`scripts/audit-mechanisms.py` reads an instance as the cell.
-/

namespace LeanDag

namespace Properties

namespace DagRule.OnRecord

open BlockRecord

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {R : DagRule Validator BlockId Payload}
variable {P : Validity Validator BlockId Payload} {honest : Finset Validator}
variable {I : BlockRecord Validator BlockId Payload P honest → Prop}
variable (c : R.OnRecord P honest I) [P.Mechanised] [Invariant.Mechanised I]
variable {S : Slots Validator} {U : R.Universe} {G d : ℕ}

/-! ## The cut -/

/-- **Verdict transport across the cut.** A validator that pruned below
the horizon reaches exactly the verdicts it would have reached with its
whole history, at the re-indexed slot. -/
theorem decided_chop_iff (hb : Banded R) (hd : G ≤ S.slotRound d)
    {V : R.View U} {k : ℕ} {v : Option BlockId} :
    R.Decided S V (d + k) v ↔ R.Decided (S.chop G d hd) (c.chopView V G) k v :=
  LocalTruncate.of_banded hb S (S.chop G d hd) U (c.chop U G) G d (c.truncates_chop U hd)
    V (c.chopView V G) c.viewAgreeAbove_chop k v

/-- **Cross-cut agreement**, from an arbitrary view of the truncation. -/
theorem decided_agree_chop (ha : Agree R) (hb : Banded R) (hd : G ≤ S.slotRound d)
    {W : R.View (c.chop U G)} {V : R.View U} {k : ℕ} {w v : Option BlockId}
    (hW : R.Decided (S.chop G d hd) W k w) (hV : R.Decided S V (d + k) v) : w = v :=
  Arcs.decided_agree_truncate ha (LocalTruncate.of_banded hb) (c.truncates_chop U hd)
    c.viewAgreeAbove_chop hW hV

/-! ## The fill -/

variable {sk : SkipData (c.toRec U).ids (c.toRec U).block} {B : sk.Blocks}
variable {hB : ∀ k, sk.r0 < k → k ≤ sk.r → P (sk.fillMap B) (B.blk k)}
variable {hI : I (BlockRecord.fill (c.toRec U) sk B hB)}

/-- **Verdicts survive the recovery.** The replica that recovered
reaches every verdict it reached before. -/
theorem decided_fill (hb : Banded R) {V : R.View U} {k : ℕ} {v : Option BlockId}
    (h : R.Decided S V k v) : R.Decided S (c.liftView (hI := hI) V) k v :=
  Persist.of_banded hb S U _ c.extends_fill V _ (c.viewIds_subset_liftView V) k v h

/-- **And agreement across it**: a validator that recovered agrees with
one that did not, from any view of the fill. -/
theorem decided_agree_fill (ha : Agree R) (hb : Banded R) {V : R.View U}
    {W : R.View (c.fill U sk B hB hI)} {k : ℕ} {v w : Option BlockId}
    (hV : R.Decided S V k v) (hW : R.Decided S W k w) : v = w :=
  Arcs.decided_agree_extends ha (Persist.of_banded hb) c.extends_fill
    (V' := c.liftView V) (c.viewIds_subset_liftView V) hV hW

section Copy

variable [P.CopyStable]

/-- **Verdicts survive the copy fill.** -/
theorem decided_copyFill (hb : Banded R) (sk : SkipData (c.toRec U).ids (c.toRec U).block)
    {V : R.View U} {k : ℕ} {v : Option BlockId}
    (h : R.Decided S V k v) : R.Decided S (c.liftViewCopy sk V) k v :=
  c.decided_fill hb h

/-- **And agreement across it.** -/
theorem decided_agree_copyFill (ha : Agree R) (hb : Banded R)
    (sk : SkipData (c.toRec U).ids (c.toRec U).block) {V : R.View U}
    {W : R.View (c.copyFill U sk)} {k : ℕ} {v w : Option BlockId}
    (hV : R.Decided S V k v) (hW : R.Decided S W k w) : v = w :=
  c.decided_agree_fill ha hb hV hW

/-- **Fill then cut is a stack.** The composition asks nothing of the
rule: the two steps are the witnesses the mechanisms already have, and
`Stack.safe_and_live` reads the result. -/
theorem stack_copyFill_chop (sk : SkipData (c.toRec U).ids (c.toRec U).block)
    (hd : G ≤ S.slotRound d) :
    Stack R U S (c.chop (c.copyFill U sk) G) (S.chop G d hd) G (max (sk.r + 1) G) d := by
  simpa using Stack.step (Rebased.of_sustains (S := S) (c.sustains_copyFill U sk))
    (Stack.step (Rebased.of_truncates (c.truncates_chop (c.copyFill U sk) hd)) Stack.nil)

end Copy

/-! ## Re-genesis -/

variable {v : Validator} {g : BlockId} {p : Payload}
variable {hg : g ∉ (c.toRec U).ids} {hsev : ∀ b ∈ (c.toRec U).ids, ((c.toRec U).block b).creator ≠ v}

/-- **Verdicts survive re-genesis**, on any view holding the old one. -/
theorem decided_addGenesis (hb : Banded R) {V : R.View U}
    {V' : R.View (c.addGenesis U v g p hg hsev)} (hsub : R.viewIds V ⊆ R.viewIds V')
    {k : ℕ} {u : Option BlockId} (h : R.Decided S V k u) : R.Decided S V' k u :=
  Persist.of_banded hb S U _ c.extends_addGenesis V V' hsub k u h

/-- **And agreement across it.** -/
theorem decided_agree_addGenesis (ha : Agree R) (hb : Banded R) {V : R.View U}
    {V' V'' : R.View (c.addGenesis U v g p hg hsev)} (hsub : R.viewIds V ⊆ R.viewIds V')
    {k : ℕ} {u u' : Option BlockId} (h : R.Decided S V k u) (h' : R.Decided S V'' k u') :
    u = u' :=
  Arcs.decided_agree_extends ha (Persist.of_banded hb) c.extends_addGenesis (V' := V') hsub h h'

end DagRule.OnRecord

end Properties

end LeanDag
