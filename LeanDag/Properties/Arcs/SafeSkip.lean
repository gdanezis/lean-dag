import LeanDag.Properties.Extends
import LeanDag.Properties.Band
import LeanDag.Properties.Agree
import LeanDag.Properties.Derived.Persist
import LeanDag.Properties.Derived.FromBand
import LeanDag.Properties.Optional.Skip
import LeanDag.SafeSkip.Basic
import LeanDag.SafeSkip.Invariance
/-!
# Crash recovery, for any protocol with `Persist`

`docs/target-properties.md` G2. `SkipMsg.skipFill` is an extension, so
any protocol with `Persist` recovers a crashed validator through the
generic properties, with no mechanism named but this one.
-/

namespace LeanDag

namespace Properties

namespace Arcs

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
/-! ## Promptness: the fill cannot conjure a commit

A slot whose candidates are all novel is unsupported by any old view
(`Extends.old_refs_old`), so `SkipsUnsupported` skips it at once — SS3
for every rule that shows the property, at every fill. -/

/-- **A slot whose candidates are all novel is skipped**, promptly. -/
theorem decided_none_of_novel {R : DagRule Validator BlockId Payload}
    {Ok : Finset Validator → Prop} (hsk : SkipsUnsupported R Ok)
    {U U' : R.Universe} (he : Extends R U U') (S : Slots Validator)
    {V' : R.View U'} {T : Finset Validator} {k : ℕ} (hok : Ok T)
    (hpres : PresentAt R V' T (S.slotRound k + 1))
    (hnov : ∀ L, R.IsCandidate S U' k L → L ∉ R.ids U)
    (hold : ∀ c, c ∈ R.viewIds V' → (R.block U' c).creator ∈ T →
      (R.block U' c).round = S.slotRound k + 1 → c ∈ R.ids U) :
    R.Decided S V' k none :=
  hsk S U' V' T k hok hpres (unsupported_of_novel he (fun L hL => ⟨hL.1, hnov L hL⟩) hold)

section Faults

variable [Faults Validator]

/-- **The fill is an extension**: it holds every old block unchanged.
Stated through four equations rather than a type equality, so a rule
whose universes are core block universes applies it with `rfl`. -/
theorem extends_of_skipFill (R : DagRule Validator BlockId Payload)
    {U U' : R.Universe} {D : BlockUniverse Validator BlockId Payload}
    (sk : SkipMsg D)
    (hi : R.ids U = D.ids) (hb : R.block U = D.block)
    (hi' : R.ids U' = sk.skipFill.ids) (hb' : R.block U' = sk.skipFill.block) :
    Extends R U U' where
  subset := fun b h => by
    rw [hi'] ; rw [hi] at h
    exact Finset.mem_union_left _ h
  block := fun b h => by
    rw [hi] at h
    rw [hb', hb, sk.skipFill_block_old h]

/-- **Verdicts survive the recovery**, for any protocol with `Persist`. -/
theorem decided_skipFill {R : DagRule Validator BlockId Payload} (hp : Persist R)
    {S : Slots Validator} {U U' : R.Universe}
    {D : BlockUniverse Validator BlockId Payload} (sk : SkipMsg D)
    (hi : R.ids U = D.ids) (hb : R.block U = D.block)
    (hi' : R.ids U' = sk.skipFill.ids) (hb' : R.block U' = sk.skipFill.block)
    {V : R.View U} {V' : R.View U'} (hV : R.viewIds V ⊆ R.viewIds V')
    {k : ℕ} {v : Option BlockId} (h : R.Decided S V k v) :
    R.Decided S V' k v :=
  hp S U U' (extends_of_skipFill R sk hi hb hi' hb') V V' hV k v h

omit [Faults Validator] in
/-- **Agreement across the recovery**, for any extension: `Persist`
carries the earlier verdict up to meet `Agree`. -/
theorem decided_agree_extends {R : DagRule Validator BlockId Payload}
    (ha : Agree R) (hp : Persist R) {S : Slots Validator} {U U' : R.Universe}
    (he : Extends R U U') {V : R.View U} {V' W : R.View U'}
    (hsub : R.viewIds V ⊆ R.viewIds V') {k : ℕ} {v w : Option BlockId}
    (hV : R.Decided S V k v) (hW : R.Decided S W k w) : v = w :=
  ha S V' W k v w (hp S U U' he V V' hsub k v hV) hW

omit [Faults Validator] in
/-- **The prompt skip conflicts with no verdict**, on any further
extension a caught-up view reaches. -/
theorem decided_none_of_novel_agree {R : DagRule Validator BlockId Payload}
    (ha : Agree R) (hb : Banded R) {Ok : Finset Validator → Prop} (hsk : SkipsUnsupported R Ok)
    {U U' : R.Universe} (he : Extends R U U') (S : Slots Validator)
    {V' : R.View U'} {T : Finset Validator} {k : ℕ} (hok : Ok T)
    (hpres : PresentAt R V' T (S.slotRound k + 1))
    (hnov : ∀ L, R.IsCandidate S U' k L → L ∉ R.ids U)
    (hold : ∀ c, c ∈ R.viewIds V' → (R.block U' c).creator ∈ T →
      (R.block U' c).round = S.slotRound k + 1 → c ∈ R.ids U)
    {U'' : R.Universe} (he' : Extends R U' U'') {V'' W : R.View U''}
    (hsub : R.viewIds V' ⊆ R.viewIds V'') {v : Option BlockId} (hW : R.Decided S W k v) :
    v = none :=
  (decided_agree_extends ha (Persist.of_banded hb) he' hsub
    (decided_none_of_novel hsk he S hok hpres hnov hold) hW).symm


/-- **Every candidate of a slot the recovering replica leads, at a gap
round, is a filled block** — the replica authored nothing old there. A
fact about the recovery message alone: no rule appears. -/
theorem candidates_fresh [S : Slots Validator]
    {D : BlockUniverse Validator BlockId Payload} (sk : SkipMsg D) {k : ℕ}
    (hlead : S.leader k = sk.v1) (hk1 : sk.r0 < S.slotRound k) (hk2 : S.slotRound k ≤ sk.r)
    {L : BlockId} (hL : IsLeaderBlock sk.skipFill k L) : L ∉ D.ids := by
  intro hLU
  obtain ⟨-, hLr, hLc⟩ := hL
  rw [sk.skipFill_block_old hLU] at hLr hLc
  exact sk.hgap L hLU (by rw [hLc, hlead]) (by change sk.r0 < _; omega) (by omega)

/-- **The recovering view still holds a present quorum.** The lift adds
blocks and renames nothing, so what was present stays present. Stated
through the same equations as `extends_of_skipFill`. -/
theorem presentAt_liftView (R : DagRule Validator BlockId Payload)
    {U U' : R.Universe} {D : BlockUniverse Validator BlockId Payload} (sk : SkipMsg D)
    (hi : R.ids U = D.ids) (hbU : R.block U = D.block)
    (hb' : R.block U' = sk.skipFill.block)
    {V : R.View U} {V' : R.View U'} (hv : R.viewIds V' = R.viewIds V)
    {T : Finset Validator} {r : ℕ} (h : PresentAt R V T r) : PresentAt R V' T r := by
  intro v hv'
  obtain ⟨c, hcV, hcc, hcr⟩ := h v hv'
  have hcU : c ∈ R.ids U := R.viewSound V hcV
  refine ⟨c, by rw [hv]; exact hcV, ?_, ?_⟩
  · rw [hb', sk.skipFill_block_old (by rw [← hi]; exact hcU), ← hbU]; exact hcc
  · rw [hb', sk.skipFill_block_old (by rw [← hi]; exact hcU), ← hbU]; exact hcr

end Faults
