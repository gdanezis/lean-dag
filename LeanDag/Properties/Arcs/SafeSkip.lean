import LeanDag.Properties.Extends
import LeanDag.Properties.Derived.Persist
import LeanDag.Properties.Optional.Skip
import LeanDag.SafeSkip.Basic
import LeanDag.SafeSkip.Invariance
import LeanDag.Mysticeti.Properties
import LeanDag.Odontoceti.Properties
import LeanDag.MahiMahi.Properties
import LeanDag.Properties.Arcs.GC
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

/-! ## For the core -/

section Core

variable {U : BlockUniverse Validator BlockId Payload}

/-- **Verdicts survive the core's fill**, from the core's `Persist`. -/
theorem decided_fill_of_persist [S : Slots Validator] (sk : SkipMsg U)
    {V : View Validator BlockId Payload U} {k : ℕ} {v : Option BlockId}
    (h : Decided U V k v) :
    Decided sk.skipFill (sk.liftView V) k v :=
  decided_skipFill (R := MysticetiProperties.mysticetiRule) MysticetiProperties.persist sk
    (U := U) (U' := sk.skipFill) rfl rfl rfl rfl (fun _ hb => hb) h

/-- **Agreement across the core's recovery**: a verdict reached before
agrees with any reached after. -/
theorem decided_fill_agree_of_properties [S : Slots Validator] (sk : SkipMsg U)
    {V : View Validator BlockId Payload U}
    {W : View Validator BlockId Payload sk.skipFill} {k : ℕ} {v w : Option BlockId}
    (hv : Decided U V k v) (hw : Decided sk.skipFill W k w) : v = w :=
  MysticetiProperties.agree S (sk.liftView V) W k v w (decided_fill_of_persist sk hv) hw

/-! ### What the fill sustains -/

/-- **A fill sustains from the top of its gap**: above `sk.r` nothing
was added. Below it the claim is false, deliberately — a filled block
stands in for one that voted, and need not vote as it did. -/
theorem sustains_skipFill (sk : SkipMsg U) :
    Sustains (MysticetiProperties.mysticetiRule (Payload := Payload))
      U sk.skipFill 0 (sk.r + 1) :=
  coreOnRecord.sustains_fill (U := U) (sk := sk) (B := sk.selfBlocks U.complete)
    (hB := fun _ hk1 hk2 => sk.fillBlock_valid hk1 hk2) (hI := True.intro)

/-! ### The filled slot is decided, and SS3 falls out

`SafeSkip.directSkip_fresh` (SS3) as a *verdict*: the fill is an
extension, so its candidates are unsupported by the old view, and the
core skips what nothing supports. SS3's hypothesis `v1 ∉ T` is not
needed: `hgap` already rules the recovering replica out of any `T`
present at a gap round. -/

/-- Presence in the pre-crash view is presence in the lifted one: the
ids are the same and old blocks are unchanged. -/
theorem presentAt_liftView [S : Slots Validator] (sk : SkipMsg U)
    {V : View Validator BlockId Payload U} {T : Finset Validator} {r : ℕ}
    (h : PresentAt MysticetiProperties.mysticetiRule V T r) :
    PresentAt MysticetiProperties.mysticetiRule (sk.liftView V) T r := by
  intro v hv
  obtain ⟨c, hcV, hcc, hcr⟩ := h v hv
  have hcU : c ∈ U.ids := V.subset_ids hcV
  refine ⟨c, hcV, ?_, ?_⟩
  · show (sk.skipFill.block c).creator = v
    rw [sk.skipFill_block_old hcU]; exact hcc
  · show (sk.skipFill.block c).round = r
    rw [sk.skipFill_block_old hcU]; exact hcr

/-- **Every candidate of a slot the recovering replica leads, at a gap
round, is a filled block** — the replica authored nothing old there. -/
theorem candidates_fresh [S : Slots Validator] (sk : SkipMsg U) {k : ℕ}
    (hlead : S.leader k = sk.v1) (hk1 : sk.r0 < S.slotRound k) (hk2 : S.slotRound k ≤ sk.r)
    {L : BlockId} (hL : IsLeaderBlock sk.skipFill k L) : L ∉ U.ids := by
  intro hLU
  obtain ⟨-, hLr, hLc⟩ := hL
  rw [sk.skipFill_block_old hLU] at hLr hLc
  exact sk.hgap L hLU (by rw [hLc, hlead]) (by change sk.r0 < _; omega) (by omega)

/-- **SS3, as a verdict, from the properties.** The slot the recovering
replica leads at a gap round is decided `none` on the lifted view, given
a quorum of the pre-crash view present one round above it. No induction;
the fill is an extension, and the core skips what nothing supports. -/
theorem decided_none_fresh [S : Slots Validator] (sk : SkipMsg U)
    {V : View Validator BlockId Payload U} {T : Finset Validator} {k : ℕ}
    (hcard : quorumCard Validator ≤ T.card)
    (hlead : S.leader k = sk.v1) (hk1 : sk.r0 < S.slotRound k) (hk2 : S.slotRound k ≤ sk.r)
    (hpres : PresentAt MysticetiProperties.mysticetiRule V T (S.slotRound k + 1)) :
    Decided sk.skipFill (sk.liftView V) k none :=
  decided_none_of_novel MysticetiProperties.skipsUnsupported
    (extends_of_skipFill MysticetiProperties.mysticetiRule sk rfl rfl rfl rfl) S hcard
    (presentAt_liftView sk hpres) (fun L hL => candidates_fresh sk hlead hk1 hk2 hL)
    (fun c hcV _ _ => V.subset_ids hcV)

/-- **And the skip conflicts with no verdict**: any view of the fill, or
of any extension of it a caught-up view reaches, decides the slot
`none` if at all. -/
theorem decided_none_fresh_agree [S : Slots Validator] (sk : SkipMsg U)
    {V : View Validator BlockId Payload U} {T : Finset Validator} {k : ℕ}
    (hcard : quorumCard Validator ≤ T.card)
    (hlead : S.leader k = sk.v1) (hk1 : sk.r0 < S.slotRound k) (hk2 : S.slotRound k ≤ sk.r)
    (hpres : PresentAt MysticetiProperties.mysticetiRule V T (S.slotRound k + 1))
    {U'' : BlockUniverse Validator BlockId Payload}
    (he' : Extends MysticetiProperties.mysticetiRule sk.skipFill U'')
    {V'' W : View Validator BlockId Payload U''} (hsub : (sk.liftView V).ids ⊆ V''.ids)
    {v : Option BlockId} (hW : Decided U'' W k v) : v = none :=
  (decided_agree_extends MysticetiProperties.agree (Persist.of_banded MysticetiProperties.banded)
    he' (V := sk.liftView V) (V' := V'') hsub (decided_none_fresh sk hcard hlead hk1 hk2 hpres) hW).symm

end Core

end Faults

/-! ### The prompt skip, for Odontoceti

The fill's verdict cells are `Arcs/Record.lean` at `odontocetiOnRecord`;
what is stated here is the prompt skip, which reads the rule's
`SkipsUnsupported`. -/

section Odontoceti

variable [Faults5 Validator] {B : Type} [LinearOrder B]
variable {W : BlockUniverse Validator B Payload}

/-- **SS3 for Odontoceti**: the slot the recovering replica leads at a
gap round is skipped at once, from its `SkipsUnsupported`. -/
theorem decided_none_fresh_odontoceti [S : Slots Validator] (sk : SkipMsg W)
    {V : View Validator B Payload W} {T : Finset Validator} {k : ℕ}
    (hcard : quorumCard Validator ≤ T.card)
    (hlead : S.leader k = sk.v1) (hk1 : sk.r0 < S.slotRound k) (hk2 : S.slotRound k ≤ sk.r)
    (hpres : PresentAt (OdontocetiProperties.odontocetiRule (Payload := Payload)) V T
      (S.slotRound k + 1)) :
    Odontoceti.Decided (U := sk.skipFill) (sk.liftView V) k none :=
  decided_none_of_novel OdontocetiProperties.skipsUnsupported
    (extends_of_skipFill (OdontocetiProperties.odontocetiRule (Payload := Payload)) sk
      (U := W) (U' := sk.skipFill) rfl rfl rfl rfl) S hcard
    (fun v hv => by
      obtain ⟨c, hcV, hcc, hcr⟩ := hpres v hv
      have hcU : c ∈ W.ids := V.subset_ids hcV
      refine ⟨c, hcV, ?_, ?_⟩
      · show (sk.skipFill.block c).creator = v
        rw [sk.skipFill_block_old hcU]; exact hcc
      · show (sk.skipFill.block c).round = S.slotRound k + 1
        rw [sk.skipFill_block_old hcU]; exact hcr)
    (fun L hL => candidates_fresh sk hlead hk1 hk2 hL)
    (fun c hcV _ _ => V.subset_ids hcV)

/-- **And it conflicts with no verdict.** -/
theorem decided_none_fresh_agree_odontoceti [S : Slots Validator] (sk : SkipMsg W)
    {V : View Validator B Payload W} {T : Finset Validator} {k : ℕ}
    (hcard : quorumCard Validator ≤ T.card)
    (hlead : S.leader k = sk.v1) (hk1 : sk.r0 < S.slotRound k) (hk2 : S.slotRound k ≤ sk.r)
    (hpres : PresentAt (OdontocetiProperties.odontocetiRule (Payload := Payload)) V T
      (S.slotRound k + 1))
    {U'' : BlockUniverse Validator B Payload}
    (he' : Extends (OdontocetiProperties.odontocetiRule (Payload := Payload)) sk.skipFill U'')
    {V'' Y : View Validator B Payload U''} (hsub : (sk.liftView V).ids ⊆ V''.ids)
    {v : Option B} (hY : Odontoceti.Decided U'' Y k v) : v = none :=
  (decided_agree_extends OdontocetiProperties.agree
    (Persist.of_banded OdontocetiProperties.banded) he' (V := sk.liftView V) (V' := V'') hsub
    (decided_none_fresh_odontoceti sk hcard hlead hk1 hk2 hpres) hY).symm

end Odontoceti

