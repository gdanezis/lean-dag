import LeanDag.Properties.Record
import LeanDag.Properties.Arcs.GC
import LeanDag.SafeSkip.Invariance
import LeanDag.SafeSkip.Basic
import LeanDag.Properties.Arcs.SafeSkip
import LeanDag.Properties.Derived.Truncate
import LeanDag.Properties.Sustain
import LeanDag.GC.Chop
import LeanDag.GC.ChopDecided
import LeanDag.Mysticeti.Properties
/-!
# Mysticeti on the record

The witness that the core's universes are block records, from which the cut, the copy fill and
re-genesis are the record's own and every verdict cell is
`Properties/Arcs/Record.lean` at this instance.
-/

namespace LeanDag

namespace MysticetiProperties

open LeanDag.Properties
open LeanDag.Properties.Arcs

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}

section Core

variable [Faults Validator] {U : BlockUniverse Validator BlockId Payload} {G : ℕ}

/-- **The core's carrier, read as block records**: both maps are the
identity. -/
def onRecord :
    (MysticetiProperties.mysticetiRule (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload)).OnRecord ValidWrt (Correct : Finset Validator) BlockRecord.Any where
  toRec := fun U => U
  inv := fun _ => True.intro
  ofRec := fun W _ => W
  ids_to := fun _ => rfl
  block_to := fun _ => rfl
  ids_of := fun _ _ => rfl
  block_of := fun _ _ => rfl
  toView := fun V => V
  ofView := fun V => V
  viewIds_to := fun _ => rfl
  viewIds_of := fun _ => rfl

/-- **The cut sustains the core from its horizon.** The record's witness. -/
theorem sustains_chop :
    Sustains (MysticetiProperties.mysticetiRule (Payload := Payload)) U (chop U G) G G :=
  onRecord.sustains_chop U

/-- **The reactive commit survives the cut** — the consumer test, from
the obligation rather than from `chop` directly. -/
theorem directCommit_chop {T : Finset Validator} {r : ℕ} {L : BlockId}
    (hr : G ≤ r) (hcard : quorumCard Validator ≤ T.card)
    (hpop : LeanDag.PopulatedOn U T (r + 2)) (hc : CertifiesAt U T r L) :
    DirectCommit (chop U G) L (r - G) :=
  MysticetiProperties.directCommit_of_sustains sustains_chop hr hr hcard hpop hc

end Core

/-! ## The canonical cut is a truncation, and the arc's theorems follow

What is left is the witness that the cut stands in `Truncates`; the
arc's own transport theorems then come out of the band property with no
induction, where `GC/ChopDecided.lean` proves them by hand. -/

section CoreTruncate

variable [Faults Validator] {U : BlockUniverse Validator BlockId Payload}
variable {S : Slots Validator} {G d : ℕ}

/-- **The cut is a truncation.** The witness `Truncates` was written to
have, exhibited before anything is proved from it. -/
theorem truncates_chop (hd : G ≤ S.slotRound d) :
    Truncates (MysticetiProperties.mysticetiRule (Payload := Payload))
      U (chop U G) S (S.chop G d hd) G d :=
  onRecord.truncates_chop U hd

/-- **G3 re-derived, with no induction of its own.** Both directions of
the cut's verdict transport, from the band. -/
theorem decided_chop_iff (hd : G ≤ S.slotRound d)
    {V : View Validator BlockId Payload U} {k : ℕ} {v : Option BlockId} :
    Decided U V (d + k) v ↔ Decided (S := S.chop G d hd) (chop U G) (V.chop G) k v :=
  LocalTruncate.of_banded MysticetiProperties.banded
    S (S.chop G d hd) U (chop U G) G d (truncates_chop hd) V (V.chop G)
    (fun b hb hr => by
      show b ∈ V.ids ↔ b ∈ (V.chop G).ids
      rw [BlockRecord.View.chop_ids, Finset.mem_filter]
      exact ⟨fun h => ⟨h, hr⟩, fun h => h.1⟩) k v

/-- **The chopped view agrees with the original above the cut**, which
is the view hypothesis the two theorems below need. -/
theorem viewAgreeAbove_chop {V : View Validator BlockId Payload U} :
    ViewAgreeAbove (MysticetiProperties.mysticetiRule (Payload := Payload))
      V (V.chop G) G :=
  fun b _ hr => by
    show b ∈ V.ids ↔ b ∈ (V.chop G).ids
    rw [BlockRecord.View.chop_ids, Finset.mem_filter]
    exact ⟨fun h => ⟨h, hr⟩, fun h => h.1⟩

/-- **G4 re-derived.** `GC/ChopDecided.decided_agree_chop` proves this
by running the core's uniqueness inside the truncation and carrying the
verdict across by induction. Here it is two properties applied. -/
theorem decided_agree_chop (hd : G ≤ S.slotRound d)
    {W : View Validator BlockId Payload (chop U G)}
    {V : View Validator BlockId Payload U} {k : ℕ} {w v : Option BlockId}
    (hW : Decided (S := S.chop G d hd) (chop U G) W k w)
    (hV : Decided U V (d + k) v) : w = v :=
  decided_agree_truncate MysticetiProperties.agree
    (LocalTruncate.of_banded MysticetiProperties.banded)
    (truncates_chop hd) viewAgreeAbove_chop hW hV

/-- **G8 re-derived.** Validators at different horizons agree. -/
theorem decided_agree_horizons_chop {G₁ G₂ d₁ d₂ : ℕ}
    (hd₁ : G₁ ≤ S.slotRound d₁) (hd₂ : G₂ ≤ S.slotRound d₂)
    {W₁ : View Validator BlockId Payload (chop U G₁)}
    {W₂ : View Validator BlockId Payload (chop U G₂)}
    {V : View Validator BlockId Payload U}
    {k₁ k₂ : ℕ} (halign : d₁ + k₁ = d₂ + k₂) {w₁ w₂ v : Option BlockId}
    (hW₁ : Decided (S := S.chop G₁ d₁ hd₁) (chop U G₁) W₁ k₁ w₁)
    (hW₂ : Decided (S := S.chop G₂ d₂ hd₂) (chop U G₂) W₂ k₂ w₂)
    (hV : Decided U V (d₁ + k₁) v) : w₁ = w₂ :=
  decided_agree_horizons MysticetiProperties.agree
    (LocalTruncate.of_banded MysticetiProperties.banded)
    (truncates_chop hd₁) (truncates_chop hd₂)
    viewAgreeAbove_chop viewAgreeAbove_chop halign hW₁ hW₂ hV

/-- **And so does non-equivocation**, from the truncation. -/
theorem noEquivOn_chop (hd : G ≤ S.slotRound d) {T : Finset Validator}
    (hne : NoEquivOn (MysticetiProperties.mysticetiRule (Payload := Payload)) U T) :
    NoEquivOn (MysticetiProperties.mysticetiRule (Payload := Payload)) (chop U G) T :=
  noEquivOn_of_truncates (truncates_chop hd) hne

end CoreTruncate

/-! ## For the core -/

variable [Faults Validator]

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
  MysticetiProperties.onRecord.sustains_fill (U := U) (sk := sk) (B := sk.selfBlocks U.complete)
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

end MysticetiProperties

end LeanDag
