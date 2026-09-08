import LeanDag.Properties.Record
import LeanDag.Properties.Arcs.GC
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

end MysticetiProperties

end LeanDag
