import LeanDag.Properties.Truncate
import LeanDag.Properties.Sustain
import LeanDag.GC.Chop
import LeanDag.GC.ChopDecided
import LeanDag.Mysticeti.Properties
import LeanDag.Odontoceti.Properties
import LeanDag.MahiMahi.Properties
import LeanDag.Properties.Band
import LeanDag.Properties.Derived.Truncate
import LeanDag.Properties.Record
/-!
# Garbage collection, for any protocol with a band

`docs/target-properties.md` G2. Garbage collection is `LocalTruncate`
applied; the two corollaries below are the directions a deployment
uses. `Properties.LocalTruncate.of_banded` derives it from `Banded` and
`ViewSound`, so a protocol proves nothing new — what a mechanism owes
is the witness that its cut stands in the `Truncates` relation.
-/

namespace LeanDag

namespace Properties

namespace Arcs

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {R : DagRule Validator BlockId Payload}
variable {S S' : Slots Validator} {U U' : R.Universe} {G d : ℕ}
variable {V : R.View U} {V' : R.View U'}

/-- **A verdict survives the cut**, at the replica's own numbering. -/
theorem decided_of_truncate (h : LocalTruncate R) (ht : Truncates R U U' S S' G d)
    (hv : ViewAgreeAbove R V V' G) {k : ℕ} {v : Option BlockId}
    (hd : R.Decided S V (d + k) v) : R.Decided S' V' k v :=
  (h S S' U U' G d ht V V' hv k v).mp hd

/-- **And a verdict of the truncation is a verdict of the whole DAG**,
which is what lets a pruned replica be compared with one that never
pruned. -/
theorem decided_of_truncated (h : LocalTruncate R) (ht : Truncates R U U' S S' G d)
    (hv : ViewAgreeAbove R V V' G) {k : ℕ} {v : Option BlockId}
    (hd : R.Decided S' V' k v) : R.Decided S V (d + k) v :=
  (h S S' U U' G d ht V V' hv k v).mpr hd

/-! ## The agreement half

A deployment needs more than `decided_of_truncate`: a validator that
joined from the truncation holds an arbitrary view of it and must still
agree with a full-history one. `Agree` and `LocalTruncate` compose to
give this for any rule with both, with nothing proved per protocol. -/

/-- **Cross-cut agreement.** A validator holding any view of the
truncation agrees, slot for slot, with a full-history validator. -/
theorem decided_agree_truncate (ha : Agree R) (hlt : LocalTruncate R)
    (ht : Truncates R U U' S S' G d) (hv : ViewAgreeAbove R V V' G)
    {W : R.View U'} {k : ℕ} {w v : Option BlockId}
    (hW : R.Decided S' W k w) (hV : R.Decided S V (d + k) v) : w = v :=
  ha S' W V' k w v hW ((hlt S S' U U' G d ht V V' hv k v).mp hV)

/-- **And across two horizons.** Validators cut at different depths
agree on every shared slot, matched through the absolute slot index.
Horizons need never be negotiated. -/
theorem decided_agree_horizons (ha : Agree R) (hlt : LocalTruncate R)
    {U₁ U₂ : R.Universe} {S₁ S₂ : Slots Validator} {G₁ d₁ G₂ d₂ : ℕ}
    (ht₁ : Truncates R U U₁ S S₁ G₁ d₁) (ht₂ : Truncates R U U₂ S S₂ G₂ d₂)
    {V₁ : R.View U₁} {V₂ : R.View U₂}
    (hv₁ : ViewAgreeAbove R V V₁ G₁) (hv₂ : ViewAgreeAbove R V V₂ G₂)
    {W₁ : R.View U₁} {W₂ : R.View U₂} {k₁ k₂ : ℕ}
    (halign : d₁ + k₁ = d₂ + k₂) {w₁ w₂ v : Option BlockId}
    (hW₁ : R.Decided S₁ W₁ k₁ w₁) (hW₂ : R.Decided S₂ W₂ k₂ w₂)
    (hV : R.Decided S V (d₁ + k₁) v) : w₁ = w₂ :=
  (decided_agree_truncate ha hlt ht₁ hv₁ hW₁ hV).trans
    (decided_agree_truncate ha hlt ht₂ hv₂ hW₂ (halign ▸ hV)).symm

/-! ## The liveness half, for the core

On the liveness side the mechanism *owes* `Sustains`; the core's
carrier discharges it. -/

section Core

variable [Faults Validator] {U : BlockUniverse Validator BlockId Payload} {G : ℕ}

/-- **The core's carrier, read as block records**: both maps are the
identity. -/
def coreOnRecord :
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
  coreOnRecord.sustains_chop U

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
  coreOnRecord.truncates_chop U hd

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


/-! ## The rules on the core's record

Odontoceti and Mahi-Mahi run on the core's universes, so their carriers
read as records by the identity maps, and every mechanism cell is
`Arcs/Record.lean` at the instance. -/

section OdontocetiRecord

variable [Faults5 Validator] {B : Type} [LinearOrder B]

/-- **Odontoceti's carrier, read as block records**: the core's, at its
fault model. -/
def odontocetiOnRecord :
    (OdontocetiProperties.odontocetiRule (Validator := Validator) (BlockId := B)
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

end OdontocetiRecord

section MahiMahiRecord

variable [Faults Validator] {B : Type} [LinearOrder B]

/-- **Mahi-Mahi's carrier, read as block records**, at each wave width. -/
def mahiMahiOnRecord (w : ℕ) :
    (MahiMahiProperties.mahiMahiRule (Validator := Validator) (BlockId := B)
      (Payload := Payload) w).OnRecord ValidWrt (Correct : Finset Validator) BlockRecord.Any where
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

end MahiMahiRecord

end Arcs

end Properties

end LeanDag
