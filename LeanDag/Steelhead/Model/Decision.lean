import LeanDag.Steelhead.Model.Wavelength
import LeanDag.MahiMahi.Model.Decision
/-!
# Steelhead — the decision relation at a wavelength function

The Mahi-Mahi rule with the wave read at the slot's kind
(`steelhead.md` §2, `docs/kinds.md`): a slot of kind `κ` proposed at
round `r` is voted on at `r + w κ − 2`, decided at `r + w κ − 1`, and
anchored no lower than `r + w κ`. For the 3f+1 pair this is the whole of
Steelhead — the paper's "collapses to a wavelength function" — and the
anchored relation's `waveAt` field is what lets one rule carry it.

**One family of predicates, not two.** The pair instantiated here is
Mysticeti at `ws = 3` and Mahi-Mahi at `wa`, and at wavelength three
Mahi-Mahi's relation is the core's, slot for slot and verdict for
verdict (`Safety/Statement.lean`, SH4, an `↔`: MM1d one way and
`decided_of_core_decided` the other). The two rules of the paper are
therefore one predicate family read at two numbers, which is why every
law is Mahi-Mahi's at the wave of the slot it concerns and no law
compares two rules.

**Definitions only**, as in the Mahi-Mahi model files this one imports
read-only. The direct predicates, the certificate, and the indirect test
are Mahi-Mahi's at wave `w κ`; nothing is restated.

**Why the floor is the slot's own wave.** An asynchronous slot at round
`r` with `wa = 5` has its certificates at `r + 4`; a block at `r + 1`
references only round-`r` blocks and sees none of them. Anchoring at the
next synchronous slot would let one validator skip what another directly
committed. The relation's eligibility reads `waveAt (S.kind k)`, so the
floor of every slot is its own (`steelhead.md` §3, the counterexample is
`LeanDagTest/Steelhead/Model.lean`).
-/

namespace LeanDag

namespace Steelhead

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type} [LinearOrder BlockId] {Payload : Type}
variable {U : BlockUniverse Validator BlockId Payload}

/-- **Steelhead as an anchored rule** at the wavelength function `w`: at a
slot of kind `κ` proposed at round `r`, Mahi-Mahi's rule at wave `w κ` —
the certificate-quorum direct commit, the slot's blame as direct skip,
one rung of link, a certificate in the anchor's cone, no tie — with the
wave offset `w κ − 1`, so that an anchor sits at round `r + w κ` or
above. At a constant `w` this is `mahiMahiAnchored` by definition
(SH4). -/
def steelheadAnchored (Validator BlockId Payload : Type) [Fintype Validator]
    [DecidableEq Validator] [Faults Validator] [LinearOrder BlockId] (w : ℕ → ℕ) :
    AnchoredRule Validator BlockId Payload ValidWrt Correct where
  waveAt := fun κ => w κ - 1
  Commit := fun U V L r κ => MahiMahi.DirectCommitIn U V (w κ) L r
  decCommit := fun _ _ _ _ _ => inferInstance
  Skip := fun U V S k => MahiMahi.DirectSkipIn U V (w (S.kind k)) (S.leader k) (S.slotRound k)
  rungs := 1
  Link := fun _ U A L S k => MahiMahi.CertifiedIn U (w (S.kind k)) A L (S.slotRound k)
  tie := fun _ _ _ => False

section Slots

variable [S : Slots Validator]

/-- **The decision relation at the wavelength function `w`**: the
anchored relation at Steelhead's data. `Decided w U V k (some L)`: a
validator holding `V` may commit `L` at `k`; `Decided w U V k none`: it
may skip the slot; *undecided* is the absence of any derivation. At
`w = wavelength ws wa` under a schedule whose kinds are `periodicKind p`
this is Algorithm 1 of the paper. -/
abbrev Decided (w : ℕ → ℕ) (U : BlockUniverse Validator BlockId Payload)
    (V : View Validator BlockId Payload U) : ℕ → Option BlockId → Prop :=
  (steelheadAnchored Validator BlockId Payload w).Decided (S := S) U V

namespace Decided
export AnchoredRule.Decided (directCommit directSkip indirectCommit indirectSkip)
end Decided

/-- **A hop of the floor chain**: from slot `x`, the anchor search passes over every slot the view
skips and stops at the first slot at or above `x`'s floor, `x + w κ` at `x`'s kind `κ`, that it
does not, which is `y`. One slot per round, as Theorem 2 reads the chain. -/
def FloorHop (w : ℕ → ℕ) (U : BlockUniverse Validator BlockId Payload)
    (V : View Validator BlockId Payload U) (x y : ℕ) : Prop :=
  x + w (S.kind x) ≤ y ∧ (∀ j, x + w (S.kind x) ≤ j → j < y → Decided w U V j none) ∧
    ¬ Decided w U V y none

/-- **The landing of a hop**: the least slot at or above `k`'s floor that the view does not skip,
which is where the anchor search stops. The floor itself where the view skips every slot above
it, a case a finite universe never reaches above its top, since nothing up there is decided at
all; the claims that read the chain carry the landing's own `¬ Decided` and so never see it. -/
noncomputable def floorLanding (w : ℕ → ℕ) (U : BlockUniverse Validator BlockId Payload)
    (V : View Validator BlockId Payload U) (k : ℕ) : ℕ :=
  open Classical in
  if h : ∃ y, k + w (S.kind k) ≤ y ∧ ¬ Decided w U V y none then Nat.find h
  else k + w (S.kind k)

/-- **The floor chain from a slot**: hop to the landing, and again from there. A function of the
view, so that under a coin-shaped universe it is a function of the coin, which is what a bound on
the landings' leaders has to quantify over. -/
noncomputable def floorChain (w : ℕ → ℕ) (U : BlockUniverse Validator BlockId Payload)
    (V : View Validator BlockId Payload U) (k : ℕ) : ℕ → ℕ
  | 0 => k
  | i + 1 => floorLanding w U V (floorChain w U V k i)

instance {V : View Validator BlockId Payload U} (w : ℕ → ℕ) (L : BlockId) (r κ : ℕ) :
    Decidable ((steelheadAnchored Validator BlockId Payload w).Commit U V L r κ) :=
  inferInstanceAs (Decidable (MahiMahi.DirectCommitIn U V (w κ) L r))

instance {V : View Validator BlockId Payload U} (w : ℕ → ℕ) (k : ℕ) :
    Decidable ((steelheadAnchored Validator BlockId Payload w).Skip U V S k) :=
  inferInstanceAs
    (Decidable (MahiMahi.DirectSkipIn U V (w (S.kind k)) (S.leader k) (S.slotRound k)))

end Slots

end Steelhead

end LeanDag
