import LeanDag.Steelhead.Model.Wavelength
import LeanDag.MahiMahi.Model.Decision
/-!
# Steelhead — the decision relation at a wavelength function

The Mahi-Mahi rule with the wave read at the slot's round
(`steelhead.md` §2): a slot proposed at round `r` is voted on at
`r + w r − 2`, decided at `r + w r − 1`, and anchored no lower than
`r + w r`. For the 3f+1 pair this is the whole of Steelhead — the paper's
"collapses to a wavelength function" — and the anchored relation's
`waveAt` field is what lets one rule carry it.

**Definitions only**, as in the Mahi-Mahi model files this one imports
read-only. The direct predicates, the certificate, and the indirect test
are Mahi-Mahi's at wave `w r`; nothing is restated.

**Why the floor is the slot's own wave.** An asynchronous slot at round
`r` with `wa = 5` has its certificates at `r + 4`; a block at `r + 1`
references only round-`r` blocks and sees none of them. Anchoring at the
next synchronous slot would let one validator skip what another directly
committed. The relation's eligibility reads `waveAt (S.slotRound k)`, so
the floor of every slot is its own (`steelhead.md` §3, the
counterexample is `LeanDagTest/Steelhead/Model.lean`).
-/

namespace LeanDag

namespace Steelhead

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type} [LinearOrder BlockId] {Payload : Type}
variable {U : BlockUniverse Validator BlockId Payload}

/-- **Steelhead as an anchored rule** at the wavelength function `w`: at a
slot proposed at round `r`, Mahi-Mahi's rule at wave `w r` — the
certificate-quorum direct commit, the slot's blame as direct skip, one
rung of link, a certificate in the anchor's cone, no tie — with the wave
offset `w r − 1`, so that an anchor sits at round `r + w r` or above. At a
constant `w` this is `mahiMahiAnchored` by definition (SH4). -/
def steelheadAnchored (Validator BlockId Payload : Type) [Fintype Validator]
    [DecidableEq Validator] [Faults Validator] [LinearOrder BlockId] (w : ℕ → ℕ) :
    AnchoredRule Validator BlockId Payload ValidWrt Correct where
  waveAt := fun r => w r - 1
  Commit := fun U V L r => MahiMahi.DirectCommitIn U V (w r) L r
  decCommit := fun _ _ _ _ => inferInstance
  Skip := fun U V S k => MahiMahi.DirectSkipIn U V (w (S.slotRound k)) (S.leader k) (S.slotRound k)
  rungs := 1
  Link := fun _ U A L S k => MahiMahi.CertifiedIn U (w (S.slotRound k)) A L (S.slotRound k)
  tie := fun _ _ _ => False

section Slots

variable [S : Slots Validator]

/-- **The decision relation at the wavelength function `w`**: the
anchored relation at Steelhead's data. `Decided w U V k (some L)`: a
validator holding `V` may commit `L` at `k`; `Decided w U V k none`: it
may skip the slot; *undecided* is the absence of any derivation. Under
`periodic ws wa k` this is Algorithm 1 of the paper. -/
abbrev Decided (w : ℕ → ℕ) (U : BlockUniverse Validator BlockId Payload)
    (V : View Validator BlockId Payload U) : ℕ → Option BlockId → Prop :=
  (steelheadAnchored Validator BlockId Payload w).Decided (S := S) U V

namespace Decided
export AnchoredRule.Decided (directCommit directSkip indirectCommit indirectSkip)
end Decided

instance {V : View Validator BlockId Payload U} (w : ℕ → ℕ) (L : BlockId) (r : ℕ) :
    Decidable ((steelheadAnchored Validator BlockId Payload w).Commit U V L r) :=
  inferInstanceAs (Decidable (MahiMahi.DirectCommitIn U V (w r) L r))

instance {V : View Validator BlockId Payload U} (w : ℕ → ℕ) (k : ℕ) :
    Decidable ((steelheadAnchored Validator BlockId Payload w).Skip U V S k) :=
  inferInstanceAs
    (Decidable (MahiMahi.DirectSkipIn U V (w (S.slotRound k)) (S.leader k) (S.slotRound k)))

end Slots

end Steelhead

end LeanDag
