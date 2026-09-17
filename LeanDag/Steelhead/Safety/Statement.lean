import LeanDag.Steelhead.Model.Chain
import LeanDag.MahiMahi.Model.Rules
/-!
# Safety at a wavelength function — statement

The rules at the wavelength function `w` never disagree about a slot,
whichever rule decided it and whichever anchor a view found
(`steelhead.md` §3). Eight claims:

* **SH1a, skip excludes certificates** — Lemma 1's skip half at the
  slot's own wave;
* **SH1b, certificate uniqueness** — Lemma 1's uniqueness half;
* **SH1c, quorum intersection across the wave** — Lemma 2: a direct
  commit at round `r` leaves a certificate in the causal history of every
  block at round `r + w r` or above;
* **SH2, agreement** — Theorem 1: two views deciding one slot reach the
  same verdict, by any routes, whether the slot's wave is `ws` or `wa`
  and whether the anchor's is;
* **SH3, handover** — Corollary 1: a direct commit in one view is
  committed by every view that finds an anchor for the slot, whichever
  rule decides the anchor, and no view skips it;
* **SH4, conservativity** — Theorem 5: at a constant wavelength the rule
  *is* Mahi-Mahi's, at period one it is Mahi-Mahi's at `wa`, and at wave
  three the derivations are exactly the core's;
* **SH5, chain agreement** — the chain verdicts agree across views: an
  instance of MM1c at the chain schedule, one slot per round led by the
  round's coin leader;
* **SH5b, the direct verdicts coincide**: at an asynchronous round the
  coin leads, the output's direct commit and direct skip are the chain's
  predicates, so "whenever either verdict of an asynchronous slot is
  direct, the two coincide" (the paper's protocol section).

Each claim states the weakest bound its proof consumes: `1 ≤ w r` for
the quorum intersection, `2 ≤ w r` for the rest, which is the bound the
paper's interface states. Mahi-Mahi states MM1a-c at `3 ≤ w`, the bound
below which the 3f+1 pair's vote-and-certify pattern has nowhere to put
a certificate. These are claims about the decision relation rather than
about that pattern, so they are stated at what they use.

Statements only; the proofs live in `Proof.lean`.
-/

namespace LeanDag

namespace Steelhead

namespace Safety

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
  [F : Faults Validator] {BlockId : Type} [LinearOrder BlockId] {Payload : Type}
  [S : Slots Validator]

/-- **SH1a, skip excludes certificates**, at the slot's own wave. -/
def SkipExcludesCertificates (U : BlockUniverse Validator BlockId Payload) (w : ℕ → ℕ) : Prop :=
  ∀ (a : Validator) (r : ℕ) (L : BlockId),
    2 ≤ w r → MahiMahi.DirectSkip U (w r) a r →
    L ∈ U.ids → (U.block L).creator = a → (U.block L).round = r →
    MahiMahi.certificates U (w r) L r = ∅

/-- **SH1b, certificate uniqueness**, at the slot's own wave. -/
def CertificateUniqueness (U : BlockUniverse Validator BlockId Payload) (w : ℕ → ℕ) : Prop :=
  ∀ (r : ℕ) (L₁ L₂ : BlockId),
    2 ≤ w r →
    (MahiMahi.certificates U (w r) L₁ r).Nonempty → (MahiMahi.certificates U (w r) L₂ r).Nonempty →
    (U.block L₁).creator = (U.block L₂).creator →
    (U.block L₁).round = (U.block L₂).round →
    L₁ = L₂

/-- **SH1c, quorum intersection across the wave**: a directly committed
candidate proposed at `r` is certified in the cone of every block at
round `r + w r` or above — whatever wave that block's own slot has. -/
def CertificateInHistory (U : BlockUniverse Validator BlockId Payload) (w : ℕ → ℕ) : Prop :=
  ∀ (L : BlockId) (r : ℕ),
    1 ≤ w r → MahiMahi.DirectCommit U (w r) L r →
    ∀ A ∈ U.ids, r + w r ≤ (U.block A).round → MahiMahi.CertifiedIn U (w r) A L r

/-- **SH2, agreement**: two views deciding one slot agree on the verdict,
whatever routes each took and whatever the waves of the slot and of the
anchors — the core's M6 at a wavelength function. -/
def Agreement (U : BlockUniverse Validator BlockId Payload) (w : ℕ → ℕ) : Prop :=
  ∀ (V₁ V₂ : View Validator BlockId Payload U) (k : ℕ) (v₁ v₂ : Option BlockId),
    (∀ r, 2 ≤ w r) → Decided w U V₁ k v₁ → Decided w U V₂ k v₂ → v₁ = v₂

/-- **SH3, handover**: a direct commit in one view is committed by every
view that finds the slot an anchor — the nearest eligible committed slot
with every eligible slot between skipped — whichever rule decides that
anchor; and no view skips the slot. -/
def Handover (U : BlockUniverse Validator BlockId Payload) (w : ℕ → ℕ) : Prop :=
  ∀ (V₁ V₂ : View Validator BlockId Payload U) (k : ℕ) (L : BlockId),
    (∀ r, 2 ≤ w r) →
    -- L is slot k's candidate, directly committed in V₁
    IsLeaderBlock U k L →
    (steelheadAnchored Validator BlockId Payload w).Commit U V₁ L (S.slotRound k) →
    -- then any anchor V₂ finds for k commits L ...
    (∀ (j : ℕ) (A : BlockId),
      k < j → (steelheadAnchored Validator BlockId Payload w).Eligible k j →
      Decided w U V₂ j (some A) →
      (∀ m, k < m → m < j → (steelheadAnchored Validator BlockId Payload w).Eligible k m →
        Decided w U V₂ m none) →
      Decided w U V₂ k (some L)) ∧
    -- ... and V₂ never skips k
    ¬ Decided w U V₂ k none

/-- **SH4, conservativity of the rule**: at a constant wavelength the
rule is Mahi-Mahi's at that wave, and the period-one function is the
constant `wa`. A statement about definitions, as MM1d is. -/
def RuleConservative : Prop :=
  (∀ w : ℕ, steelheadAnchored Validator BlockId Payload (fun _ => w) =
    MahiMahi.mahiMahiAnchored Validator BlockId Payload w) ∧
  (∀ ws wa : ℕ, periodic ws wa 1 = fun _ => wa)

/-- **SH4, conservativity of the relation at wave three**: at the
constant wavelength three the derivations are exactly the core's
(Mysticeti's), so `k = ∞` at `ws = 3` is Mysticeti, as the paper's
Theorem 5 says. Whether anything commits is a liveness question, as in
MM1d. -/
def DecidedConservative (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ (V : View Validator BlockId Payload U) (k : ℕ) (v : Option BlockId),
    Decided (fun _ => 3) U V k v ↔ LeanDag.Decided U V k v

/-- **SH5, chain agreement**: two views agree on the chain verdict of
every round, under any coin. -/
def ChainAgreement (U : BlockUniverse Validator BlockId Payload) (wa : ℕ) : Prop :=
  ∀ (coin : ℕ → Validator) (V₁ V₂ : View Validator BlockId Payload U) (r : ℕ)
    (v₁ v₂ : Option BlockId),
    2 ≤ wa → ChainDecided wa coin U V₁ r v₁ → ChainDecided wa coin U V₂ r v₂ → v₁ = v₂

/-- **SH5b, the direct verdicts coincide**: at an asynchronous round whose
slot is proposed there and led by the coin, the output's direct commit
and direct skip are the chain's, predicate for predicate, so a direct
derivation in either relation is one in the other. -/
def DirectAgreesWithChain (U : BlockUniverse Validator BlockId Payload) (ws wa : ℕ) : Prop :=
  ∀ (coin : ℕ → Validator) (V : View Validator BlockId Payload U) (k r : ℕ) (L : BlockId),
    -- slot r is proposed at round r, asynchronous, and the coin leads it
    S.slotRound r = r → IsAsync k r → S.leader r = coin r →
    -- the direct commit of L at r is the same predicate in both relations ...
    ((steelheadAnchored Validator BlockId Payload (periodic ws wa k)).Commit U V L r ↔
      (MahiMahi.mahiMahiAnchored Validator BlockId Payload wa).Commit U V L r) ∧
    -- ... and so is the direct skip of the slot
    ((steelheadAnchored Validator BlockId Payload (periodic ws wa k)).Skip U V S r ↔
      (MahiMahi.mahiMahiAnchored Validator BlockId Payload wa).Skip U V (chainSlots coin) r)

/-- Safety of the rule at a wavelength function, over every fault
configuration, schedule, block universe, wavelength function and
wavelength pair the model admits. -/
def Statement : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [LinearOrder BlockId] [Slots Validator]
    (U : BlockUniverse Validator BlockId Payload) (w : ℕ → ℕ) (ws wa : ℕ),
    SkipExcludesCertificates U w ∧ CertificateUniqueness U w ∧ CertificateInHistory U w ∧
      Agreement U w ∧ Handover U w ∧
      RuleConservative (Validator := Validator) (BlockId := BlockId) (Payload := Payload) ∧
      DecidedConservative U ∧ ChainAgreement U wa ∧ DirectAgreesWithChain U ws wa

end Safety

end Steelhead

end LeanDag
