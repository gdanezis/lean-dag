import LeanDag.Steelhead.Model.Chain
import LeanDag.MahiMahi.Model.Unpredictable
/-!
# Liveness at a wavelength function — statement

What the rule decides under synchrony, what the chain decides under the
unpredictable-leader clause, and what the output does *not* decide under
the paper's asynchronous adversary (`steelhead.md` §4–6). Six claims:

* **SH6a, a reliable leader commits under coverage** — Theorem 2's
  per-slot half: on a DAG a reliable quorum has synchronised and
  populated through the slot's decision round, a reliably led slot
  commits in every view caught up to that round, at whichever wave the
  slot's round carries;
* **SH6b, everything below a fair run is decided** — the core's L10 at
  the wavelength function: past any slot the schedule offers a run of
  reliably led slots, and once the DAG is covered through the run's
  decision rounds every slot below the run is decided;
* **SH7a, chain liveness** — MM3c at the chain schedule: a run of `wa`
  consecutive chain commits, which the clause promises in every window,
  decides every chain verdict below it;
* **SH7b, the chain under synchrony** — L10 at the chain schedule: past
  any round the coin names reliable leaders at `wa` consecutive rounds,
  and once the DAG is covered through that run's decision rounds every
  chain verdict below it is settled, with no clause;
* **SH8, the stall** — at a period `k ≥ ws` and one slot per round, if
  no synchronous candidate is ever certified and no synchronous slot is
  directly skipped, then no slot at a round `≡ k − 1 (mod k)` is ever
  decided, in any view, whatever the asynchronous slots do. The paper's
  own adversary — the leader block delivered to exactly `f + 1`
  validators before the vote — produces these hypotheses at every
  synchronous slot, so the output stalls at every period `k ≥ ws`.
  This is the paper's "Why the chain, and not the output" as
  a theorem, for every period rather than the one it walks through
  (`steelhead.md` §4; the DAG is `LeanDagTest/Steelhead/Stall.lean`);
* **SH9, the drain** — Theorem 3 (ii): at any wavelength function
  bounded by `wa` and one slot per round, `wa` consecutive committed
  slots decide every slot below them, whatever wave those slots carry.
  Once the period is `1` and Mahi-Mahi's run clause supplies the run,
  the slots an earlier period left undecided are finished by it.

SH6 assumes `3 ≤ w r` everywhere, as the safety claims do; SH7a assumes
`1 ≤ wa`, as MM3c does, and SH7b `4 ≤ wa`, as MM5 does; SH8 assumes
`2 ≤ ws ≤ k` and nothing of `wa`; SH9 assumes `1 ≤ w r ≤ wa`.

Statements only; the proofs live in `Proof.lean`.
-/

namespace LeanDag

namespace Steelhead

namespace Liveness

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
  [F : Faults Validator] {BlockId : Type} [LinearOrder BlockId] {Payload : Type}
  [S : Slots Validator]

/-- **SH6a, a reliable leader commits under coverage.** -/
def CommitsOfSynchrony (U : BlockUniverse Validator BlockId Payload) (w : ℕ → ℕ) : Prop :=
  ∀ (T : Finset Validator) (V : View Validator BlockId Payload U) (R N k : ℕ),
    (∀ r, 3 ≤ w r) →
    -- T is a reliable set: correct, and a quorum
    T ⊆ (Correct : Finset Validator) → quorumCard Validator ≤ T.card →
    -- T is synchronised from R and populates every round from R to the horizon N
    SynchronisedOn U T R → (∀ r, R ≤ r → r ≤ N → PopulatedOn U T r) →
    -- the slot lies at or past R, and every slot up to it decides at or below N
    R ≤ S.slotRound k →
    (∀ j, j ≤ k → (steelheadAnchored Validator BlockId Payload w).decisionRound j ≤ N) →
    -- the view holds every block up to N
    V.CoversUpto N →
    -- and the slot's leader is reliable
    S.leader k ∈ T →
    -- then the slot commits its candidate in that view
    ∃ L, IsLeaderBlock U k L ∧ Decided w U V k (some L)

/-- **SH6b, everything below a fair run is decided.** The run is named by
the schedule alone, before any DAG is mentioned, so the horizon cannot
cap how far fairness reaches. -/
def AllDecidedBelowOfSynchrony (w : ℕ → ℕ) : Prop :=
  ∀ (T : Finset Validator) (c : ℕ),
    (∀ r, 3 ≤ w r) →
    T ⊆ (Correct : Finset Validator) → quorumCard Validator ≤ T.card →
    -- a run of c slots spans eligibility, each slot at the wave of its own round
    (steelheadAnchored Validator BlockId Payload w).SpansEligible c →
    -- past any slot the schedule offers c consecutive T-led slots
    FairRunOn T c →
    -- then past any slot k and any round R there is a slot b ...
    ∀ (R k : ℕ), ∃ b, k ≤ b ∧ R ≤ S.slotRound b ∧
      -- ... below which every slot is decided, on any DAG T has synchronised
      -- from R and populated through the run's decision rounds, in any view
      -- covering them
      ∀ (U : BlockUniverse Validator BlockId Payload) (V : View Validator BlockId Payload U)
        (N : ℕ),
        SynchronisedOn U T R → (∀ r, R ≤ r → r ≤ N → PopulatedOn U T r) →
        V.CoversUpto N →
        (∀ j, j < b + c → (steelheadAnchored Validator BlockId Payload w).decisionRound j ≤ N) →
        ∀ i, i < b → ∃ v, Decided w U V i v

/-- **SH7a, chain liveness.** -/
def ChainAllDecidedBelow (U : BlockUniverse Validator BlockId Payload) (wa : ℕ) : Prop :=
  ∀ (coin : ℕ → Validator) (V : View Validator BlockId Payload U) (c N : ℕ),
    1 ≤ wa →
    -- the run form of the clause at the chain schedule: in every window of c
    -- rounds below the horizon, wa consecutive rounds whose coin leaders are
    -- committed candidates
    MahiMahi.UnpredictableRunWithin (S := chainSlots coin) U wa c wa N →
    -- the view holds every block up to the horizon
    V.CoversUpto N →
    -- then past every round r whose window decides below the horizon ...
    ∀ r, MahiMahi.decisionRoundAt wa (r + c + wa - 1) ≤ N →
      -- ... there is a round b at or past r below which every chain verdict is settled
      ∃ b, r ≤ b ∧ ∀ i, i < b → ∃ v, ChainDecided wa coin U V i v

/-- **SH7b, the chain under synchrony.** The run is named by the coin
alone, so the horizon cannot cap how far it reaches. -/
def ChainAllDecidedBelowOfSynchrony (wa : ℕ) : Prop :=
  ∀ (coin : ℕ → Validator) (T : Finset Validator),
    4 ≤ wa →
    T ⊆ (Correct : Finset Validator) → quorumCard Validator ≤ T.card →
    -- past any round the coin names T-leaders at wa consecutive rounds
    FairRunOn (S := chainSlots coin) T wa →
    -- then past any round k and any round R there is a round b ...
    ∀ (R k : ℕ), ∃ b, k ≤ b ∧ R ≤ b ∧
      -- ... below which every chain verdict is settled, on any DAG T has
      -- synchronised from R and populated through the run's decision round
      ∀ (U : BlockUniverse Validator BlockId Payload) (V : View Validator BlockId Payload U)
        (N : ℕ),
        SynchronisedOn U T R → (∀ r, R ≤ r → r ≤ N → PopulatedOn U T r) →
        V.CoversUpto N → MahiMahi.decisionRoundAt wa (b + wa - 1) ≤ N →
        ∀ i, i < b → ∃ v, ChainDecided wa coin U V i v

/-- **SH8, the stall.** -/
def Stall (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ (V : View Validator BlockId Payload U) (ws wa k : ℕ),
    -- a synchronous wave of at least two rounds, no longer than the period
    2 ≤ ws → ws ≤ k →
    -- one slot per round
    (∀ s, S.slotRound s = s) →
    -- no synchronous candidate is ever certified ...
    (∀ (j : ℕ) (L : BlockId), ¬ IsAsync k j → IsLeaderBlock U j L →
      MahiMahi.certificates U ws L j = ∅) →
    -- ... and no synchronous slot is directly skipped in V
    (∀ j, ¬ IsAsync k j → ¬ MahiMahi.DirectSkipIn U V ws (S.leader j) j) →
    -- then no slot at a round ≡ k − 1 (mod k) is ever decided in V
    ∀ i, i % k = k - 1 → ∀ v, ¬ Decided (periodic ws wa k) U V i v

/-- **SH9, the drain.** -/
def AllDecidedBelowOfRun (U : BlockUniverse Validator BlockId Payload) (w : ℕ → ℕ) (wa : ℕ) :
    Prop :=
  ∀ (V : View Validator BlockId Payload U) (b : ℕ),
    -- every wave lies between one round and wa
    (∀ r, 1 ≤ w r) → (∀ r, w r ≤ wa) →
    -- one slot per round
    (∀ s, S.slotRound s = s) →
    -- wa consecutive slots from b are committed in V
    (∀ i, i < wa → ∃ L, Decided w U V (b + i) (some L)) →
    -- then every slot below b is decided in V
    ∀ i, i < b → ∃ v, Decided w U V i v

/-- Liveness at a wavelength function, over every fault configuration,
schedule, block universe, wavelength function and asynchronous wave the
model admits. -/
def Statement : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [LinearOrder BlockId] [Slots Validator]
    (U : BlockUniverse Validator BlockId Payload) (w : ℕ → ℕ) (wa : ℕ),
    CommitsOfSynchrony U w ∧
      AllDecidedBelowOfSynchrony (Validator := Validator) (BlockId := BlockId)
        (Payload := Payload) w ∧
      ChainAllDecidedBelow U wa ∧
      ChainAllDecidedBelowOfSynchrony (Validator := Validator) (BlockId := BlockId)
        (Payload := Payload) wa ∧
      Stall U ∧ AllDecidedBelowOfRun U w wa

end Liveness

end Steelhead

end LeanDag
