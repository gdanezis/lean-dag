import LeanDag.Reactive.Mysticeti
import LeanDag.Mysticeti.Properties
import LeanDag.Properties.Arcs.Quality
/-!
# Reactive Mysticeti conforms to the schedule family

`docs/target-properties.md` §4. The reactive discipline changes no
rule — `Decided` is the core's, so safety is inherited unchanged — only
the liveness precondition, a second `Live` at the same `LeaderCommits`.
`reactiveLive` is a `ReactiveM` execution's clauses over a slot window,
past GST with the timeout clearing `2Δ + proc`; unlike `coreLive` it
reads the schedule's leaders directly, through `cert_or_wait` and
`vote_or_wait`.
-/

namespace LeanDag

namespace MysticetiProperties

open Properties

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}

/-- **The reactive liveness precondition**, over a slot window: a
correct quorum `T`, a reactive execution under the schedule with its GST
at or below the window's first slot and its timeout clearing
`2Δ + proc` from there, the view caught up to the horizon, and every slot
of the window two rounds under it. -/
def reactiveLive (S : Slots Validator) {U : BlockUniverse Validator BlockId Payload}
    (V : View Validator BlockId Payload U) (T : Finset Validator) (lo K : ℕ) : Prop :=
  T ⊆ (Correct : Finset Validator) ∧ quorumCard Validator ≤ T.card ∧
    ∃ (N R₀ : ℕ) (rm : ReactiveM (S := S) U T N),
      rm.gst ≤ R₀ ∧ (∀ n, R₀ ≤ n → 2 * rm.delay + rm.proc ≤ rm.timeout n) ∧
      R₀ ≤ S.slotRound lo ∧ V.CoversUpto N ∧ ∀ k, k < K → S.slotRound k + 2 ≤ N

/-- **The reactive discipline is the other bridge to `certLive`**:
`cert_or_wait` certifies every candidate of a reliably-led slot past
GST, so the two execution models meet at one precondition — with no
`SynchronisedOn`, which a reactive builder cannot promise. -/
theorem certLive_of_reactiveLive {S : Slots Validator}
    {U : BlockUniverse Validator BlockId Payload} {V : View Validator BlockId Payload U}
    {T : Finset Validator} {lo K : ℕ} (h : reactiveLive S (U := U) V T lo K) :
    certLive S (U := U) V T lo K := by
  obtain ⟨hT, hcard, N, R₀, rm, hgst, hto, hR, hcov, hN⟩ := h
  refine ⟨hcard, N, hcov, hN, ?_⟩
  intro k hlo hK hlead
  have hRk : R₀ ≤ S.slotRound k := le_trans hR (S.mono hlo)
  have hNk : S.slotRound k + 2 ≤ N := hN k hK
  exact ⟨rm.toPaceCore.populatedOn hcard _ (by omega),
    rm.toPaceCore.populatedOn hcard _ (by omega),
    fun L hL => rm.certifies hT hcard hgst hto hRk hNk hlead hL⟩

/-- **The reactive discipline reaches the core's support precondition**
(`Properties/Support.lean`): a reactive execution past GST is a quorum
certifying every candidate of every reliably-led slot in the window,
which is `Support.live` and the socket every mechanism reads. -/
theorem coreSupport_live_of_reactiveLive {S : Slots Validator}
    {U : BlockUniverse Validator BlockId Payload} {V : View Validator BlockId Payload U}
    {T : Finset Validator} {lo K : ℕ} (h : reactiveLive S (U := U) V T lo K) :
    (coreSupport (Validator := Validator) (BlockId := BlockId) (Payload := Payload)).live
      (coreReliability Validator) S (U := U) V T lo K := by
  obtain ⟨hT, hcard, N, R₀, rm, hgst, hto, hR, hcov, hN⟩ := h
  refine ⟨⟨hT, hcard⟩, N, hcov, hN, ?_⟩
  intro k hlo hK hlead
  have hRk : R₀ ≤ S.slotRound k := le_trans hR (S.mono hlo)
  have hNk : S.slotRound k + 2 ≤ N := hN k hK
  refine ⟨fun n _ h2 => rm.toPaceCore.populatedOn hcard n
    (by change n ≤ S.slotRound k + 2 at h2; omega), ?_⟩
  rintro L ⟨hLmem, hLr, hLc⟩
  exact rm.certifies hT hcard hgst hto hRk hNk hlead ⟨hLmem, hLr, hLc⟩

/-- **Reactive Mysticeti commits its reliable leaders.** The statement is
unchanged; the proof is now the bridge composed with the core's single
`LeaderCommits`, where it was a second proof of the same shape. -/
theorem leaderCommits_reactive :
    LeaderCommits (mysticetiRule (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload)) (fun S {U} V T lo K => reactiveLive S (U := U) V T lo K) :=
  fun S _ V T lo K hlive => leaderCommits_cert S V T lo K (certLive_of_reactiveLive hlive)

end MysticetiProperties

namespace ReactiveM

/-! ## RS5 — reactive inclusion, from the generic theorem

The generic inclusion theorem (`Properties/Arcs/Quality.lean`), with
the reactive bridge supplying `certLive`. -/

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {S : Slots Validator} {T : Finset Validator}

/-- **RS5 — reactive inclusion.** The schedule fixes a `u`-led slot
above any round `m` before an execution is named, and a sufficiently
grown reactive execution commits it with a leader block whose cone
contains `u`'s round-`m` block, so it lands in the agreed ledger. -/
theorem committed_of_correct_block
    (hT : T ⊆ (Correct : Finset Validator))
    (hcard : quorumCard Validator ≤ T.card)
    (fair : FairToEach (S := S) T) {u : Validator} (hu : u ∈ T) (R m : ℕ)
    (hRm : R ≤ m) :
    ∃ k', m < S.slotRound k' ∧ R ≤ S.slotRound k' ∧ S.leader k' = u ∧
      ∀ (U : BlockUniverse Validator BlockId Payload) (N : ℕ)
        (rm : ReactiveM U T N),
        rm.gst ≤ R →
        (∀ n, R ≤ n → 2 * rm.delay + rm.proc ≤ rm.timeout n) →
        S.slotRound k' + 2 ≤ N →
        ∀ b ∈ U.ids, (U.block b).creator = u → (U.block b).round = m →
          ∃ L, IsLeaderBlock U k' L ∧ Decided U (View.full U) k' (some L) ∧
            Reaches U L b ∧
            ∀ (g : ℕ → Option BlockId) (n : ℕ), g k' = some L → k' < n →
              b ∈ ledgerSet U g n := by
  obtain ⟨k', hk', hlead⟩ := fair u hu (slotAt Validator (m + 1))
  have hm : m < S.slotRound k' := by
    have h1 := le_slotRound_slotAt (Validator := Validator) (m + 1)
    have h2 := S.mono hk'
    omega
  refine ⟨k', hm, by omega, hlead, ?_⟩
  intro U N rm hgst hto hN b hb hbc hbr
  have hlive : MysticetiProperties.reactiveLive S (U := U) (View.full U) T k' (k' + 1) :=
    ⟨hT, hcard, N, R, rm, hgst, hto, by omega, View.coversUpto_full U N,
      fun j hj => by have := S.mono (Nat.lt_succ_iff.mp hj); omega⟩
  obtain ⟨L, hdec, hL⟩ := Properties.Arcs.includes_of_leads
    (R := MysticetiProperties.mysticetiRule) MysticetiProperties.selfParent
    MysticetiProperties.noEquiv MysticetiProperties.commitsCandidate
    MysticetiProperties.leaderCommits_cert S hT (by rw [hlead]; exact hu) (le_of_lt hm)
    U (View.full U) (MysticetiProperties.certLive_of_reactiveLive hlive)
  obtain ⟨hmem, hledger⟩ := hL b hb (by change (U.block b).creator = S.leader k'; rw [hbc, hlead]) hbr
  have hcand := MysticetiProperties.commitsCandidate S U (View.full U) k' L hdec
  exact ⟨L, hcand, hdec, (mem_history_iff hcand.1).mp hmem, hledger⟩

/-- **No reliable validator's block is censored** (RS5, execution first). In
a reactive run past GST whose timeout clears `2Δ + proc`, every block a
reliable validator authors is reached by a later commit --- at a slot the
validator leads itself --- and so enters the agreed ledger. -/
theorem committed_of_correct_block_of_run {U : BlockUniverse Validator BlockId Payload} {N : ℕ}
    (hT : T ⊆ (Correct : Finset Validator))
    (hcard : quorumCard Validator ≤ T.card)
    (fair : FairToEach (S := S) T) (rm : ReactiveM U T N) {R m : ℕ}
    (hgst : rm.gst ≤ R) (hto : ∀ n, R ≤ n → 2 * rm.delay + rm.proc ≤ rm.timeout n)
    {u : Validator} (hu : u ∈ T) (hRm : R ≤ m) :
    ∃ k', m < S.slotRound k' ∧ S.leader k' = u ∧
      (S.slotRound k' + 2 ≤ N →
        ∀ b ∈ U.ids, (U.block b).creator = u → (U.block b).round = m →
          ∃ L, IsLeaderBlock U k' L ∧ Decided U (View.full U) k' (some L) ∧
            Reaches U L b ∧
            ∀ (g : ℕ → Option BlockId) (n : ℕ), g k' = some L → k' < n →
              b ∈ ledgerSet U g n) := by
  obtain ⟨k', hm, hR, hlead, hrest⟩ :=
    committed_of_correct_block (BlockId := BlockId) (Payload := Payload)
      hT hcard fair hu R m hRm
  exact ⟨k', hm, hlead, fun hN => hrest U N rm hgst hto hN⟩

end ReactiveM

end LeanDag
