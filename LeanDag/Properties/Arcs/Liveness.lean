import LeanDag.Properties.Support
import LeanDag.Properties.Derived.LeaderCommits
import LeanDag.Properties.Derived.Progress
import LeanDag.Properties.Truncate
/-!
# Liveness, from a support: on a covered DAG, and across a mechanism

`docs/target-properties.md` §11.7. Three theorems, each proved once for
any rule with a `Support` and its laws, none of them per rule and none
per mechanism.

* `decidedBelow_of_fairRun` — every slot below a fair run is decided,
  on any execution meeting `live` on the run. Law 2 and `Descends`;
  no precondition of the rule's own, and no synchrony: the timed
  reading is `Timed.decidedBelow_of_fairRun`.
* `certifiesAt_of_rebased` — certification survives every
  `RebasedAbove`, from Law 1.
* `exists_decided_of_sustains` — a commit survives any `Sustains` at the
  same schedule: the candidates are the same blocks, certification and
  production carry over, and Law 3 fires in the transformed universe.
  The liveness half of what `Arcs/GC.lean` and `Arcs/SafeSkip.lean`
  give for safety.
-/

namespace LeanDag

namespace Properties

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}

/-- **Coverage survives the cut**, on a view that agrees with the original
above the horizon: a block of the truncation under the rebased bound is an
old block under the original one. -/
theorem coversUpto_of_truncates {R : DagRule Validator BlockId Payload} {U U' : R.Universe}
    {S S' : Slots Validator} {G d N : ℕ} (h : Truncates R U U' S S' G d)
    {V : R.View U} {V' : R.View U'} (hv : ViewAgreeAbove R V V' G) (hGN : G ≤ N)
    (hc : CoversUpto R V N) : CoversUpto R V' (N - G) := by
  intro b hb hr
  have hm := (h.mem_iff b).mp hb
  have hround := h.round_of hb
  exact (hv b hm.1 hm.2).mp (hc b hm.1 (by omega))

namespace Support

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {R : DagRule Validator BlockId Payload}
variable (sp : Support R)

/-- **Everything below a fair run is decided**, for any rule with a
support and `Descends`. The run is named by the schedule alone, past
`k`; any execution meeting `live` on the run's window decides every slot
below it. What is asked of the DAG is certification of the run's
candidates and production across its waves — nothing about how the
certifiers came to reference what they reference. The timed reading,
with synchrony and production to a horizon in place of `live`, is
`Timed.decidedBelow_of_fairRun`. -/
theorem decidedBelow_of_fairRun {rel : Reliability Validator} (hlc : sp.Commits rel)
    {S : Slots Validator} {c : ℕ} (hd : Descends R S c)
    {T : Finset Validator}
    (fair : FairRunOn T c) (k : ℕ) :
    ∃ b, k ≤ b ∧ ∀ {U : R.Universe} (V : R.View U), sp.live rel S V T b (b + c) →
      ∀ i, i < b → ∃ v, DecidedBelow R S (b + c) V i v := by
  obtain ⟨b, hb, hrunT⟩ := fair k
  exact ⟨b, hb, fun V hlive => decidedBelow_of_run (sp.leaderCommits hlc) hd V T b hlive hrunT⟩

/-- **Certification survives every mechanism, from Law 1.** -/
theorem certifiesAt_of_rebased (hloc : sp.Local) {U U' : R.Universe} {G R₀ : ℕ}
    (h : RebasedAbove R U U' G R₀) {T : Finset Validator} {r : ℕ} {L : BlockId}
    (hr : R₀ ≤ r) (hG : G ≤ r) (hw : sp.waveAt (r - G) = sp.waveAt r) (hL : L ∈ R.ids U)
    (hLr : (R.block U L).round = r) (hc : sp.certifiesAt U T r L) :
    sp.certifiesAt U' T (r - G) L := by
  intro v hv c hc' hcc hcr
  rw [hw] at hcr
  obtain ⟨hcU, hround⟩ := h.of_mem' hc' (by omega)
  have hcrU : (R.block U c).round = r + sp.waveAt r := by omega
  have hccU : (R.block U c).creator = v := by
    rw [← h.creator c hcU (by omega)]; exact hcc
  exact (hloc h c L hcU (by rw [hLr]; omega) hL (by rw [hLr]; omega)).mpr
    (hc v hv c hcU hccU hcrU)

/-- **A commit survives a sustaining mechanism**, at the same schedule. -/
theorem exists_decided_of_sustains {rel : Reliability Validator}
    (hloc : sp.Local) (hlc : sp.Commits rel)
    {U U' : R.Universe} {R₀ : ℕ} (h : Sustains R U U' 0 R₀)
    (S : Slots Validator) (V' : R.View U') {T : Finset Validator} (k : ℕ) (hq : rel.IsQuorum T)
    (hR₀ : R₀ ≤ S.slotRound k)
    (hpop : ∀ n, S.slotRound k ≤ n → n ≤ S.slotRound k + sp.waveAt (S.slotRound k) →
      PopulatedOn R U T n)
    (hcert : ∀ L, R.IsCandidate S U k L → sp.certifiesAt U T (S.slotRound k) L)
    (hV' : CoversUpto R V' (S.slotRound k + sp.waveAt (S.slotRound k))) (hlead : S.leader k ∈ T) :
    ∃ L, DecidedBelow R S (k + 1) V' k (some L) := by
  refine hlc S V' T k hq ?_ ?_ hV' hlead
  · intro n h1 h2
    have := h.populatedOn_of (T := T) (r := n) (by omega) (Nat.zero_le _) (hpop n h1 h2)
    rwa [Nat.sub_zero] at this
  · rintro L ⟨hL', hLr', hLc'⟩
    obtain ⟨hLU, hround⟩ := h.of_mem' hL' (by omega)
    have hLr : (R.block U L).round = S.slotRound k := by omega
    have hLc : (R.block U L).creator = S.leader k := by
      rw [← h.creator L hLU (by omega)]; exact hLc'
    have := sp.certifiesAt_of_rebased hloc h (T := T) (r := S.slotRound k) hR₀ (Nat.zero_le _)
      (by rw [Nat.sub_zero]) hLU hLr (hcert L ⟨hLU, hLr, hLc⟩)
    rwa [Nat.sub_zero] at this


/-! ## The precondition itself survives a mechanism

What every consumer downstream reads — `LeaderCommits`,
`decidedBelow_of_run`, chain quality, Barnacle — is `Support.live`, the
whole window, and the two theorems below carry that across a `Sustains`
or `Truncates` witness, with the rule contributing nothing but its
support. The view is a hypothesis in both: what the transformed view
covers is the mechanism's business, not the rule's. -/

/-- **`live` survives a sustaining mechanism**, at the same schedule:
production and certification carry across, and the candidates are the
same blocks. -/
theorem live_of_sustains {rel : Reliability Validator} (hloc : sp.Local)
    {U U' : R.Universe} {R₀ : ℕ} (h : Sustains R U U' 0 R₀)
    {S : Slots Validator} {V : R.View U} {V' : R.View U'} {T : Finset Validator} {lo K : ℕ}
    (hlive : sp.live rel S V T lo K) (hR₀ : R₀ ≤ S.slotRound lo)
    (hV' : ∀ N, CoversUpto R V N → CoversUpto R V' N) :
    sp.live rel S V' T lo K := by
  obtain ⟨hq, N, hcov, hN, hslot⟩ := hlive
  refine ⟨hq, N, hV' N hcov, hN, ?_⟩
  intro k hlo hK hlead
  obtain ⟨hpop, hcert⟩ := hslot k hlo hK hlead
  have hRk : R₀ ≤ S.slotRound k := le_trans hR₀ (S.mono hlo)
  refine ⟨?_, ?_⟩
  · intro n h1 h2
    have := h.populatedOn_of (T := T) (r := n) (by omega) (Nat.zero_le _) (hpop n h1 h2)
    rwa [Nat.sub_zero] at this
  · rintro L ⟨hL', hLr', hLc'⟩
    obtain ⟨hLU, hround⟩ := h.of_mem' hL' (by omega)
    have hLr : (R.block U L).round = S.slotRound k := by omega
    have hLc : (R.block U L).creator = S.leader k := by
      rw [← h.creator L hLU (by omega)]; exact hLc'
    have := sp.certifiesAt_of_rebased hloc h (T := T) (r := S.slotRound k) hRk (Nat.zero_le _)
      (by rw [Nat.sub_zero]) hLU hLr (hcert L ⟨hLU, hLr, hLc⟩)
    rwa [Nat.sub_zero] at this

/-- **`live` survives the cut**, at the re-indexed schedule: slot `k`
of the truncation is slot `d + k` of the original, a round `G` lower,
and the window moves with it. -/
theorem live_of_truncates {rel : Reliability Validator} (hloc : sp.Local)
    {U U' : R.Universe} {S S' : Slots Validator} {G d : ℕ}
    (h : Truncates R U U' S S' G d) {V : R.View U} {V' : R.View U'}
    {T : Finset Validator} {lo K : ℕ}
    (hlive : sp.live rel S V T lo K) (hlo : d ≤ lo) (hK : lo < K)
    (hV' : ∀ N, G ≤ N → CoversUpto R V N → CoversUpto R V' (N - G))
    (hw : ∀ r, G ≤ r → sp.waveAt (r - G) = sp.waveAt r) :
    sp.live rel S' V' T (lo - d) (K - d) := by
  obtain ⟨hq, N, hcov, hN, hslot⟩ := hlive
  have hGN : G ≤ N := by
    have := hN lo hK
    have := h.base
    have := S.mono hlo
    omega
  refine ⟨hq, N - G, hV' N hGN hcov, ?_, ?_⟩
  · intro k' hk'
    have hs := h.slotRound k'
    have := hN (d + k') (by omega)
    have hGk : G ≤ S.slotRound (d + k') := le_trans h.base (S.mono (Nat.le_add_right d k'))
    have hsr : S'.slotRound k' = S.slotRound (d + k') - G := by omega
    rw [hsr, hw _ hGk]
    omega
  · intro k' hlo' hK' hlead'
    have hs := h.slotRound k'
    have hl := h.leader k'
    have hlead : S.leader (d + k') ∈ T := by rw [← hl]; exact hlead'
    obtain ⟨hpop, hcert⟩ := hslot (d + k') (by omega) (by omega) hlead
    have hGk : G ≤ S.slotRound (d + k') := le_trans h.base (S.mono (Nat.le_add_right d k'))
    have hsr : S'.slotRound k' = S.slotRound (d + k') - G := by omega
    refine ⟨?_, ?_⟩
    · intro n' h1 h2
      rw [hsr, hw _ hGk] at h2
      have := h.toRebasedAbove.populatedOn_of (T := T) (r := n' + G) (by omega) (by omega)
        (hpop (n' + G) (by omega) (by omega))
      rwa [Nat.add_sub_cancel] at this
    · rintro L ⟨hL', hLr', hLc'⟩
      obtain ⟨hLU, hround⟩ := h.toRebasedAbove.of_mem' hL' (Nat.le_add_left _ _)
      have hLr : (R.block U L).round = S.slotRound (d + k') := by omega
      have hLc : (R.block U L).creator = S.leader (d + k') := by
        rw [← h.creator L hLU (by omega), hLc']; exact hl
      have := sp.certifiesAt_of_rebased hloc h.toRebasedAbove (T := T)
        (r := S.slotRound (d + k')) hGk hGk (hw _ hGk) hLU hLr (hcert L ⟨hLU, hLr, hLc⟩)
      have e : S.slotRound (d + k') - G = S'.slotRound k' := by omega
      rwa [e] at this

/-- **Anchored liveness after a sustaining mechanism.** A run of `c`
reliably-led slots above `b` in the transformed universe decides every
slot below `b` there — `decidedBelow_of_run` fed by the carried
precondition. -/
theorem decidedBelow_of_run_sustains {rel : Reliability Validator}
    (hloc : sp.Local) (hlc : sp.Commits rel) {S : Slots Validator} {c : ℕ}
    (hd : Descends R S c) {U U' : R.Universe} {R₀ : ℕ} (h : Sustains R U U' 0 R₀)
    {V : R.View U} (V' : R.View U') {T : Finset Validator} {b : ℕ}
    (hlive : sp.live rel S V T b (b + c)) (hR₀ : R₀ ≤ S.slotRound b)
    (hV' : ∀ N, CoversUpto R V N → CoversUpto R V' N)
    (hlead : ∀ i, i < c → S.leader (b + i) ∈ T) :
    ∀ i, i < b → ∃ v, DecidedBelow R S (b + c) V' i v :=
  decidedBelow_of_run (sp.leaderCommits hlc) hd V' T b
    (sp.live_of_sustains hloc h hlive hR₀ hV') hlead

/-- **Anchored liveness after the cut**, at the re-indexed schedule. -/
theorem decidedBelow_of_run_truncates {rel : Reliability Validator}
    (hloc : sp.Local) (hlc : sp.Commits rel) {S S' : Slots Validator} {c : ℕ}
    (hc : 0 < c) (hd : Descends R S' c) {U U' : R.Universe} {G d : ℕ}
    (h : Truncates R U U' S S' G d) {V : R.View U} (V' : R.View U')
    {T : Finset Validator} {b : ℕ}
    (hlive : sp.live rel S V T (d + b) (d + b + c))
    (hV' : ∀ N, G ≤ N → CoversUpto R V N → CoversUpto R V' (N - G))
    (hw : ∀ r, G ≤ r → sp.waveAt (r - G) = sp.waveAt r)
    (hlead : ∀ i, i < c → S'.leader (b + i) ∈ T) :
    ∀ i, i < b → ∃ v, DecidedBelow R S' (b + c) V' i v := by
  have hl := sp.live_of_truncates hloc h hlive (Nat.le_add_right d b) (by omega) hV' hw
  have e1 : d + b - d = b := by omega
  have e2 : d + b + c - d = b + c := by omega
  rw [e1, e2] at hl
  exact decidedBelow_of_run (sp.leaderCommits hlc) hd V' T b hl hlead

end Support

end Properties

end LeanDag
