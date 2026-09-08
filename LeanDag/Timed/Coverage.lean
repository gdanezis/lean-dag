import LeanDag.Properties.Sustain
import LeanDag.Properties.Support
import LeanDag.Properties.Arcs.Liveness
/-!
# The timed model: coverage, and the bridge into certification

`docs/target-properties.md` §11.16. Synchrony is not a property: it is
the antecedent a timed execution reaches `Support.live` from, where a
reactive one reaches it from its wait clauses instead. `SynchronisedOn`,
`CoversToward`, `OfCoverage` and the theorems consuming them live here,
in `LeanDag.Timed`, and nowhere under `Properties/`
(`scripts/check-arc-holes.py` enforces this).
-/

namespace LeanDag

namespace Timed

open Properties

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {R : DagRule Validator BlockId Payload}

/-! ## Coverage, at the carrier -/

/-- **Full coverage from a round**: every `T`-block one round up holds
every `T`-block below it as a reference. `LeanDag.SynchronisedFrom`, read
at the carrier. -/
def SynchronisedOn (R : DagRule Validator BlockId Payload) (U : R.Universe)
    (T : Finset Validator) (r : ℕ) : Prop :=
  SynchronisedFrom (R.block U) (R.ids U) T r

/-- Synchrony from a round is synchrony from any later one. -/
theorem SynchronisedOn.mono {U : R.Universe} {T : Finset Validator} {r r' : ℕ}
    (h : SynchronisedOn R U T r) (hr : r ≤ r') : SynchronisedOn R U T r' :=
  fun n hn => h n (le_trans hr hn)

/-- **Synchrony survives a rebase**, for the reason votes and production
do: it is read from rounds, authors and references, and above the
settling round the mechanism changed none of them. -/
theorem synchronisedOn_of_rebased {U U' : R.Universe} {G R₀ : ℕ}
    (h : RebasedAbove R U U' G R₀) {T : Finset Validator} {r : ℕ}
    (hr : R₀ ≤ r) (hG : G ≤ r) (hs : SynchronisedOn R U T r) :
    SynchronisedOn R U' T (r - G) := by
  intro n hn b hb hbr hbc a ha har hac
  obtain ⟨hbU, hbround⟩ := h.of_mem' hb (by omega)
  obtain ⟨haU, haround⟩ := h.of_mem' ha (by omega)
  have hbc' : (R.block U b).creator ∈ T := by rwa [← h.creator b hbU (by omega)]
  have hac' : (R.block U a).creator ∈ T := by rwa [← h.creator a haU (by omega)]
  rw [h.refs b hbU (by omega)]
  exact hs (n + G) (by omega) b hbU (by omega) hbc' a haU (by omega) hac'

/-- **Coverage toward a candidate** over a window: every `T`-block at
each level of the window references every `T`-block one level below it
that reaches the candidate. Full coverage restricted to the candidate's
support. -/
def CoversToward (R : DagRule Validator BlockId Payload) (U : R.Universe)
    (T : Finset Validator) (r wave : ℕ) (L : BlockId) : Prop :=
  ∀ n, r ≤ n → n < r + wave →
    ∀ b, b ∈ R.ids U → (R.block U b).creator ∈ T → (R.block U b).round = n + 1 →
    ∀ a, a ∈ R.ids U → (R.block U a).creator ∈ T → (R.block U a).round = n →
      ReachesFrom (R.block U) a L → a ∈ (R.block U b).refs

/-- Full coverage from `Rnd` is coverage toward anything, over any window
at or above `Rnd`. -/
theorem coversToward_of_synchronisedOn {U : R.Universe} {T : Finset Validator}
    {Rnd r wave : ℕ} {L : BlockId} (hs : SynchronisedOn R U T Rnd) (hr : Rnd ≤ r) :
    CoversToward R U T r wave L :=
  fun n hn _ b hb hbc hbr a ha hac har _ => hs n (by omega) b hb hbr hbc a ha har hac

/-! ## Coverage certifies

The timed model's one obligation: on a window the reliable set has
populated, with coverage toward a reliable candidate at its base, every
reliable block at the top certifies it. A rule with no synchronous story
does not owe it. -/

/-- **Coverage certifies**, for a support. -/
def OfCoverage (sp : Support R) (rel : Reliability Validator) : Prop :=
  ∀ (U : R.Universe) (T : Finset Validator), rel.IsQuorum T →
    ∀ (r : ℕ) (L : BlockId),
    (∀ n, r ≤ n → n ≤ r + sp.wave → Properties.PopulatedOn R U T n) →
    CoversToward R U T r sp.wave L →
    L ∈ R.ids U → (R.block U L).round = r → (R.block U L).creator ∈ T →
    ∀ c, c ∈ R.ids U → (R.block U c).creator ∈ T → (R.block U c).round = r + sp.wave →
      sp.Certifies U c L

/-- **For vote support**, coverage toward the candidate at its own round
is the vote. -/
theorem voteSupport_ofCoverage (rel : Reliability Validator) :
    OfCoverage (voteSupport R) rel := by
  intro U T _ r L _ hct hL hLr hLc c hc hcc hcr
  change (R.block U c).round = r + 1 at hcr
  exact hct r le_rfl (by change r < r + 1; omega) c hc hcc hcr L hL hLc hLr
    Relation.ReflTransGen.refl

/-! ## The bridge -/

/-- **A covered, populated window is a live one.** The only theorem that
turns synchrony into certification; everything after it is generic. -/
theorem live_of_coverage (sp : Support R) {rel : Reliability Validator}
    (hcov : OfCoverage sp rel) {U : R.Universe} {T : Finset Validator}
    (hq : rel.IsQuorum T) {Rnd N : ℕ} (hs : SynchronisedOn R U T Rnd)
    (hpop : ∀ r, Rnd ≤ r → r ≤ N → Properties.PopulatedOn R U T r)
    (S : Slots Validator) (V : R.View U) {lo K : ℕ} (hV : CoversUpto R V N)
    (hRnd : Rnd ≤ S.slotRound lo) (hN : ∀ k, k < K → S.slotRound k + sp.wave ≤ N) :
    sp.live rel S V T lo K := by
  refine ⟨hq, N, hV, hN, ?_⟩
  intro k hlo hK hlead
  have hRk : Rnd ≤ S.slotRound k := le_trans hRnd (S.mono hlo)
  have hkN := hN k hK
  refine ⟨fun n h1 h2 => hpop n (by omega) (by omega), ?_⟩
  intro L hL v hv c hc hcc hcr
  exact hcov U T hq _ L (fun n h1 h2 => hpop n (by omega) (by omega))
    (coversToward_of_synchronisedOn hs hRk) hL.1 hL.2.1 (by rw [hL.2.2]; exact hlead)
    c hc (by rw [hcc]; exact hv) hcr

/-- **A reliably-led slot commits on a covered, populated DAG.** The
bridge, then Law 3. -/
theorem exists_decided_of_coverage (sp : Support R) {rel : Reliability Validator}
    (hcov : OfCoverage sp rel) (hlc : sp.Commits rel)
    {U : R.Universe} {T : Finset Validator} (hq : rel.IsQuorum T) {Rnd N : ℕ}
    (hs : SynchronisedOn R U T Rnd)
    (hpop : ∀ r, Rnd ≤ r → r ≤ N → Properties.PopulatedOn R U T r)
    (S : Slots Validator) (V : R.View U) (k : ℕ) (hV : CoversUpto R V N)
    (hRnd : Rnd ≤ S.slotRound k) (hN : S.slotRound k + sp.wave ≤ N)
    (hlead : S.leader k ∈ T) :
    ∃ L, DecidedBelow R S (k + 1) V k (some L) :=
  sp.leaderCommits hlc S V T k (k + 1)
    (live_of_coverage sp hcov hq hs hpop S V hV hRnd (fun j hj => by
      have := S.mono (Nat.lt_succ_iff.mp hj); omega))
    k le_rfl (Nat.lt_succ_self k) hlead

/-- **Everything below a fair run is decided, on a covered DAG.** The
timed reading of `Support.decidedBelow_of_fairRun`: the run is placed
past the synchrony round as well as past `k`, and the bridge supplies
the window. -/
theorem decidedBelow_of_fairRun (sp : Support R) {rel : Reliability Validator}
    (hcov : OfCoverage sp rel) (hlc : sp.Commits rel)
    {S : Slots Validator} {c : ℕ} (hd : Descends R S c)
    {T : Finset Validator} (hq : rel.IsQuorum T)
    (fair : FairRunOn T c) (Rnd k : ℕ) :
    ∃ b, k ≤ b ∧ Rnd ≤ S.slotRound b ∧
      ∀ {U : R.Universe} (V : R.View U) (N : ℕ),
        SynchronisedOn R U T Rnd → (∀ r, Rnd ≤ r → r ≤ N → Properties.PopulatedOn R U T r) →
        CoversUpto R V N → S.slotRound (b + c - 1) + sp.wave ≤ N →
        ∀ i, i < b → ∃ v, DecidedBelow R S (b + c) V i v := by
  obtain ⟨k₀, hk₀⟩ := S.unbounded Rnd
  obtain ⟨b, hb, h⟩ := sp.decidedBelow_of_fairRun hlc hd fair (max k k₀)
  have hRb : Rnd ≤ S.slotRound b :=
    le_trans hk₀ (S.mono (le_trans (le_max_right k k₀) hb))
  refine ⟨b, le_trans (le_max_left _ _) hb, hRb, ?_⟩
  intro U V N hs hpop hV hN i hi
  refine h V (live_of_coverage sp hcov hq hs hpop S V hV hRb ?_) i hi
  intro j hj
  exact le_trans (Nat.add_le_add_right (S.mono (by omega)) _) hN

/-! ## A good DAG -/

/-- **A good DAG, from `Rnd` to `N`**: some quorum of the fault model is
synchronised from `Rnd` and populates every round from `Rnd` to `N`.
Everything a timed model asks of the DAG, packaged: a live rule's notion
of a good DAG is this at its own carrier and fault model. -/
def Good (R : DagRule Validator BlockId Payload) (rel : Reliability Validator)
    (U : R.Universe) (Rnd N : ℕ) : Prop :=
  ∃ T, rel.IsQuorum T ∧ SynchronisedOn R U T Rnd ∧
    ∀ r, Rnd ≤ r → r ≤ N → Properties.PopulatedOn R U T r

end Timed

end LeanDag
