import LeanDag.Properties.Arcs.Stack
import LeanDag.Properties.Arcs.Quality
import LeanDag.Properties.Derived.FromBand
/-!
# The headline theorems: safety and liveness, from the properties

`docs/target-properties.md` §11.18. Two statements a protocol gets by
showing the properties and nothing else.

**Safety** (`Safe`, from `Banded`, `Agree`, `CommitsCandidate`) holds
across a `Stack` — any composition of cuts, fills and re-genesis:
verdicts transport to the composite's numbering, agree across views,
name a real candidate, and never commit one block at two slots; a fifth
clause carries agreement across a plain `Extends` at every slot, which
is what a fill's gap needs. `Safe.prefix_agree` is the ledger reading.

**Liveness** (`Lives`, from a support's `Commits`, `CommitsCandidate`,
`SelfParent` and `NoEquiv`) has one antecedent, `Support.live`, reached
from coverage or from a reactive execution's wait clauses alike (no
synchrony, §11.16): every slot below a fair run is decided, a
reliably-led slot commits past every point, and every reliable block
enters the ledger through a slot its author leads. `Progresses` is the
first two, for models with no self-parent clause.
-/

namespace LeanDag

namespace Properties

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {R : DagRule Validator BlockId Payload}

/-! ## Safety -/

/-- **A block is the candidate of one slot.** Two slots with the same
candidate share its round and author, and `Slots.keyed` says slots
differ in one of them. -/
theorem DagRule.IsCandidate.slot_unique {S : Slots Validator} {U : R.Universe} {k k' : ℕ}
    {L : BlockId} (h : R.IsCandidate S U k L) (h' : R.IsCandidate S U k' L) : k = k' :=
  S.keyed (a₁ := k) (a₂ := k')
    (Prod.ext (h.2.1.symm.trans h'.2.1) (h.2.2.symm.trans h'.2.2))

/-- **Safety, across any stack of mechanisms**, and at every slot across
an extension. -/
def Safe (R : DagRule Validator BlockId Payload) : Prop :=
  (∀ {U U' : R.Universe} {S S' : Slots Validator} {G R₀ d : ℕ}, Stack R U S U' S' G R₀ d →
    ∀ {V : R.View U} {V' : R.View U'}, ViewAgreeAbove R V V' R₀ →
      (∀ (k : ℕ) (v : Option BlockId), R₀ ≤ S.slotRound (d + k) →
          (R.Decided S V (d + k) v ↔ R.Decided S' V' k v)) ∧
      (∀ (W : R.View U') (k : ℕ) (w v : Option BlockId), R₀ ≤ S.slotRound (d + k) →
          R.Decided S' W k w → R.Decided S V (d + k) v → w = v) ∧
      (∀ (W : R.View U') (k : ℕ) (L : BlockId), R.Decided S' W k (some L) →
          R.IsCandidate S' U' k L) ∧
      (∀ (W : R.View U') (k k' : ℕ) (L : BlockId), R.Decided S' W k (some L) →
          R.Decided S' W k' (some L) → k = k')) ∧
  (∀ {U U' : R.Universe}, Extends R U U' → ∀ (S : Slots Validator)
    {V : R.View U} {V' W : R.View U'}, R.viewIds V ⊆ R.viewIds V' →
      ∀ (k : ℕ) (v w : Option BlockId), R.Decided S V k v → R.Decided S W k w → v = w)

/-- **The safety headline**, assembled from `Banded`, `Agree` and
`CommitsCandidate`. -/
theorem safety (hb : Banded R) (ha : Agree R) (hcc : CommitsCandidate R) : Safe R := by
  refine ⟨?_, ?_⟩
  · intro U U' S S' G R₀ d st V V' hv
    exact ⟨fun k v hk => decided_of_rebased hb st.rebased hv k hk v,
      fun _ k _ _ hk hW hV => decided_agree_rebased ha hb st.rebased hv hk hW hV,
      fun W k L h => hcc _ _ W k L h,
      fun W k k' L h h' => (hcc _ _ W k L h).slot_unique (hcc _ _ W k' L h')⟩
  · intro U U' he S V V' W hsub k v w hV hW
    exact ha S V' W k v w (Persist.of_banded hb S _ _ he V V' hsub k v hV) hW

/-- **The ledger reading.** Two validators' verdict functions agree on
every slot both have decided above the settling round — the common
prefix of their ledgers is one prefix. -/
theorem Safe.prefix_agree (hs : Safe R) {U U' : R.Universe} {S S' : Slots Validator}
    {G R₀ d : ℕ} (st : Stack R U S U' S' G R₀ d) {V : R.View U} {V' : R.View U'}
    (hv : ViewAgreeAbove R V V' R₀) {W : R.View U'} {g g' : ℕ → Option BlockId} {n : ℕ}
    (hn : ∀ k, k < n → R₀ ≤ S.slotRound (d + k))
    (hg : ∀ k, k < n → R.Decided S V (d + k) (g k))
    (hg' : ∀ k, k < n → R.Decided S' W k (g' k)) :
    ∀ k, k < n → g' k = g k :=
  fun k hk => (hs.1 st hv).2.1 W k (g' k) (g k) (hn k hk) (hg' k hk) (hg k hk)

/-! ## Liveness -/

namespace Support

variable (sp : Support R) (rel : Reliability Validator)

/-- **Progress**: the ledger does not stall, and commits recur. Both
clauses name the slot by the schedule first and ask of the execution
only `live` on that window. -/
def Progresses : Prop :=
  ∀ (S : Slots Validator) (c : ℕ), 0 < c → Descends R S c → ∀ (T : Finset Validator),
    (∀ k, ∃ k', k ≤ k' ∧ ∀ i, i < c → S.leader (k' + i) ∈ T) →
    (∀ k, ∃ b, k ≤ b ∧ ∀ (U : R.Universe) (V : R.View U), sp.live rel S V T b (b + c) →
        ∀ i, i < b → ∃ v, DecidedBelow R S (b + c) V i v) ∧
    (∀ k, ∃ k', k ≤ k' ∧ S.leader k' ∈ T ∧
        ∀ (U : R.Universe) (V : R.View U), sp.live rel S V T k' (k' + 1) →
          ∃ L, DecidedBelow R S (k' + 1) V k' (some L))

/-- **Inclusion**: every block by a reliable author enters the ledger
through a slot its author leads, under a schedule fair to each. -/
def Includes : Prop :=
  ∀ (S : Slots Validator) (T : Finset Validator), T ⊆ rel.correct →
    (∀ v ∈ T, ∀ n, ∃ k, n ≤ k ∧ S.leader k = v) →
    ∀ (m : ℕ), ∀ v ∈ T, ∃ k', m ≤ S.slotRound k' ∧ S.leader k' = v ∧
      ∀ (U : R.Universe) (V : R.View U), sp.live rel S V T k' (k' + 1) →
        ∃ L, R.Decided S V k' (some L) ∧
          ∀ b ∈ R.ids U, (R.block U b).creator = v → (R.block U b).round = m →
            b ∈ historyFrom (R.block U) L ∧
              ∀ (g : ℕ → Option BlockId) (n : ℕ), g k' = some L → k' < n →
                b ∈ Arcs.ledgerSetOf R U g n

/-- **Liveness**: progress and inclusion. -/
def Lives : Prop := sp.Progresses rel ∧ sp.Includes rel

variable {sp rel}

/-- **Progress, from Law 2.** -/
theorem progress (hlc : sp.Commits rel) : sp.Progresses rel := by
  intro S c hc hd T fair
  refine ⟨fun k => ?_, fun k => ?_⟩
  · obtain ⟨b, hb, h⟩ := sp.decidedBelow_of_fairRun hlc hd fair k
    exact ⟨b, hb, fun _ V hlive => h V hlive⟩
  · obtain ⟨k', hk', hrun⟩ := fair k
    have hlead : S.leader k' ∈ T := by simpa using hrun 0 hc
    exact ⟨k', hk', hlead, fun _ V hlive =>
      sp.leaderCommits hlc S V T k' (k' + 1) hlive k' le_rfl (Nat.lt_succ_self k') hlead⟩

/-- **Inclusion, from Law 2 and self-reference.** -/
theorem inclusion (hlc : sp.Commits rel) (hcc : CommitsCandidate R) (hsp : SelfParent R)
    (hne : NoEquiv R rel) : sp.Includes rel :=
  fun S T hT fair m v hv =>
    Arcs.committed_of_correct_block hsp hne hcc (sp.leaderCommits hlc) S hT fair m hv

/-- **The liveness headline.** -/
theorem liveness (hlc : sp.Commits rel) (hcc : CommitsCandidate R) (hsp : SelfParent R)
    (hne : NoEquiv R rel) : sp.Lives rel :=
  ⟨progress hlc, inclusion hlc hcc hsp hne⟩

end Support

end Properties

end LeanDag
