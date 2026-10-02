import LeanDag.RedSnapper.Helpers.History
import LeanDag.RedSnapper.Model.Transaction
import LeanDag.RedSnapper.Model.Stance
import Mathlib.Data.Finset.Max

/-!
# Computable candidates and stances

Generated: `Finset` surrogates for the reachability-dependent predicates
of `Model/Transaction.lean` and `Model/Stance.lean` — the transactions
a block includes, its candidates for an object, the declaring and
latest-declaring blocks of a validator — each pinned against the audited
definition by an iff for universe members, so that witness models decide
the computable side and bridge. Also the two structural facts about
`StanceIs` promised in its docstring: it is total and functional.
Nothing here is part of the audit surface.
-/

namespace LeanDag

namespace RedSnapper

variable {Validator BlockId Tx Obj : Type*} [Fintype Validator] [DecidableEq Validator]
  [DecidableEq BlockId] [F : Faults Validator]

section Surrogates

variable (U : Universe Validator BlockId Tx Obj)

/-- The universe members in `b`'s computed history. -/
def historyIn (b : BlockId) : Finset BlockId :=
  (history U b).filter fun b' => b' ∈ U.ids

/-- The transactions carried somewhere in `b`'s history. -/
def txsIn [DecidableEq Tx] (b : BlockId) : Finset Tx :=
  (historyIn U b).biUnion fun b' => (U.block b').txs

/-- The paper's `Candidates(b, o)` as a `Finset`. -/
def candidates [DecidableEq Tx] [DecidableEq Obj] [T : Transactions Tx Obj] (b : BlockId)
    (o : Obj) : Finset Tx :=
  (txsIn U b).filter fun tx => T.Valid tx ∧ T.input tx = o

/-- The declaring blocks of `id` on `o` below `b`. -/
def declarers (id : Validator) (o : Obj) (b : BlockId) : Finset BlockId :=
  (historyIn U b).filter fun b' => (U.block b').author = id ∧ (U.block b').declares o ≠ none

/-- The latest declaring blocks of `id` on `o` below `b`. -/
def latestDeclarers (id : Validator) (o : Obj) (b : BlockId) : Finset BlockId :=
  (declarers U id o b).filter fun b' =>
    ∀ b'' ∈ declarers U id o b, (U.block b'').round ≤ (U.block b').round

/-- The computable form of `StanceDiscipline.no_return`. -/
def NoReturnDec : Prop :=
  ∀ b ∈ U.ids, (U.block b).author ∈ (Correct : Finset Validator) →
    ∀ p ∈ historyIn U b, (U.block p).author = (U.block b).author → p ≠ b →
    ∀ (o : Obj) (tx : Tx), (U.block b).declares o = some (Stance.ack tx) →
      (U.block p).declares o ≠ some Stance.bot

/-- The computable form of `StanceDiscipline.no_switch`. -/
def NoSwitchDec : Prop :=
  ∀ b ∈ U.ids, (U.block b).author ∈ (Correct : Finset Validator) →
    ∀ p ∈ historyIn U b, (U.block p).author = (U.block b).author → p ≠ b →
    ∀ (o : Obj) (tx tx' : Tx), (U.block b).declares o = some (Stance.ack tx) →
      (U.block p).declares o = some (Stance.ack tx') → tx' = tx

end Surrogates

/-- Whether an optional stance is an ACK. -/
def isAck {Tx : Type*} : Option (Stance Tx) → Bool
  | some (Stance.ack _) => true
  | _ => false

theorem isAck_iff {Tx : Type*} {s : Option (Stance Tx)} :
    isAck s = true ↔ ∃ tx, s = some (Stance.ack tx) := by
  cases s with
  | none => simp [isAck]
  | some v =>
      cases v with
      | ack tx => simp [isAck]
      | bot => simp [isAck]

variable {U : Universe Validator BlockId Tx Obj}

theorem mem_historyIn_iff {b b' : BlockId} (hb : b ∈ U.ids) :
    b' ∈ historyIn U b ↔ b' ∈ U.ids ∧ Reaches U b b' := by
  rw [historyIn, Finset.mem_filter, mem_history_iff hb, and_comm]

theorem mem_txsIn_iff [DecidableEq Tx] {b : BlockId} {tx : Tx} (hb : b ∈ U.ids) :
    tx ∈ txsIn U b ↔ Includes U b tx := by
  unfold txsIn Includes
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨b', hb', htx⟩
    obtain ⟨hid, hr⟩ := (mem_historyIn_iff hb).mp hb'
    exact ⟨b', hid, htx, hr⟩
  · rintro ⟨b', hid, htx, hr⟩
    exact ⟨b', (mem_historyIn_iff hb).mpr ⟨hid, hr⟩, htx⟩

theorem mem_candidates_iff [DecidableEq Tx] [DecidableEq Obj] [T : Transactions Tx Obj]
    {b : BlockId} {o : Obj} {tx : Tx} (hb : b ∈ U.ids) :
    tx ∈ candidates U b o ↔ IsCandidate U b o tx := by
  unfold candidates IsCandidate
  rw [Finset.mem_filter, mem_txsIn_iff hb]
  exact ⟨fun ⟨h1, h2, h3⟩ => ⟨h2, h3, h1⟩, fun ⟨h1, h2, h3⟩ => ⟨h3, h1, h2⟩⟩

theorem conflicted_iff [DecidableEq Tx] [DecidableEq Obj] [T : Transactions Tx Obj]
    {b : BlockId} {o : Obj} (hb : b ∈ U.ids) :
    Conflicted U b o ↔ 1 < (candidates U b o).card := by
  rw [Finset.one_lt_card]
  constructor
  · rintro ⟨tx, tx', h1, h2, hne⟩
    exact ⟨tx, (mem_candidates_iff hb).mpr h1, tx', (mem_candidates_iff hb).mpr h2, hne⟩
  · rintro ⟨tx, h1, tx', h2, hne⟩
    exact ⟨tx, tx', (mem_candidates_iff hb).mp h1, (mem_candidates_iff hb).mp h2, hne⟩

theorem mem_declarers_iff {id : Validator} {o : Obj} {b b' : BlockId} (hb : b ∈ U.ids) :
    b' ∈ declarers U id o b ↔ Declaring U id o b b' := by
  unfold declarers Declaring
  rw [Finset.mem_filter, mem_historyIn_iff hb]
  tauto

theorem mem_latestDeclarers_iff {id : Validator} {o : Obj} {b b' : BlockId} (hb : b ∈ U.ids) :
    b' ∈ latestDeclarers U id o b ↔ Latest U id o b b' := by
  unfold latestDeclarers Latest
  rw [Finset.mem_filter, mem_declarers_iff hb]
  simp only [mem_declarers_iff hb]

theorem stanceIs_some_iff {id : Validator} {o : Obj} {b : BlockId} {s : Stance Tx}
    (hb : b ∈ U.ids) :
    StanceIs U id o b (some s) ↔
      ∃ b' ∈ latestDeclarers U id o b, (U.block b').declares o = some s ∧
        ∀ b'' ∈ latestDeclarers U id o b, b'' = b' := by
  unfold StanceIs
  simp only [mem_latestDeclarers_iff hb]

theorem stanceIs_none_iff {id : Validator} {o : Obj} {b : BlockId} (hb : b ∈ U.ids) :
    StanceIs U id o b none ↔
      declarers U id o b = ∅ ∨
        ∃ b₁ ∈ latestDeclarers U id o b, ∃ b₂ ∈ latestDeclarers U id o b, b₁ ≠ b₂ := by
  unfold StanceIs
  rw [Finset.eq_empty_iff_forall_notMem]
  constructor
  · rintro (h | ⟨b₁, b₂, h₁, h₂, hne⟩)
    · exact Or.inl fun b' hb' => h ⟨b', (mem_declarers_iff hb).mp hb'⟩
    · exact Or.inr ⟨b₁, (mem_latestDeclarers_iff hb).mpr h₁,
        b₂, (mem_latestDeclarers_iff hb).mpr h₂, hne⟩
  · rintro (h | ⟨b₁, h₁, b₂, h₂, hne⟩)
    · exact Or.inl fun ⟨b', hb'⟩ => h b' ((mem_declarers_iff hb).mpr hb')
    · exact Or.inr ⟨b₁, b₂, (mem_latestDeclarers_iff hb).mp h₁,
        (mem_latestDeclarers_iff hb).mp h₂, hne⟩

theorem ackedBefore_iff {id : Validator} {o : Obj} {b : BlockId} (hb : b ∈ U.ids) :
    AckedBefore U id o b ↔
      ∃ b' ∈ historyIn U b, (U.block b').author = id ∧
        ∃ b'' ∈ latestDeclarers U id o b', isAck ((U.block b'').declares o) = true ∧
          ∀ b''' ∈ latestDeclarers U id o b', b''' = b'' := by
  unfold AckedBefore
  constructor
  · rintro ⟨b', tx, hid, ha, hr, hs⟩
    obtain ⟨b'', hl, hd, hu⟩ := (stanceIs_some_iff hid).mp hs
    exact ⟨b', (mem_historyIn_iff hb).mpr ⟨hid, hr⟩, ha, b'', hl, isAck_iff.mpr ⟨tx, hd⟩, hu⟩
  · rintro ⟨b', hb', ha, b'', hl, hack, hu⟩
    obtain ⟨hid, hr⟩ := (mem_historyIn_iff hb).mp hb'
    obtain ⟨tx, hd⟩ := isAck_iff.mp hack
    exact ⟨b', tx, hid, ha, hr, (stanceIs_some_iff hid).mpr ⟨b'', hl, hd, hu⟩⟩

theorem stanceDiscipline_iff : StanceDiscipline U ↔ NoReturnDec U ∧ NoSwitchDec U := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro b hb hc p hp ha hne o tx hd
      obtain ⟨hpid, hr⟩ := (mem_historyIn_iff hb).mp hp
      exact h.no_return b hb hc p hpid ha hr hne o tx hd
    · intro b hb hc p hp ha hne o tx tx' hd hd'
      obtain ⟨hpid, hr⟩ := (mem_historyIn_iff hb).mp hp
      exact h.no_switch b hb hc p hpid ha hr hne o tx tx' hd hd'
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · intro b hb hc p hpid ha hr hne o tx hd
      exact h1 b hb hc p ((mem_historyIn_iff hb).mpr ⟨hpid, hr⟩) ha hne o tx hd
    · intro b hb hc p hpid ha hr hne o tx tx' hd hd'
      exact h2 b hb hc p ((mem_historyIn_iff hb).mpr ⟨hpid, hr⟩) ha hne o tx tx' hd hd'

omit [DecidableEq BlockId] in
/-- `StanceIs` is functional: a validator has one stance on an object at
a block. -/
theorem stanceIs_unique {id : Validator} {o : Obj} {b : BlockId} {s s' : Option (Stance Tx)}
    (h : StanceIs U id o b s) (h' : StanceIs U id o b s') : s = s' := by
  cases s with
  | some v =>
      obtain ⟨b₁, hL₁, hd₁, hu₁⟩ := h
      cases s' with
      | some v' =>
          obtain ⟨b₂, hL₂, hd₂, hu₂⟩ := h'
          have := hu₁ b₂ hL₂
          subst this
          rw [hd₁] at hd₂
          exact hd₂
      | none =>
          rcases h' with hno | ⟨c₁, c₂, hc₁, hc₂, hne⟩
          · exact absurd ⟨b₁, hL₁.1⟩ hno
          · exact absurd ((hu₁ c₁ hc₁).trans (hu₁ c₂ hc₂).symm) hne
  | none =>
      cases s' with
      | some v' =>
          obtain ⟨b₂, hL₂, hd₂, hu₂⟩ := h'
          rcases h with hno | ⟨c₁, c₂, hc₁, hc₂, hne⟩
          · exact absurd ⟨b₂, hL₂.1⟩ hno
          · exact absurd ((hu₂ c₁ hc₁).trans (hu₂ c₂ hc₂).symm) hne
      | none => rfl

omit [DecidableEq BlockId] in
/-- `StanceIs` is total: a validator has a stance on every object at
every block of the universe. -/
theorem stanceIs_exists {id : Validator} {o : Obj} {b : BlockId} (hb : b ∈ U.ids) :
    ∃ s, StanceIs U id o b s := by
  classical
  by_cases h : ∃ b', Declaring U id o b b'
  · obtain ⟨b', hb'⟩ := h
    have hne : (declarers U id o b).Nonempty := ⟨b', (mem_declarers_iff hb).mpr hb'⟩
    obtain ⟨m, hm, hmax⟩ :=
      Finset.exists_max_image (declarers U id o b) (fun b' => (U.block b').round) hne
    have hL : Latest U id o b m :=
      ⟨(mem_declarers_iff hb).mp hm, fun b'' hb'' => hmax b'' ((mem_declarers_iff hb).mpr hb'')⟩
    by_cases huniq : ∀ b'', Latest U id o b b'' → b'' = m
    · cases hs : (U.block m).declares o with
      | none => exact absurd hs hL.1.2.2.2
      | some s => exact ⟨some s, m, hL, hs, huniq⟩
    · push Not at huniq
      obtain ⟨b₂, hb₂, hne⟩ := huniq
      exact ⟨none, Or.inr ⟨m, b₂, hL, hb₂, fun h => hne h.symm⟩⟩
  · exact ⟨none, Or.inl h⟩

end RedSnapper

end LeanDag
