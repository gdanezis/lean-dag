import LeanDag.Integration.CompRun
import LeanDag.Barnacle.Helpers.Ledger
/-!
# The ledger of a composed run

`Barnacle/Ledger` reads a run's committed blocks off its per-configuration
slot numbering, where the first slot of round `r` is `count k * r`. A
composed run has one numbering throughout, and the first slot of round
`r` is `F.cum r`; `ledgerOf` is the same function of a verdict function
and an interval, so only the interval moves.

`RangeClosed` is what the ledger asks of a configuration: its range lies
in the epochs the run has decided. Barnacle owes no such clause because
its runs decide their whole range by construction; a composed run decides
an epoch at a time, and its last configuration may reach past the last
epoch it has closed.

**Trusted core: `rangeLedger` and `ledgerUpto` are definitions.**
-/

namespace LeanDag
namespace Integration

open Barnacle Properties

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {R : Properties.DagRule Validator BlockId Payload} {P : Params}
variable {W : ℕ} {upd : ℕ → ℕ → (U : R.Universe) → R.View U → BlockId → ℕ × ℕ}
variable {pick : (U : R.Universe) → R.View U → (ℕ → Option BlockId) → ℕ → Validator}
variable {U : R.Universe} {V : R.View U} {K H : ℕ}

namespace Composed

/-- The ledger of configuration `k`: the blocks its range commits, in
slot order. The range is the slots of the rounds after `start k` through
`start (k + 1)`. -/
def rangeLedger (Rn : Composed (R := R) W P pick upd U V K H) (k : ℕ) : List BlockId :=
  ledgerOf Rn.vdct (Rn.F.cum (Rn.start k + 1)) (Rn.F.cum (Rn.start (k + 1) + 1))

/-- The ledger through configuration `K' − 1`: the ranges' ledgers,
concatenated in configuration order. -/
def ledgerUpto (Rn : Composed (R := R) W P pick upd U V K H) (K' : ℕ) : List BlockId :=
  (List.range K').flatMap Rn.rangeLedger

/-- **A configuration's range lies in the epochs the run has closed.**
Every slot of the range is one the run has decided, which is what reading
a verdict off it needs. -/
def RangeClosed (Rn : Composed (R := R) W P pick upd U V K H) (k : ℕ) : Prop :=
  Rn.F.cum (Rn.start (k + 1) + 1) ≤ W * H

/-- A slot of range `k` lies in the range's rounds. -/
theorem round_of_mem_interval (Rn : Composed (R := R) W P pick upd U V K H) {k g : ℕ}
    (h1 : Rn.F.cum (Rn.start k + 1) ≤ g) (h2 : g < Rn.F.cum (Rn.start (k + 1) + 1)) :
    Rn.start k < Rn.F.roundOf g ∧ Rn.F.roundOf g ≤ Rn.start (k + 1) := by
  have hlo := Rn.F.cum_le_iff_le_roundOf.mp h1
  have hhi := Frame.roundOf_lt_of_lt_cum h2
  omega

/-- Every slot of a closed range is decided. -/
theorem decided_of_mem_interval (hW : 0 < W)
    (Rn : Composed (R := R) W P pick upd U V K H) {k g : ℕ} (hcl : Rn.RangeClosed k)
    (h2 : g < Rn.F.cum (Rn.start (k + 1) + 1)) :
    R.Decided (Rn.F.toSlots Rn.asg Rn.keyed) V g (Rn.vdct g) :=
  Rn.decided_at g ((epochOf_lt_iff hW).mpr (by unfold RangeClosed at hcl; omega))

/-- **A block of range `k`'s ledger has a round in the range.** -/
theorem round_of_mem_rangeLedger (hcc : Properties.CommitsCandidate R) (hW : 0 < W)
    (Rn : Composed (R := R) W P pick upd U V K H) {k : ℕ} (hcl : Rn.RangeClosed k)
    {L : BlockId} (h : L ∈ Rn.rangeLedger k) :
    Rn.start k < (R.block U L).round ∧ (R.block U L).round ≤ Rn.start (k + 1) := by
  obtain ⟨g, h1, h2, hv⟩ := mem_ledgerOf.mp h
  obtain ⟨hlo, hhi⟩ := round_of_mem_interval Rn h1 h2
  have hd := decided_of_mem_interval hW Rn hcl h2
  rw [hv] at hd
  have hc := hcc _ _ _ g L hd
  rw [hc.2.1]
  exact ⟨hlo, hhi⟩

/-- **Within a range a block is committed by one slot**: two committing
slots share the block's round and author, and `Slots.keyed` identifies
them. -/
theorem slot_unique_of_rangeLedger (hcc : Properties.CommitsCandidate R) (hW : 0 < W)
    (Rn : Composed (R := R) W P pick upd U V K H) {k : ℕ} (hcl : Rn.RangeClosed k)
    {g₁ g₂ : ℕ} {L : BlockId}
    (h₁' : g₁ < Rn.F.cum (Rn.start (k + 1) + 1))
    (h₂' : g₂ < Rn.F.cum (Rn.start (k + 1) + 1))
    (hv₁ : Rn.vdct g₁ = some L) (hv₂ : Rn.vdct g₂ = some L) : g₁ = g₂ := by
  have d₁ := decided_of_mem_interval hW Rn hcl h₁'
  have d₂ := decided_of_mem_interval hW Rn hcl h₂'
  rw [hv₁] at d₁
  rw [hv₂] at d₂
  have c₁ := hcc _ _ _ g₁ L d₁
  have c₂ := hcc _ _ _ g₂ L d₂
  apply (Rn.F.toSlots Rn.asg Rn.keyed).keyed
  simp only [Prod.mk.injEq]
  exact ⟨c₁.2.1.symm.trans c₂.2.1, c₁.2.2.symm.trans c₂.2.2⟩

/-- **BN5c for a range**: a closed range's ledger has no repetition. -/
theorem rangeLedger_nodup (hcc : Properties.CommitsCandidate R) (hW : 0 < W)
    (Rn : Composed (R := R) W P pick upd U V K H) {k : ℕ} (hcl : Rn.RangeClosed k) :
    (Rn.rangeLedger k).Nodup := by
  unfold rangeLedger
  set lo := Rn.F.cum (Rn.start k + 1)
  set hi := Rn.F.cum (Rn.start (k + 1) + 1)
  have hres : ledgerOf Rn.vdct lo hi =
      ledgerOf (fun g => if lo ≤ g ∧ g < hi then Rn.vdct g else none) lo hi :=
    ledgerOf_congr (fun g h1 h2 => by rw [if_pos ⟨h1, h2⟩])
  rw [hres]
  unfold ledgerOf
  refine List.Nodup.filterMap ?_ (List.nodup_range' 1)
  intro a a' b ha ha'
  simp only [Option.mem_def] at ha ha'
  split_ifs at ha ha' with h h'
  · exact slot_unique_of_rangeLedger hcc hW Rn hcl h.2 h'.2 ha ha'
  all_goals exact absurd ‹_› (by simp_all)

/-- **Two closed ranges' ledgers are disjoint**: their blocks have rounds
in disjoint intervals. -/
theorem rangeLedger_disjoint (hcc : Properties.CommitsCandidate R) (hW : 0 < W)
    (Rn : Composed (R := R) W P pick upd U V K H) {k k' : ℕ} (h : k < k') (hK : k' < K)
    (hcl : Rn.RangeClosed k) (hcl' : Rn.RangeClosed k') :
    (Rn.rangeLedger k).Disjoint (Rn.rangeLedger k') := by
  intro L hL hL'
  obtain ⟨-, hhi⟩ := round_of_mem_rangeLedger hcc hW Rn hcl hL
  obtain ⟨hlo', -⟩ := round_of_mem_rangeLedger hcc hW Rn hcl' hL'
  have := Rn.toCompRun.start_mono (show k + 1 ≤ k' by omega) (by omega)
  omega

/-- **BN5b, the ledger grows**: to a lower height it is a prefix of
itself to a higher one. Nothing is asked of the run: the ranges only
append. -/
theorem ledgerUpto_prefix (Rn : Composed (R := R) W P pick upd U V K H) {K₁ K₂ : ℕ}
    (h : K₁ ≤ K₂) : Rn.ledgerUpto K₁ <+: Rn.ledgerUpto K₂ := by
  unfold ledgerUpto
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [List.range_add, List.flatMap_append]
  exact List.prefix_append _ _

/-- **BN5c, integrity**: no block appears twice in the ledger. -/
theorem ledgerUpto_nodup (hcc : Properties.CommitsCandidate R) (hW : 0 < W)
    (Rn : Composed (R := R) W P pick upd U V K H) {K' : ℕ} (hK' : K' ≤ K)
    (hcl : ∀ k, k < K' → Rn.RangeClosed k) : (Rn.ledgerUpto K').Nodup := by
  unfold ledgerUpto
  rw [List.nodup_flatMap]
  refine ⟨fun k hkm => rangeLedger_nodup hcc hW Rn
    (hcl k (by rw [List.mem_range] at hkm; omega)), ?_⟩
  have hpw : (List.range K').Pairwise (fun a b => a < b ∧ b < K') := by
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    simp only [List.getElem_range]
    rw [List.length_range] at hj
    exact ⟨hij, hj⟩
  exact hpw.imp (fun {a b} hab => rangeLedger_disjoint hcc hW Rn hab.1 (by omega)
    (hcl a (by omega)) (hcl b hab.2))

/-- **BN5a, the ledger is agreed**: two runs over one universe, held by
validators with different views of it, read the same blocks off every
range both have closed. It is `agreement` and nothing else — the starts
fix the interval, the widths fix where its rounds begin, and the verdicts
fix what it holds. -/
theorem rangeLedger_agree (hR : Properties.Agree R) (hW : 0 < W) (hgap : P.gap = 2 * W)
    (hadapted : ∀ (U : R.Universe) (V₁ V₂ : R.View U) v w k,
      (∀ j, epochOf W j + 2 ≤ epochOf W k → v j = w j) →
      pick U V₁ v k = pick U V₂ w k)
    (hupd : ∀ (U : R.Universe) (V₁ V₂ : R.View U) (m b : ℕ) (A : BlockId),
      upd m b U V₁ A = upd m b U V₂ A)
    {V' : R.View U} (Rn : Composed (R := R) W P pick upd U V K H)
    (Rn' : Composed (R := R) W P pick upd U V' K H)
    (hK : 0 < K) (hhor : W * (H + 1) ≤ Rn.F.cum (Rn.start K))
    {k : ℕ} (hk : k < K) (hcl : Rn.RangeClosed k) :
    Rn.rangeLedger k = Rn'.rangeLedger k := by
  obtain ⟨hv, hcfg, -, hwid⟩ := agreement hR hW hgap hadapted hupd Rn Rn' hK hhor
  have hs : Rn.start k = Rn'.start k := (hcfg k (by omega)).1
  have hs1 : Rn.start (k + 1) = Rn'.start (k + 1) := (hcfg (k + 1) (by omega)).1
  have hw : ∀ r, r < Rn.start (k + 1) + 1 → Rn'.F.width r = Rn.F.width r :=
    fun r hr => hwid (k + 1) (by omega) r (by omega)
  have hsm : Rn.start k ≤ Rn.start (k + 1) :=
    le_of_lt (Rn.toCompRun.start_lt k hk)
  unfold rangeLedger
  rw [← hs, ← hs1, Frame.cum_congr hw (le_refl (Rn.start (k + 1) + 1)),
    Frame.cum_congr hw (show Rn.start k + 1 ≤ Rn.start (k + 1) + 1 by omega)]
  refine ledgerOf_congr (fun g _ h2 => hv g ?_)
  exact (epochOf_lt_iff hW).mpr (by unfold RangeClosed at hcl; omega)

/-- **BN5a, whole**: the ledger to any height both runs have closed is
one list. -/
theorem ledgerUpto_agree (hR : Properties.Agree R) (hW : 0 < W) (hgap : P.gap = 2 * W)
    (hadapted : ∀ (U : R.Universe) (V₁ V₂ : R.View U) v w k,
      (∀ j, epochOf W j + 2 ≤ epochOf W k → v j = w j) →
      pick U V₁ v k = pick U V₂ w k)
    (hupd : ∀ (U : R.Universe) (V₁ V₂ : R.View U) (m b : ℕ) (A : BlockId),
      upd m b U V₁ A = upd m b U V₂ A)
    {V' : R.View U} (Rn : Composed (R := R) W P pick upd U V K H)
    (Rn' : Composed (R := R) W P pick upd U V' K H)
    (hK : 0 < K) (hhor : W * (H + 1) ≤ Rn.F.cum (Rn.start K))
    {K' : ℕ} (hK' : K' ≤ K) (hcl : ∀ k, k < K' → Rn.RangeClosed k) :
    Rn.ledgerUpto K' = Rn'.ledgerUpto K' := by
  induction K' with
  | zero => rfl
  | succ j ih =>
      have hj := ih (by omega) (fun k hk => hcl k (by omega))
      unfold ledgerUpto at *
      rw [List.range_succ, List.flatMap_append, List.flatMap_append, hj,
        List.flatMap_cons, List.flatMap_cons, List.flatMap_nil, List.flatMap_nil,
        rangeLedger_agree hR hW hgap hadapted hupd Rn Rn' hK hhor (by omega)
          (hcl j (by omega))]

end Composed

end Integration

end LeanDag
