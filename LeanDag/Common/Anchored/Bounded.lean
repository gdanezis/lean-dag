import LeanDag.Common.Anchored.Band
import LeanDag.Properties.Bounded
import Mathlib.Data.Finset.Max

/-!
# The bounded relation, and the descent

`DecidedWithin` is the anchored relation with every slot the derivation
mentions — the decided slot, the anchor, the eligible intermediates —
strictly below a bound. It is a rule's own tool rather than part of any
interface: the mechanisms read `Properties.DecidedBelow`, and
`decidedBelow_of_decidedWithin` carries this into that. What it adds is
a **tight** bound, which the semantic form cannot recover; the bound
lives in the relation because a `Decided` derivation is a proof of a
`Prop` and its anchors cannot be recovered from it.

Every derivation is bounded (`exists_bound`), and **the descent** — a
committed run of eligible span decides everything below it — is one
proof over the bounded relation, from which the unbounded form follows.
-/

namespace LeanDag

open Properties

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {P : Validity Validator BlockId Payload} {honest : Finset Validator}

namespace AnchoredRule

variable (R : AnchoredRule Validator BlockId Payload P honest)
variable [S : Slots Validator]

/-- **The bounded relation**: `Decided`, with every slot the derivation
mentions strictly below `B`. -/
inductive DecidedWithin (U : BlockRecord Validator BlockId Payload P honest) (V : U.View)
    (B : ℕ) : ℕ → Option BlockId → Prop
  /-- The direct rule commits a candidate outright. -/
  | directCommit {k : ℕ} {L : BlockId} :
      k < B → IsLeaderBlock U k L → R.Commit U V L (S.slotRound k) →
      DecidedWithin U V B k (some L)
  /-- The direct rule skips the slot. -/
  | directSkip {k : ℕ} :
      k < B → R.Skip U V S k → DecidedWithin U V B k none
  /-- Anchored below the bound, the tie-break's choice at the first
  nonempty rung is committed. -/
  | indirectCommit {k j : ℕ} {A L : BlockId} {i : ℕ} :
      k < j → j < B → R.Eligible k j → DecidedWithin U V B j (some A) →
      (∀ m, k < m → m < j → R.Eligible k m → DecidedWithin U V B m none) →
      i < R.rungs → (∀ i', i' < i → R.RungEmpty U A i' k) →
      IsLeaderBlock U k L → R.Link i U A L S k → R.Least U A i k L →
      DecidedWithin U V B k (some L)
  /-- Anchored below the bound, every rung is empty. -/
  | indirectSkip {k j : ℕ} {A : BlockId} :
      k < j → j < B → R.Eligible k j → DecidedWithin U V B j (some A) →
      (∀ m, k < m → m < j → R.Eligible k m → DecidedWithin U V B m none) →
      (∀ i, i < R.rungs → R.RungEmpty U A i k) →
      DecidedWithin U V B k none

variable {R} {I : Slots Validator → BlockRecord Validator BlockId Payload P honest → Prop}
variable {U : BlockRecord Validator BlockId Payload P honest}

/-- The bounded indirect commit at a single rung with no tie. -/
theorem DecidedWithin.indirectCommit_single {V : U.View} (h1 : R.rungs = 1)
    (hno : ∀ L L', ¬ R.tie 0 L L') {B k j : ℕ} {A L : BlockId}
    (hkj : k < j) (hjB : j < B) (helig : R.Eligible k j) (hj : R.DecidedWithin U V B j (some A))
    (hmid : ∀ m, k < m → m < j → R.Eligible k m → R.DecidedWithin U V B m none)
    (hL : IsLeaderBlock U k L) (hlink : R.Link 0 U A L S k) :
    R.DecidedWithin U V B k (some L) :=
  DecidedWithin.indirectCommit (i := 0) hkj hjB helig hj hmid (by omega)
    (fun i' hi' => absurd hi' (Nat.not_lt_zero _)) hL hlink (fun L' _ _ h => hno L' L h)

/-- The bounded indirect skip at a single rung. -/
theorem DecidedWithin.indirectSkip_single {V : U.View} (h1 : R.rungs = 1) {B k j : ℕ}
    {A : BlockId} (hkj : k < j) (hjB : j < B) (helig : R.Eligible k j)
    (hj : R.DecidedWithin U V B j (some A))
    (hmid : ∀ m, k < m → m < j → R.Eligible k m → R.DecidedWithin U V B m none)
    (hnone : ∀ L, IsLeaderBlock U k L → ¬ R.Link 0 U A L S k) :
    R.DecidedWithin U V B k none :=
  DecidedWithin.indirectSkip hkj hjB helig hj hmid (fun i hi L hL => by
    have : i = 0 := by omega
    subst this; exact hnone L hL)

namespace DecidedWithin

variable {V : U.View} {B B' k : ℕ} {v : Option BlockId}

/-- The bound is what it says: a derivation only names slots under it. -/
theorem lt_bound (h : R.DecidedWithin U V B k v) : k < B := by
  cases h with
  | directCommit hk _ _ => exact hk
  | directSkip hk _ => exact hk
  | indirectCommit _ hj _ _ _ _ _ _ _ _ => omega
  | indirectSkip _ hj _ _ _ _ => omega

/-- Forgetting the bound: every bounded derivation is a derivation. -/
theorem toDecided (h : R.DecidedWithin U V B k v) : R.Decided U V k v := by
  induction h with
  | directCommit _ hL hdc => exact Decided.directCommit hL hdc
  | directSkip _ hall => exact Decided.directSkip hall
  | indirectCommit hkj _ helig _ _ hi hemp hL hlink hmin ihj ihmid =>
      exact Decided.indirectCommit hkj helig ihj ihmid hi hemp hL hlink hmin
  | indirectSkip hkj _ helig _ _ hnone ihj ihmid =>
      exact Decided.indirectSkip hkj helig ihj ihmid hnone

/-- The bound relaxes upward. -/
theorem mono (h : R.DecidedWithin U V B k v) (hBB : B ≤ B') : R.DecidedWithin U V B' k v := by
  induction h with
  | directCommit hk hL hdc => exact directCommit (by omega) hL hdc
  | directSkip hk hall => exact directSkip (by omega) hall
  | indirectCommit hkj hj helig _ _ hi hemp hL hlink hmin ihj ihmid =>
      exact indirectCommit hkj (by omega) helig ihj (fun m h1 h2 h3 => ihmid m h1 h2 h3)
        hi hemp hL hlink hmin
  | indirectSkip hkj hj helig _ _ hnone ihj ihmid =>
      exact indirectSkip hkj (by omega) helig ihj (fun m h1 h2 h3 => ihmid m h1 h2 h3) hnone

/-- Two bounded verdicts agree — agreement, through the embedding. -/
theorem agree (hl : R.Laws I) (hI : I S U) {V₁ V₂ : U.View} {B₁ B₂ k : ℕ}
    {v₁ v₂ : Option BlockId} (h₁ : R.DecidedWithin U V₁ B₁ k v₁)
    (h₂ : R.DecidedWithin U V₂ B₂ k v₂) : v₁ = v₂ :=
  decided_agree hl hI h₁.toDecided h₂.toDecided

end DecidedWithin

/-- **Every derivation is bounded**: by the largest slot it mentions. -/
theorem exists_bound {V : U.View} {k : ℕ} {v : Option BlockId} (h : R.Decided U V k v) :
    ∃ B, R.DecidedWithin U V B k v := by
  classical
  induction h with
  | @directCommit k L hL hc => exact ⟨k + 1, DecidedWithin.directCommit (by omega) hL hc⟩
  | @directSkip k hs => exact ⟨k + 1, DecidedWithin.directSkip (by omega) hs⟩
  | @indirectCommit k j A L i hkj helig _ hmid hi hemp hL hlink hmin ihj ihmid =>
      obtain ⟨Bj, hj⟩ := ihj
      set f : ℕ → ℕ := fun m =>
        if hh : k < m ∧ m < j ∧ R.Eligible (S := S) k m then
          (ihmid m hh.1 hh.2.1 hh.2.2).choose else 0 with hf
      refine ⟨max Bj ((Finset.Ico (k + 1) j).sup f) + (j + 1), ?_⟩
      refine DecidedWithin.indirectCommit hkj (by omega) helig
        (hj.mono (by omega)) ?_ hi hemp hL hlink hmin
      intro m h1 h2 h3
      have heqf : f m = (ihmid m h1 h2 h3).choose := by
        simp only [hf]; exact dif_pos ⟨h1, h2, h3⟩
      have hle : f m ≤ (Finset.Ico (k + 1) j).sup f :=
        Finset.le_sup (Finset.mem_Ico.mpr ⟨by omega, h2⟩)
      exact (ihmid m h1 h2 h3).choose_spec.mono (by omega)
  | @indirectSkip k j A hkj helig _ hmid hnone ihj ihmid =>
      obtain ⟨Bj, hj⟩ := ihj
      set f : ℕ → ℕ := fun m =>
        if hh : k < m ∧ m < j ∧ R.Eligible (S := S) k m then
          (ihmid m hh.1 hh.2.1 hh.2.2).choose else 0 with hf
      refine ⟨max Bj ((Finset.Ico (k + 1) j).sup f) + (j + 1), ?_⟩
      refine DecidedWithin.indirectSkip hkj (by omega) helig (hj.mono (by omega)) ?_ hnone
      intro m h1 h2 h3
      have heqf : f m = (ihmid m h1 h2 h3).choose := by
        simp only [hf]; exact dif_pos ⟨h1, h2, h3⟩
      have hle : f m ≤ (Finset.Ico (k + 1) j).sup f :=
        Finset.le_sup (Finset.mem_Ico.mpr ⟨by omega, h2⟩)
      exact (ihmid m h1 h2 h3).choose_spec.mono (by omega)

/-! ## Congruence in the schedule -/

/-- **The bounded relation moves with the schedule**, for any two
schedules naming the same rounds and the same leaders below the bound:
the candidate set reads the schedule only through `IsLeaderBlock`, the
direct skip only at its slot, and the links not at all. -/
theorem decidedWithin_congr_of_slotRound (hl : R.Laws I) {S₁ S₂ : Slots Validator} (hI : I S₁ U)
    (hround : S₁.slotRound = S₂.slotRound) {V : U.View} {B k : ℕ} {v : Option BlockId}
    (ha : ∀ m, m < B → S₁.leader m = S₂.leader m)
    (h : R.DecidedWithin (S := S₁) U V B k v) : R.DecidedWithin (S := S₂) U V B k v := by
  obtain ⟨sr, ld, hmono, hunb, hkeyed⟩ := S₁
  obtain ⟨sr', ld', hmono', hunb', hkeyed'⟩ := S₂
  simp only at hround
  subst hround
  induction h with
  | @directCommit k L hk hL hdc =>
      exact DecidedWithin.directCommit (S := ⟨sr, ld', hmono', hunb', hkeyed'⟩) hk
        (isLeaderBlock_congr (S₁ := ⟨sr, ld, hmono, hunb, hkeyed⟩)
          (S₂ := ⟨sr, ld', hmono', hunb', hkeyed'⟩) rfl (ha k hk) hL) hdc
  | @directSkip k hk hall =>
      exact DecidedWithin.directSkip (S := ⟨sr, ld', hmono', hunb', hkeyed'⟩) hk
        (hl.skip_congr hI (S₁ := ⟨sr, ld, hmono, hunb, hkeyed⟩)
          (S₂ := ⟨sr, ld', hmono', hunb', hkeyed'⟩) rfl (ha k hk) hall)
  | @indirectCommit k j A L i hkj hj helig _ _ hi hemp hL hlink hmin ihj ihmid =>
      refine DecidedWithin.indirectCommit (S := ⟨sr, ld', hmono', hunb', hkeyed'⟩) hkj hj helig
        ihj (fun m h1 h2 h3 => ihmid m h1 h2 h3) hi ?_
        (isLeaderBlock_congr (S₁ := ⟨sr, ld, hmono, hunb, hkeyed⟩)
          (S₂ := ⟨sr, ld', hmono', hunb', hkeyed'⟩) rfl (ha k (by omega)) hL)
        (hl.link_congr (S₁ := ⟨sr, ld, hmono, hunb, hkeyed⟩)
          (S₂ := ⟨sr, ld', hmono', hunb', hkeyed'⟩) rfl (ha k (by omega)) hlink) ?_
      · intro i' hi' L' hL' hlink'
        exact hemp i' hi' L' (isLeaderBlock_congr (S₁ := ⟨sr, ld', hmono', hunb', hkeyed'⟩)
          (S₂ := ⟨sr, ld, hmono, hunb, hkeyed⟩) rfl (ha k (by omega)).symm hL')
          (hl.link_congr (S₁ := ⟨sr, ld', hmono', hunb', hkeyed'⟩)
            (S₂ := ⟨sr, ld, hmono, hunb, hkeyed⟩) rfl (ha k (by omega)).symm hlink')
      · intro L' hL' hlink'
        exact hmin L' (isLeaderBlock_congr (S₁ := ⟨sr, ld', hmono', hunb', hkeyed'⟩)
          (S₂ := ⟨sr, ld, hmono, hunb, hkeyed⟩) rfl (ha k (by omega)).symm hL')
          (hl.link_congr (S₁ := ⟨sr, ld', hmono', hunb', hkeyed'⟩)
            (S₂ := ⟨sr, ld, hmono, hunb, hkeyed⟩) rfl (ha k (by omega)).symm hlink')
  | @indirectSkip k j A hkj hj helig _ _ hnone ihj ihmid =>
      refine DecidedWithin.indirectSkip (S := ⟨sr, ld', hmono', hunb', hkeyed'⟩) hkj hj helig
        ihj (fun m h1 h2 h3 => ihmid m h1 h2 h3) ?_
      intro i hi L hL hlink
      exact hnone i hi L (isLeaderBlock_congr (S₁ := ⟨sr, ld', hmono', hunb', hkeyed'⟩)
        (S₂ := ⟨sr, ld, hmono, hunb, hkeyed⟩) rfl (ha k (by omega)).symm hL)
        (hl.link_congr (S₁ := ⟨sr, ld', hmono', hunb', hkeyed'⟩)
          (S₂ := ⟨sr, ld, hmono, hunb, hkeyed⟩) rfl (ha k (by omega)).symm hlink)

/-! ## The tie-break's choice -/

/-- At a rung with no tie, any linked candidate is the choice. -/
theorem least_of_no_tie {A L : BlockId} {i k : ℕ} (hno : ∀ L L', ¬ R.tie i L L') :
    R.Least (S := S) U A i k L :=
  fun L' _ _ h => hno L' L h

/-- At a rung whose tie is the order, the least linked candidate is the
choice; one exists whenever the rung is nonempty. -/
theorem exists_least_of_lt [LinearOrder BlockId] {A : BlockId} {i k : ℕ}
    (hlt : ∀ L L', R.tie i L L' ↔ L < L')
    (h : ∃ L, IsLeaderBlock (S := S) U k L ∧ R.Link i U A L S k) :
    ∃ L, IsLeaderBlock (S := S) U k L ∧ R.Link i U A L S k ∧
      R.Least (S := S) U A i k L := by
  classical
  obtain ⟨L₀, hL₀, hl₀⟩ := h
  set s := U.ids.filter (fun L => IsLeaderBlock (S := S) U k L ∧ R.Link i U A L S k)
    with hs
  have hne : s.Nonempty := ⟨L₀, Finset.mem_filter.mpr ⟨hL₀.1, hL₀, hl₀⟩⟩
  refine ⟨s.min' hne, (Finset.mem_filter.mp (s.min'_mem hne)).2.1,
    (Finset.mem_filter.mp (s.min'_mem hne)).2.2, ?_⟩
  intro L' hL' hl' ht
  rw [hlt] at ht
  exact absurd (s.min'_le L' (Finset.mem_filter.mpr ⟨hL'.1, hL', hl'⟩)) (not_le.mpr ht)

/-! ## Totality at an anchor -/

/-- **Under the nearest eligible committed anchor the slot is decided**:
the first nonempty rung's choice commits, or every rung is empty and the
slot skips. -/
theorem exists_decided_of_anchor
    (hleast : ∀ {A : BlockId} {i k : ℕ}, i < R.rungs →
      (∃ L, IsLeaderBlock (S := S) U k L ∧ R.Link i U A L S k) →
      ∃ L, IsLeaderBlock (S := S) U k L ∧ R.Link i U A L S k ∧
        R.Least (S := S) U A i k L)
    {V : U.View} {k j : ℕ} {A : BlockId} (helig : R.Eligible (S := S) k j)
    (hj : R.Decided (S := S) U V j (some A))
    (hmid : ∀ m, k < m → m < j → R.Eligible (S := S) k m → R.Decided (S := S) U V m none) :
    ∃ v, R.Decided (S := S) U V k v := by
  classical
  have hkj : k < j := R.lt_of_eligible helig
  by_cases hc : ∃ r, r < R.rungs ∧ ∃ L, IsLeaderBlock (S := S) U k L ∧ R.Link r U A L S k
  · let r₀ := Nat.find hc
    have hr₀ := Nat.find_spec hc
    obtain ⟨L, hL, hlink, hmin⟩ := hleast hr₀.1 hr₀.2
    refine ⟨some L, Decided.indirectCommit (i := r₀) hkj helig hj hmid hr₀.1 ?_ hL hlink hmin⟩
    intro r' hr' L' hL' hlink'
    exact Nat.find_min hc hr' ⟨lt_trans hr' hr₀.1, L', hL', hlink'⟩
  · push Not at hc
    exact ⟨none, Decided.indirectSkip hkj helig hj hmid fun r hr L hL hlink => hc r hr L hL hlink⟩

/-! ## The descent -/

/-- **A committed run of eligible span decides everything below it**,
within any bound above the run. Walk down from the run, anchoring each
slot on the nearest eligible committed slot above it — whose
intermediate premise the induction supplies, every eligible slot between
being decided and not committed — and read the rungs there. -/
theorem decidedWithin_below_of_committed_run
    (hleast : ∀ {A : BlockId} {i k : ℕ}, i < R.rungs →
      (∃ L, IsLeaderBlock (S := S) U k L ∧ R.Link i U A L S k) →
      ∃ L, IsLeaderBlock (S := S) U k L ∧ R.Link i U A L S k ∧
        R.Least (S := S) U A i k L)
    {V : U.View} {b n B : ℕ} (hbn : b ≤ n) (hnB : n < B)
    (hspan : ∀ i, i < b → R.Eligible (S := S) i n)
    (hrun : ∀ j, b ≤ j → j ≤ n → ∃ L, R.DecidedWithin (S := S) U V B j (some L)) :
    ∀ i, i < b → ∃ v, R.DecidedWithin (S := S) U V B i v := by
  classical
  have key : ∀ d i, i < b → b - i ≤ d → ∃ v, R.DecidedWithin (S := S) U V B i v := by
    intro d
    induction d with
    | zero => intro i hi hd; omega
    | succ d ih =>
      intro i hi hd
      -- the nearest eligible committed slot above `i`
      have hex : ∃ j, R.Eligible (S := S) i j ∧ ∃ A, R.DecidedWithin (S := S) U V B j (some A) :=
        ⟨n, hspan i hi, hrun n hbn le_rfl⟩
      let j := Nat.find hex
      have hj := Nat.find_spec hex
      obtain ⟨helig, A, hA⟩ := hj
      have hjn : j ≤ n := Nat.find_min' hex ⟨hspan i hi, hrun n hbn le_rfl⟩
      have hij : i < j := R.lt_of_eligible helig
      have hmid : ∀ m, i < m → m < j → R.Eligible (S := S) i m →
          R.DecidedWithin (S := S) U V B m none := by
        intro m him hmj hem
        have hnot : ¬ ∃ A, R.DecidedWithin (S := S) U V B m (some A) :=
          fun hc => Nat.find_min hex hmj ⟨hem, hc⟩
        by_cases hmb : b ≤ m
        · exact absurd (hrun m hmb (by omega)) hnot
        · obtain ⟨v, hv⟩ := ih m (by omega) (by omega)
          cases v with
          | none => exact hv
          | some A' => exact absurd ⟨A', hv⟩ hnot
      by_cases hc : ∃ r, r < R.rungs ∧ ∃ L, IsLeaderBlock (S := S) U i L ∧
          R.Link r U A L S i
      · let r₀ := Nat.find hc
        have hr₀ := Nat.find_spec hc
        obtain ⟨L, hL, hlink, hmin⟩ := hleast hr₀.1 hr₀.2
        refine ⟨some L, DecidedWithin.indirectCommit (i := r₀) hij (by omega) helig hA hmid
          hr₀.1 ?_ hL hlink hmin⟩
        intro r' hr' L' hL' hlink'
        exact Nat.find_min hc hr' ⟨lt_trans hr' hr₀.1, L', hL', hlink'⟩
      · push Not at hc
        exact ⟨none, DecidedWithin.indirectSkip hij (by omega) helig hA hmid
          fun r hr L hL hlink => hc r hr L hL hlink⟩
  exact fun i hi => key (b - i) i hi le_rfl

/-- **The descent, unbounded**: every derivation is bounded, so the run
sits within one bound and the bounded descent applies. -/
theorem decided_below_of_committed_run
    (hleast : ∀ {A : BlockId} {i k : ℕ}, i < R.rungs →
      (∃ L, IsLeaderBlock (S := S) U k L ∧ R.Link i U A L S k) →
      ∃ L, IsLeaderBlock (S := S) U k L ∧ R.Link i U A L S k ∧
        R.Least (S := S) U A i k L)
    {V : U.View} {b n : ℕ} (hbn : b ≤ n)
    (hspan : ∀ i, i < b → R.Eligible (S := S) i n)
    (hrun : ∀ j, b ≤ j → j ≤ n → ∃ L, R.Decided (S := S) U V j (some L)) :
    ∀ i, i < b → ∃ v, R.Decided (S := S) U V i v := by
  classical
  -- a bound above every commit of the run
  have hb : ∀ j, ∃ Bj, b ≤ j → j ≤ n → ∃ L, R.DecidedWithin (S := S) U V Bj j (some L) := by
    intro j
    by_cases hj : b ≤ j ∧ j ≤ n
    · obtain ⟨L, hL⟩ := hrun j hj.1 hj.2
      obtain ⟨Bj, hBj⟩ := exists_bound hL
      exact ⟨Bj, fun _ _ => ⟨L, hBj⟩⟩
    · exact ⟨0, fun h1 h2 => absurd ⟨h1, h2⟩ hj⟩
  choose Bf hBf using hb
  set B := max ((Finset.Icc b n).sup Bf) n + 1 with hB
  have hrun' : ∀ j, b ≤ j → j ≤ n → ∃ L, R.DecidedWithin (S := S) U V B j (some L) := by
    intro j h1 h2
    obtain ⟨L, hL⟩ := hBf j h1 h2
    have : Bf j ≤ (Finset.Icc b n).sup Bf := Finset.le_sup (Finset.mem_Icc.mpr ⟨h1, h2⟩)
    exact ⟨L, hL.mono (by omega)⟩
  intro i hi
  obtain ⟨v, hv⟩ := decidedWithin_below_of_committed_run hleast (B := B) hbn (by omega)
    hspan hrun' i hi
  exact ⟨v, hv.toDecided⟩

/-- **The descent below a run**: `c` slots from `b` whose leaders satisfy
`Led`, each of which commits when its leader does, decide every slot below
`b`. -/
theorem decided_below_of_run
    (hleast : ∀ {A : BlockId} {i k : ℕ}, i < R.rungs →
      (∃ L, IsLeaderBlock (S := S) U k L ∧ R.Link i U A L S k) →
      ∃ L, IsLeaderBlock (S := S) U k L ∧ R.Link i U A L S k ∧
        R.Least (S := S) U A i k L)
    {V : U.View} {b c : ℕ} (hc : 0 < c) (hspan : R.SpansEligible (S := S) c)
    {Led : ℕ → Prop} (hrun : ∀ i, i < c → Led (b + i))
    (commit : ∀ j, b ≤ j → j ≤ b + c - 1 → Led j → ∃ L, R.Decided (S := S) U V j (some L)) :
    ∀ i, i < b → ∃ v, R.Decided (S := S) U V i v :=
  decided_below_of_committed_run hleast (b := b) (n := b + c - 1) (by omega)
    (fun i hi => hspan b i hi) fun j h1 h2 => commit j h1 h2 (by
      have := hrun (j - b) (by omega)
      rwa [Nat.add_sub_cancel' h1] at this)

/-- Totality, from a choice at every nonempty rung. -/
theorem total_of_least
    (hleast : ∀ {A : BlockId} {i k : ℕ}, i < R.rungs →
      (∃ L, IsLeaderBlock (S := S) U k L ∧ R.Link i U A L S k) →
      ∃ L, IsLeaderBlock (S := S) U k L ∧ R.Link i U A L S k ∧
        R.Least (S := S) U A i k L) :
    R.Total (S := S) U :=
  fun _ _ _ _ helig hj hmid => exists_decided_of_anchor hleast helig hj hmid

/-- The descent below a committed run, from a choice at every nonempty rung. -/
theorem decidedBelowRun_of_least
    (hleast : ∀ {A : BlockId} {i k : ℕ}, i < R.rungs →
      (∃ L, IsLeaderBlock (S := S) U k L ∧ R.Link i U A L S k) →
      ∃ L, IsLeaderBlock (S := S) U k L ∧ R.Link i U A L S k ∧
        R.Least (S := S) U A i k L) :
    R.DecidedBelowRun (S := S) U :=
  fun _ b _ hc hspan hrun i hi =>
    decided_below_of_committed_run hleast (by omega) (fun i hi => hspan b i hi) hrun i hi

end AnchoredRule

/-! ## Into the derived relation -/

section Mechanised

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {P : Validity Validator BlockId Payload} {honest : Finset Validator}
variable {R : AnchoredRule Validator BlockId Payload P honest} [S : Slots Validator]
variable {I : Slots Validator → BlockRecord Validator BlockId Payload P honest → Prop}
variable {U : BlockRecord Validator BlockId Payload P honest} [P.Mechanised]

namespace AnchoredRule

/-- **The bounded relation lands in the derived one.** -/
theorem decidedBelow_of_decidedWithin (hl : R.Laws I) (hI : I S U) {V : U.View}
    {B k : ℕ} {v : Option BlockId} (h : R.DecidedWithin (S := S) U V B k v) :
    DecidedBelow R.toDagRule S B V k v :=
  ⟨h.lt_bound, h.toDecided, fun S' hround hlead =>
    (decidedWithin_congr_of_slotRound hl hI (S₁ := S) (S₂ := S') hround.symm
      (fun m hm => (hlead m hm).symm) h).toDecided⟩

end AnchoredRule

end Mechanised

end LeanDag
