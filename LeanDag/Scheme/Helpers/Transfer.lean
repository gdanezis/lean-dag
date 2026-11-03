import LeanDag.Common.Anchored.Band
/-!
# Two anchored rules that read alike decide alike

If two anchored rules have the same wave and rungs, and their direct
predicates, links and tie-break choices agree wherever `Decided` reads
them — at a candidate of the slot and an anchor of an eligible slot —
then their decision relations are equal, and so are their carriers.
Every property stated over a carrier then holds of one exactly when it
holds of the other.
-/

namespace LeanDag

namespace Scheme

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {P : Validity Validator BlockId Payload} {honest : Finset Validator}
variable [S : Slots Validator] {U : BlockRecord Validator BlockId Payload P honest}

/-- **What `Decided` reads, agreeing**, at one record. -/
structure ReadAlike (R₁ R₂ : AnchoredRule Validator BlockId Payload P honest)
    (U : BlockRecord Validator BlockId Payload P honest) : Prop where
  waveAt : ∀ κ, R₁.waveAt κ = R₂.waveAt κ
  rungs : R₁.rungs = R₂.rungs
  commit : ∀ (V : U.View) {k : ℕ} {L : BlockId}, IsLeaderBlock U k L →
    (R₁.Commit U V L (S.slotRound k) (S.kind k) ↔ R₂.Commit U V L (S.slotRound k) (S.kind k))
  skip : ∀ (V : U.View) (k : ℕ), R₁.Skip U V S k ↔ R₂.Skip U V S k
  link : ∀ {i k j : ℕ} {A L : BlockId}, i < R₁.rungs → IsLeaderBlock U k L →
    IsLeaderBlock U j A → R₁.Eligible k j → (R₁.Link i U A L S k ↔ R₂.Link i U A L S k)
  least : ∀ {i k j : ℕ} {A L : BlockId}, i < R₁.rungs → IsLeaderBlock U k L →
    IsLeaderBlock U j A → R₁.Eligible k j → R₁.Link i U A L S k →
    (R₁.Least U A i k L ↔ R₂.Least U A i k L)

namespace ReadAlike

variable {R₁ R₂ : AnchoredRule Validator BlockId Payload P honest}

theorem eligible_iff (h : ReadAlike R₁ R₂ U) {k j : ℕ} : R₁.Eligible k j ↔ R₂.Eligible k j := by
  rw [AnchoredRule.eligible_iff, AnchoredRule.eligible_iff, h.waveAt]

/-- The agreement read from the other side. -/
theorem symm (h : ReadAlike R₁ R₂ U) : ReadAlike R₂ R₁ U where
  waveAt := fun κ => (h.waveAt κ).symm
  rungs := h.rungs.symm
  commit := fun V _ _ hL => (h.commit V hL).symm
  skip := fun V k => (h.skip V k).symm
  link := fun hi hL hA he => (h.link (h.rungs ▸ hi) hL hA (h.eligible_iff.mpr he)).symm
  least := fun hi hL hA he hl => by
    have hi' : _ < R₁.rungs := h.rungs ▸ hi
    have he' := h.eligible_iff.mpr he
    exact (h.least hi' hL hA he' ((h.link hi' hL hA he').mpr hl)).symm

theorem decided (h : ReadAlike R₁ R₂ U) {V : U.View} {k : ℕ} {v : Option BlockId}
    (hd : R₁.Decided U V k v) : R₂.Decided U V k v := by
  induction hd with
  | directCommit hL hc => exact .directCommit hL ((h.commit V hL).mp hc)
  | directSkip hs => exact .directSkip ((h.skip V _).mp hs)
  | indirectCommit hkj he hj hmid hi hempty hL hlink hleast ihj ihmid =>
    have hA := AnchoredRule.isLeaderBlock_of_decided hj
    exact .indirectCommit hkj (h.eligible_iff.mp he) ihj
      (fun m h1 h2 hm => ihmid m h1 h2 (h.eligible_iff.mpr hm)) (h.rungs ▸ hi)
      (fun i' hi' L' hL' hl' => hempty i' hi' L' hL'
        ((h.link (by omega) hL' hA he).mpr hl'))
      hL ((h.link hi hL hA he).mp hlink) ((h.least hi hL hA he hlink).mp hleast)
  | indirectSkip hkj he hj hmid hempty ihj ihmid =>
    have hA := AnchoredRule.isLeaderBlock_of_decided hj
    exact .indirectSkip hkj (h.eligible_iff.mp he) ihj
      (fun m h1 h2 hm => ihmid m h1 h2 (h.eligible_iff.mpr hm))
      (fun i hi L hL hl => hempty i (h.rungs ▸ hi) L hL
        ((h.link (h.rungs ▸ hi) hL hA he).mpr hl))

theorem decided_iff (h : ReadAlike R₁ R₂ U) {V : U.View} {k : ℕ} {v : Option BlockId} :
    R₁.Decided U V k v ↔ R₂.Decided U V k v :=
  ⟨h.decided, h.symm.decided⟩

end ReadAlike

variable [P.Mechanised] {R₁ R₂ : AnchoredRule Validator BlockId Payload P honest}

omit S in
/-- **Rules that decide alike have one carrier.** -/
theorem toDagRule_eq
    (h : ∀ (S : Slots Validator) (U : BlockRecord Validator BlockId Payload P honest)
      (V : U.View) (k : ℕ) (v : Option BlockId),
      R₁.Decided (S := S) U V k v ↔ R₂.Decided (S := S) U V k v) :
    R₁.toDagRule = R₂.toDagRule := by
  unfold AnchoredRule.toDagRule
  congr
  funext S U V k v
  exact propext (h S U V k v)

omit S in
/-- **And one carrier under any invariant.** -/
theorem toDagRuleOn_eq (I : BlockRecord Validator BlockId Payload P honest → Prop)
    (h : ∀ (S : Slots Validator) (U : BlockRecord Validator BlockId Payload P honest), I U →
      ∀ (V : U.View) (k : ℕ) (v : Option BlockId),
      R₁.Decided (S := S) U V k v ↔ R₂.Decided (S := S) U V k v) :
    R₁.toDagRuleOn I = R₂.toDagRuleOn I := by
  unfold AnchoredRule.toDagRuleOn AnchoredRule.toDagRuleVia
  congr
  funext S U V k v
  exact propext (h S U.val U.property V k v)

end Scheme

end LeanDag
