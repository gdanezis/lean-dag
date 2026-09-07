import LeanDag.Odontoceti.Rules
import LeanDag.Common.Anchored.Bounded
import LeanDag.Common.Rules
/-!
# Odontoceti: the decision relation

`odontoceti.md` §4, OP3. Odontoceti decides by the anchored relation
(`Anchored.lean`) at its data: wavelength one — supports at the decision
round are the whole story, there is no certificate round — the
supporter-quorum direct commit, the core's slot-level direct skip, and
one rung of link, `ThickLink`, with the **least** linked candidate
committed. That tie-break is not decoration — it is a gap in the thesis
made explicit. Lemma 5's proof asserts that sharing an anchor yields
agreement, but nothing in the quorum arithmetic prevents two
equivocating candidates from *both* passing `ThickLink` at one anchor
(the witness file realises exactly that configuration on data at
`n = 5f+1`); the implementation's determinism — the iteration order of
`GetLeaderBlocks` — is what actually arbitrates, and the tie is that
determinism as mathematics, under `[LinearOrder BlockId]`.

What Odontoceti proves is `odontocetiLaws`: the direct/direct cases by
O1/O1′, the direct-versus-indirect crossings by O2/O3/O4′ — a directly
committed block is the unique candidate that can pass the test
anywhere, which is why the direct verdicts need no tie — and two
tie-break choices equal by antisymmetry. Agreement (O5), the band and
the descent are the relation's.
-/

namespace LeanDag

namespace Odontoceti

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults5 Validator]
variable {BlockId : Type} [LinearOrder BlockId] {Payload : Type}
variable {U : BlockUniverse Validator BlockId Payload}
variable [S : Slots Validator]
variable {L A : BlockId} {r k : ℕ}

/-! ## The view-relative direct rules -/

/-- Direct commit, as judged from a single view: the view holds votes for
`L` at the round above it from a quorum of validators. -/
abbrev DirectCommitIn (U : BlockUniverse Validator BlockId Payload)
    (V : View Validator BlockId Payload U) (L : BlockId) (r : ℕ) : Prop :=
  supportCommit (quorumCard Validator) U V L r

/-- Direct skip, as judged from a single view: the view holds blocks at
the round above `L` that omit it, from a quorum of validators. -/
abbrev DirectSkipIn (U : BlockUniverse Validator BlockId Payload)
    (V : View Validator BlockId Payload U) (L : BlockId) (r : ℕ) : Prop :=
  HoldsAtLeast U V (quorumCard Validator) (omissionsOf U L (r + 1))

/-- A view can only under-report: its direct commit is genuine. -/
theorem directCommit_of_directCommitIn
    {V : View Validator BlockId Payload U}
    (h : DirectCommitIn U V L r) : DirectCommit U L r := h.le

/-- A view can only under-report: its direct skip is genuine. -/
theorem directSkip_of_directSkipIn
    {V : View Validator BlockId Payload U}
    (h : DirectSkipIn U V L r) : DirectSkip U L r := h.le

/-! ## The safety lemmas, lifted to views -/

/-- Cross-view O1: one validator cannot directly commit what another
directly skips. -/
theorem not_directSkipIn_of_directCommitIn
    {V₁ V₂ : View Validator BlockId Payload U}
    (h₁ : DirectCommitIn U V₁ L r) (h₂ : DirectSkipIn U V₂ L r) : False :=
  not_directSkip_of_directCommit
    (directCommit_of_directCommitIn h₁) (directSkip_of_directSkipIn h₂)

/-- Cross-view O1′: two direct commits for one slot agree. -/
theorem eq_of_directCommitIn {V₁ V₂ : View Validator BlockId Payload U}
    {k : ℕ} {L₁ L₂ : BlockId}
    (hL₁ : IsLeaderBlock U k L₁) (hL₂ : IsLeaderBlock U k L₂)
    (h₁ : DirectCommitIn U V₁ L₁ r) (h₂ : DirectCommitIn U V₂ L₂ r) :
    L₁ = L₂ :=
  eq_of_directCommit (directCommit_of_directCommitIn h₁)
    (directCommit_of_directCommitIn h₂) (by rw [hL₁.2.2, hL₂.2.2])

/-- O3, from a view: a view-level direct commit passes the indirect
test at every block two rounds up. -/
theorem thickLink_of_directCommitIn {V : View Validator BlockId Payload U}
    (h : DirectCommitIn U V L r) (hA : A ∈ U.ids)
    (hround : r + 2 ≤ (U.block A).round) : ThickLink U A L r :=
  thickLink_of_directCommit (directCommit_of_directCommitIn h) hA hround

/-- O2, from a view: a view-level direct skip fails the indirect test
everywhere. -/
theorem not_thickLink_of_directSkipIn {V : View Validator BlockId Payload U}
    (h : DirectSkipIn U V L r) (A : BlockId) : ¬ ThickLink U A L r :=
  not_thickLink_of_directSkip (directSkip_of_directSkipIn h) A

/-- O4′, from a view: a view-level direct commit is the only same-slot
candidate that can pass the indirect test, at any anchor. -/
theorem eq_of_directCommitIn_of_thickLink
    {V : View Validator BlockId Payload U} {k : ℕ} {L₁ L₂ : BlockId}
    (hL₁ : IsLeaderBlock U k L₁) (hL₂ : IsLeaderBlock U k L₂)
    (h₁ : DirectCommitIn U V L₁ r) (ht : ThickLink U A L₂ r) : L₁ = L₂ :=
  eq_of_directCommit_of_thickLink (directCommit_of_directCommitIn h₁) ht
    (by rw [hL₁.2.2, hL₂.2.2])

/-! ## The relation -/

omit S in
/-- **Odontoceti as an anchored rule.** -/
def odontocetiAnchored (Validator BlockId Payload : Type) [Fintype Validator]
    [DecidableEq Validator] [Faults5 Validator] [LinearOrder BlockId] :
    AnchoredRule Validator BlockId Payload ValidWrt Correct where
  wave := 1
  Commit := fun U V L r => Odontoceti.DirectCommitIn U V L r
  decCommit := fun _ _ _ _ => inferInstance
  Skip := fun U V S k => DirectSkipSlotIn (S := S) U V k
  rungs := 1
  Link := fun _ U A L S k => ThickLink U A L (S.slotRound k)
  tie := fun _ L L' => L < L'

omit S in
@[simp] theorem odontocetiAnchored_wave :
    (odontocetiAnchored Validator BlockId Payload).wave = 1 := rfl
omit S in
@[simp] theorem odontocetiAnchored_rungs :
    (odontocetiAnchored Validator BlockId Payload).rungs = 1 := rfl

instance {V : View Validator BlockId Payload U} (L : BlockId) (r : ℕ) :
    Decidable ((odontocetiAnchored Validator BlockId Payload).Commit U V L r) :=
  inferInstanceAs (Decidable (Odontoceti.DirectCommitIn U V L r))

instance {V : View Validator BlockId Payload U} (k : ℕ) :
    Decidable ((odontocetiAnchored Validator BlockId Payload).Skip U V S k) :=
  inferInstanceAs (Decidable (DirectSkipSlotIn (S := S) U V k))

instance (i : ℕ) (A L : BlockId) (S : Slots Validator) (k : ℕ) :
    Decidable ((odontocetiAnchored Validator BlockId Payload).Link i U A L S k) :=
  inferInstanceAs (Decidable (ThickLink U A L (S.slotRound k)))

/-- **The decision relation**: the anchored relation at Odontoceti's data. -/
abbrev Decided (U : BlockUniverse Validator BlockId Payload) (V : View Validator BlockId Payload U) :
    ℕ → Option BlockId → Prop :=
  (odontocetiAnchored Validator BlockId Payload).Decided (S := S) U V

namespace Decided
export AnchoredRule.Decided (directCommit directSkip indirectCommit indirectSkip)
end Decided

/-- **The bounded relation**, at Odontoceti's data. -/
abbrev DecidedWithin (U : BlockUniverse Validator BlockId Payload)
    (V : View Validator BlockId Payload U) (B : ℕ) : ℕ → Option BlockId → Prop :=
  (odontocetiAnchored Validator BlockId Payload).DecidedWithin (S := S) U V B

namespace DecidedWithin
export AnchoredRule.DecidedWithin (directCommit directSkip indirectCommit indirectSkip)
end DecidedWithin

omit S in
/-- **Odontoceti's laws.** -/
theorem odontocetiLaws : (odontocetiAnchored Validator BlockId Payload).Laws where
  commit_unique := fun _ hL₁ hL₂ h₁ h₂ => eq_of_directCommitIn hL₁ hL₂ h₁ h₂
  commit_skip := fun _ hL h hskip =>
    not_directSkipIn_of_directCommitIn h (directSkipIn_of_directSkipSlotIn hskip hL)
  commit_link := fun _ _ h hA helig => ⟨0, Nat.one_pos, thickLink_of_directCommitIn h hA.1 (by
    have := (odontocetiAnchored Validator BlockId Payload).anchor_round_le hA helig
    simp only [odontocetiAnchored_wave] at this; omega)⟩
  commit_link_unique := by
    intro S U V k j i L₁ L₂ A _ hL₁ hL₂ h _ _ _ _ hlink _
    exact eq_of_directCommitIn_of_thickLink hL₁ hL₂ h hlink
  skip_link := fun _ hskip hL _ =>
    not_thickLink_of_directSkipIn (directSkipIn_of_directSkipSlotIn hskip hL) _
  link_unique := by
    intro S U k j i L₁ L₂ A _ hL₁ hL₂ _ _ _ _ hl₁ hl₂ hm₁ hm₂
    exact le_antisymm (not_lt.mp (show ¬ L₂ < L₁ from hm₁ L₂ hL₂ hl₂))
      (not_lt.mp (show ¬ L₁ < L₂ from hm₂ L₁ hL₁ hl₁))
  commit_mono := fun _ hsub h => HoldsAtLeast.mono hsub h
  skip_mono := fun _ hsub h => HoldsAtLeast.mono hsub h
  skip_congr := fun _ hround hk h => blameSkip_congr hround hk h
  link_congr := (odontocetiAnchored Validator BlockId Payload).linkCongr_of_round
    (fun _ U A L r => ThickLink U A L r) fun _ _ _ _ _ _ => rfl

omit S in
/-- The rung's tie is the order, so a nonempty rung has a least
candidate. -/
theorem exists_least {S : Slots Validator} {U : BlockUniverse Validator BlockId Payload}
    {A : BlockId} {i k : ℕ} (_ : i < (odontocetiAnchored Validator BlockId Payload).rungs)
    (h : ∃ L, IsLeaderBlock (S := S) U k L ∧
      (odontocetiAnchored Validator BlockId Payload).Link i U A L S k) :
    ∃ L, IsLeaderBlock (S := S) U k L ∧
      (odontocetiAnchored Validator BlockId Payload).Link i U A L S k ∧
      (odontocetiAnchored Validator BlockId Payload).Least (S := S) U A i k L :=
  AnchoredRule.exists_least_of_lt (fun _ _ => Iff.rfl) h

end Odontoceti

end LeanDag
