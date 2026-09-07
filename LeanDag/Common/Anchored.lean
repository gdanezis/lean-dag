import LeanDag.Common.Ledger
import LeanDag.Common.Rules
import LeanDag.Common.Leader
/-!
# The anchored decision relation

Every leader-based rule of this development decides a slot the same way.
A *direct* rule reads the slot's own rounds from a view and commits a
candidate or skips the slot outright. When the direct evidence is
inconclusive, the rule looks up to an **anchor** — the nearest eligible
slot above that is itself committed — and asks what that anchor's causal
history says about the slot's candidates, through one or more graded
*rungs* of link: a candidate linked at the first rung is committed; if no
candidate is linked at the first rung, one linked at the second is
committed; and so on; if no candidate is linked at any rung, the slot is
skipped. Where a rung may hold several candidates a tie-break names the
least.

What varies between the rules is only the data below: the wave offset in
eligibility, the direct commit and skip predicates, and the rungs with
their ties. What every rule proves about that data is `Laws`, eight facts
each rule has under its own name. From them, agreement across views,
monotonicity in the view, and the ledger's agreement follow once, here.

"Nearest" is stated positively: every eligible slot strictly between the
slot and its anchor is decided `none`. The negative reading would be a
negative premise, which an inductive definition cannot carry; the
positive form is equivalent, since the sweep decides every slot it
passes, and it keeps every recursive occurrence strictly positive.
-/

namespace LeanDag

variable {Validator : Type*} {BlockId : Type*} {Payload : Type*}
variable {P : Validity Validator BlockId Payload} {honest : Finset Validator}

/-! ## Eligibility, at a wave

`j` may anchor `k` when its proposal lies past `k`'s decision round, which
sits `wave` rounds above `k`'s proposal. A predicate on the pair of slots
alone — not on any view — which is what makes agreement go through: two
validators deciding the same slot agree on which slots may anchor it. -/

section EligibleAt

variable [S : Slots Validator]

/-- `j` may anchor `k` at wave `wave`. -/
def EligibleAt (wave k j : ℕ) : Prop := S.slotRound k + wave < S.slotRound j

theorem eligibleAt_iff {wave k j : ℕ} :
    EligibleAt (S := S) wave k j ↔ S.slotRound k + wave + 1 ≤ S.slotRound j := by
  simp only [EligibleAt]; omega

instance decidableEligibleAt (wave k j : ℕ) : Decidable (EligibleAt (S := S) wave k j) :=
  inferInstanceAs (Decidable (S.slotRound k + wave < S.slotRound j))

/-- An eligible anchor is a later slot. Monotonicity is what carries it. -/
theorem lt_of_eligibleAt {wave k j : ℕ} (h : EligibleAt (S := S) wave k j) : k < j := by
  by_contra hle
  have : S.slotRound j ≤ S.slotRound k := S.mono (by omega)
  simp only [EligibleAt] at h
  omega

/-- **Every slot has an eligible anchor somewhere**: the second job the
schedule's `unbounded` does. -/
theorem exists_eligibleAt (wave k : ℕ) : ∃ j, EligibleAt (S := S) wave k j := by
  obtain ⟨j, hj⟩ := S.unbounded (S.slotRound k + wave + 1)
  exact ⟨j, by rw [eligibleAt_iff]; omega⟩

/-- Under a schedule whose consecutive slots are spaced past the wave,
every later slot is an eligible anchor. -/
theorem eligibleAt_of_lt_of_spacing {wave : ℕ}
    (hsp : ∀ k, S.slotRound k + wave + 1 ≤ S.slotRound (k + 1)) {k j : ℕ} (h : k < j) :
    EligibleAt (S := S) wave k j := by
  rw [eligibleAt_iff]
  induction j with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with hlt | heq
    · have := ih hlt
      have := hsp n
      omega
    · subst heq
      exact hsp k

/-- **A run of `c` slots reaches past everything below it**, at a wave:
the last slot of any `c` consecutive slots is eligible for every slot
below the first. -/
def SpansEligibleAt (wave c : ℕ) : Prop :=
  ∀ b i : ℕ, i < b → EligibleAt (S := S) wave i (b + c - 1)

end EligibleAt

/-! ## The rule's data -/

/-- **An anchored rule**: what a leader-based decision rule supplies. -/
structure AnchoredRule (Validator : Type*) (BlockId : Type*) (Payload : Type*)
    (P : Validity Validator BlockId Payload) (honest : Finset Validator) where
  /-- The rounds a slot's direct rules read above its proposal, less one:
  an anchor must sit strictly above `slotRound k + wave`. -/
  wave : ℕ
  /-- The direct commit, judged from a view: `Commit U V L r` says the
  candidate `L` proposed at round `r` is committed by what `V` holds. -/
  Commit : (U : BlockRecord Validator BlockId Payload P honest) → U.View → BlockId → ℕ → Prop
  /-- The direct commit is decidable: a validator computes it from its
  view, and so does a witness. -/
  decCommit : ∀ (U : BlockRecord Validator BlockId Payload P honest) (V : U.View) (L : BlockId)
    (r : ℕ), Decidable (Commit U V L r)
  /-- The direct skip of a slot, judged from a view. -/
  Skip : (U : BlockRecord Validator BlockId Payload P honest) → U.View → Slots Validator → ℕ → Prop
  /-- The number of rungs of the indirect test. -/
  rungs : ℕ
  /-- Rung `i`: `Link i U A L r` says the anchor `A` links the candidate `L`
  proposed at round `r`. -/
  Link : ℕ → (U : BlockRecord Validator BlockId Payload P honest) → BlockId → BlockId →
    Slots Validator → ℕ → Prop
  /-- The tie-break at rung `i`: `tie i L' L` says `L'` is preferred to `L`.
  Empty where the rung's link is unique per slot. -/
  tie : ℕ → BlockId → BlockId → Prop

namespace AnchoredRule

/-- The rule's own decidability of its direct commit, as an instance. -/
instance instDecidableCommit {R : AnchoredRule Validator BlockId Payload P honest}
    (U : BlockRecord Validator BlockId Payload P honest) (V : U.View) (L : BlockId) (r : ℕ) :
    Decidable (R.Commit U V L r) :=
  R.decCommit U V L r

variable (R : AnchoredRule Validator BlockId Payload P honest)
variable [S : Slots Validator]

/-! ## Eligibility -/

/-- The round at which a slot's direct verdict is settled. -/
def decisionRound (k : ℕ) : ℕ := S.slotRound k + R.wave

/-- **`j` may anchor `k`**: eligibility at the rule's wave. -/
abbrev Eligible (k j : ℕ) : Prop := EligibleAt (S := S) R.wave k j

theorem eligible_iff {k j : ℕ} :
    R.Eligible k j ↔ S.slotRound k + R.wave + 1 ≤ S.slotRound j :=
  eligibleAt_iff

/-- An eligible anchor is a later slot. -/
theorem lt_of_eligible {k j : ℕ} (h : R.Eligible k j) : k < j := lt_of_eligibleAt h

/-- Every slot has an eligible anchor somewhere. -/
theorem exists_eligible (k : ℕ) : ∃ j, R.Eligible k j := exists_eligibleAt R.wave k

/-- **A run of `c` slots reaches past everything below it**, at the
rule's wave. -/
abbrev SpansEligible (c : ℕ) : Prop := SpansEligibleAt (S := S) R.wave c

/-- Under an identity-round schedule, `wave + 1` consecutive slots span. -/
theorem spansEligible_of_identity (hid : ∀ s, S.slotRound s = s) :
    R.SpansEligible (R.wave + 1) := by
  intro b i hi
  rw [eligibleAt_iff, hid, hid]
  omega

variable {U : BlockRecord Validator BlockId Payload P honest}

/-- The anchor's round clears the slot's decision round. -/
theorem anchor_round_le {k j : ℕ} {A : BlockId} (hA : IsLeaderBlock U j A)
    (helig : R.Eligible k j) : S.slotRound k + R.wave + 1 ≤ (U.block A).round := by
  rw [hA.2.1]
  exact R.eligible_iff.mp helig

/-! ## The rungs -/

/-- No candidate of slot `k` is linked at rung `i` from the anchor `A`. -/
def RungEmpty (U : BlockRecord Validator BlockId Payload P honest) (A : BlockId) (i k : ℕ) :
    Prop :=
  ∀ L, IsLeaderBlock U k L → ¬ R.Link i U A L S k

/-- `L` is the tie-break's choice at rung `i`: no linked candidate of the
slot is preferred to it. -/
def Least (U : BlockRecord Validator BlockId Payload P honest) (A : BlockId) (i k : ℕ)
    (L : BlockId) : Prop :=
  ∀ L', IsLeaderBlock U k L' → R.Link i U A L' S k → ¬ R.tie i L' L

/-! ## The relation -/

/-- **`Decided U V k v`** — a validator holding the view `V` has settled
slot `k`, committing `v = some L` or skipping it, `v = none`. Undecided is
the absence of a derivation. -/
inductive Decided (U : BlockRecord Validator BlockId Payload P honest) (V : U.View) :
    ℕ → Option BlockId → Prop
  /-- The direct rule commits a candidate outright. -/
  | directCommit {k : ℕ} {L : BlockId} :
      IsLeaderBlock U k L → R.Commit U V L (S.slotRound k) →
      Decided U V k (some L)
  /-- The direct rule skips the slot. -/
  | directSkip {k : ℕ} :
      R.Skip U V S k → Decided U V k none
  /-- Anchored on the nearest eligible committed slot, every rung below
  `i` is empty, and `L` is the tie-break's choice among the candidates
  linked at rung `i`. -/
  | indirectCommit {k j : ℕ} {A L : BlockId} {i : ℕ} :
      k < j → R.Eligible k j → Decided U V j (some A) →
      (∀ m, k < m → m < j → R.Eligible k m → Decided U V m none) →
      i < R.rungs → (∀ i', i' < i → R.RungEmpty U A i' k) →
      IsLeaderBlock U k L → R.Link i U A L S k → R.Least U A i k L →
      Decided U V k (some L)
  /-- Anchored on the nearest eligible committed slot, every rung is
  empty. -/
  | indirectSkip {k j : ℕ} {A : BlockId} :
      k < j → R.Eligible k j → Decided U V j (some A) →
      (∀ m, k < m → m < j → R.Eligible k m → Decided U V m none) →
      (∀ i, i < R.rungs → R.RungEmpty U A i k) →
      Decided U V k none

variable {R} in
/-- **The indirect commit at a single rung with no tie**: the shape the
core, Nemo and Mahi-Mahi take. -/
theorem Decided.indirectCommit_single {U : BlockRecord Validator BlockId Payload P honest}
    {V : U.View} (h1 : R.rungs = 1) (hno : ∀ L L', ¬ R.tie 0 L L') {k j : ℕ} {A L : BlockId}
    (hkj : k < j) (helig : R.Eligible k j) (hj : R.Decided U V j (some A))
    (hmid : ∀ m, k < m → m < j → R.Eligible k m → R.Decided U V m none)
    (hL : IsLeaderBlock U k L) (hlink : R.Link 0 U A L S k) :
    R.Decided U V k (some L) :=
  Decided.indirectCommit (i := 0) hkj helig hj hmid (by omega)
    (fun i' hi' => absurd hi' (Nat.not_lt_zero _)) hL hlink (fun L' _ _ h => hno L' L h)

variable {R} in
/-- **The indirect skip at a single rung.** -/
theorem Decided.indirectSkip_single {U : BlockRecord Validator BlockId Payload P honest}
    {V : U.View} (h1 : R.rungs = 1) {k j : ℕ} {A : BlockId}
    (hkj : k < j) (helig : R.Eligible k j) (hj : R.Decided U V j (some A))
    (hmid : ∀ m, k < m → m < j → R.Eligible k m → R.Decided U V m none)
    (hnone : ∀ L, IsLeaderBlock U k L → ¬ R.Link 0 U A L S k) :
    R.Decided U V k none :=
  Decided.indirectSkip hkj helig hj hmid (fun i hi L hL => by
    have : i = 0 := by omega
    subst this; exact hnone L hL)

/-- **The indirect rule is total**: a nearest eligible committed anchor
gives the slot a verdict. -/
def Total (U : BlockRecord Validator BlockId Payload P honest) : Prop :=
  ∀ (V : U.View) (k j : ℕ) (A : BlockId), R.Eligible (S := S) k j →
    R.Decided (S := S) U V j (some A) →
    (∀ i, k < i → i < j → R.Eligible (S := S) k i → R.Decided (S := S) U V i none) →
    ∃ v, R.Decided (S := S) U V k v

/-- **A committed run decides everything below it**: `c` committed slots
from `b`, spanning eligibility, give every slot below `b` a verdict. -/
def DecidedBelowRun (U : BlockRecord Validator BlockId Payload P honest) : Prop :=
  ∀ (V : U.View) (b c : ℕ), 0 < c → R.SpansEligible (S := S) c →
    (∀ j, b ≤ j → j ≤ b + c - 1 → ∃ B, R.Decided (S := S) U V j (some B)) →
    ∀ i, i < b → ∃ v, R.Decided (S := S) U V i v

/-! ## What a rule owes -/

omit S in
/-- **A rung's link reads the schedule only at its own slot.** -/
abbrev LinkCongr : Prop :=
  ∀ {S₁ S₂ : Slots Validator} {U : BlockRecord Validator BlockId Payload P honest}
    {A L : BlockId} {i k : ℕ}, S₁.slotRound k = S₂.slotRound k → S₁.leader k = S₂.leader k →
    R.Link i U A L S₁ k → R.Link i U A L S₂ k

omit S in
/-- A link that reads the schedule only through the slot's round is
congruent. -/
theorem linkCongr_of_round
    (f : ℕ → (U : BlockRecord Validator BlockId Payload P honest) → BlockId → BlockId → ℕ → Prop)
    (h : ∀ i U A L (S : Slots Validator) k, R.Link i U A L S k = f i U A L (S.slotRound k)) :
    R.LinkCongr := by
  intro S₁ S₂ U A L i k hround _ hl
  rw [h] at hl ⊢
  rwa [← hround]

/-- **The laws of an anchored rule** — what the direct predicates and the
rungs must satisfy for agreement, on the records satisfying an invariant
`I` (every record, by default). Every rule proves each of them under
its own name. -/
structure Laws (I : Slots Validator → BlockRecord Validator BlockId Payload P honest → Prop :=
    fun _ _ => True) : Prop where
  /-- Two direct commits at one slot, from any two views, name one block. -/
  commit_unique : ∀ {S : Slots Validator} {U : BlockRecord Validator BlockId Payload P honest}
    {V₁ V₂ : U.View} {k : ℕ} {L₁ L₂ : BlockId},
    I S U → IsLeaderBlock U k L₁ → IsLeaderBlock U k L₂ →
    R.Commit U V₁ L₁ (S.slotRound k) → R.Commit U V₂ L₂ (S.slotRound k) → L₁ = L₂
  /-- A direct commit and a direct skip of one slot cannot both hold. -/
  commit_skip : ∀ {S : Slots Validator} {U : BlockRecord Validator BlockId Payload P honest}
    {V₁ V₂ : U.View} {k : ℕ} {L : BlockId},
    I S U → IsLeaderBlock U k L → R.Commit U V₁ L (S.slotRound k) → R.Skip U V₂ S k → False
  /-- **Visibility.** A direct commit is linked, at some rung, from any
  candidate anchor of any eligible slot. -/
  commit_link : ∀ {S : Slots Validator} {U : BlockRecord Validator BlockId Payload P honest}
    {V : U.View} {k j : ℕ} {L A : BlockId},
    I S U → IsLeaderBlock U k L → R.Commit U V L (S.slotRound k) →
    IsLeaderBlock U j A → R.Eligible k j →
    ∃ i, i < R.rungs ∧ R.Link i U A L S k
  /-- A direct commit and the tie-break's choice at any rung, from any
  candidate anchor of any eligible slot, are one block. -/
  commit_link_unique : ∀ {S : Slots Validator}
    {U : BlockRecord Validator BlockId Payload P honest}
    {V : U.View} {k j i : ℕ} {L₁ L₂ A : BlockId},
    I S U → IsLeaderBlock U k L₁ → IsLeaderBlock U k L₂ → R.Commit U V L₁ (S.slotRound k) →
    IsLeaderBlock U j A → R.Eligible k j → i < R.rungs →
    (∀ i', i' < i → R.RungEmpty U A i' k) →
    R.Link i U A L₂ S k → R.Least U A i k L₂ → L₁ = L₂
  /-- A direct skip excludes every link for the slot's candidates. -/
  skip_link : ∀ {S : Slots Validator} {U : BlockRecord Validator BlockId Payload P honest}
    {V : U.View} {k i : ℕ} {L A : BlockId},
    I S U → R.Skip U V S k → IsLeaderBlock U k L → i < R.rungs → ¬ R.Link i U A L S k
  /-- Two tie-break choices at one rung, from one anchor, are one block. -/
  link_unique : ∀ {S : Slots Validator} {U : BlockRecord Validator BlockId Payload P honest}
    {k j i : ℕ} {L₁ L₂ A : BlockId},
    I S U → IsLeaderBlock U k L₁ → IsLeaderBlock U k L₂ → IsLeaderBlock U j A → R.Eligible k j →
    i < R.rungs → (∀ i', i' < i → R.RungEmpty U A i' k) →
    R.Link i U A L₁ S k → R.Link i U A L₂ S k →
    R.Least U A i k L₁ → R.Least U A i k L₂ → L₁ = L₂
  /-- A larger view can only see more of a direct commit. -/
  commit_mono : ∀ {S : Slots Validator} {U : BlockRecord Validator BlockId Payload P honest}
    {V V' : U.View} {L : BlockId} {r : ℕ},
    I S U → V.ids ⊆ V'.ids → R.Commit U V L r → R.Commit U V' L r
  /-- And of a direct skip. -/
  skip_mono : ∀ {S : Slots Validator} {U : BlockRecord Validator BlockId Payload P honest}
    {V V' : U.View} {k : ℕ}, I S U → V.ids ⊆ V'.ids → R.Skip U V S k → R.Skip U V' S k
  /-- The direct skip reads the schedule only at its own slot. -/
  skip_congr : ∀ {S₁ S₂ : Slots Validator} {U : BlockRecord Validator BlockId Payload P honest}
    {V : U.View} {k : ℕ}, I S₁ U → S₁.slotRound k = S₂.slotRound k → S₁.leader k = S₂.leader k →
    R.Skip U V S₁ k → R.Skip U V S₂ k
  /-- And so does every rung's link. -/
  link_congr : R.LinkCongr

variable {R} {I : Slots Validator → BlockRecord Validator BlockId Payload P honest → Prop}

/-! ## Agreement -/

/-- Whatever route it took, a committed verdict names a genuine candidate
for that slot. -/
theorem isLeaderBlock_of_decided {V : U.View} {j : ℕ} {A : BlockId}
    (h : R.Decided U V j (some A)) : IsLeaderBlock U j A := by
  cases h with
  | directCommit hL _ => exact hL
  | indirectCommit _ _ _ _ _ _ hL _ _ => exact hL

/-- **A committed block belongs to one slot.** The ledger reads verdicts off
in slot order, so without this a single block could be delivered twice. -/
theorem slot_eq_of_decided_commit {V₁ V₂ : U.View} {k₁ k₂ : ℕ} {L : BlockId}
    (h₁ : R.Decided U V₁ k₁ (some L)) (h₂ : R.Decided U V₂ k₂ (some L)) : k₁ = k₂ :=
  slot_eq_of_isLeaderBlock (isLeaderBlock_of_decided h₁) (isLeaderBlock_of_decided h₂)

/-- **The anchor comparison.** Two indirect decisions for one slot each
name an anchor, together with the premise that every eligible slot
strictly between the slot and that anchor was decided `none`. Whichever
anchor is the earlier is then decided `none` by the other side and `some`
by its own, so the anchors coincide — and with them the blocks they name.
The statement carries no consensus content: `Dec` and `Elig` are arbitrary
predicates. -/
theorem anchor_eq {W : Type*} {Dec : W → ℕ → Option BlockId → Prop}
    {Elig : ℕ → Prop} {k j j₂ : ℕ} {A A₂ : BlockId} {V₂ : W}
    (hkj : k < j) (helig : Elig j) (hkj₂ : k < j₂) (helig₂ : Elig j₂)
    (hj₂ : Dec V₂ j₂ (some A₂))
    (hmid₂ : ∀ i, k < i → i < j₂ → Elig i → Dec V₂ i none)
    (ihj : ∀ V v, Dec V j v → some A = v)
    (ihmid : ∀ i, k < i → i < j → Elig i → ∀ V v, Dec V i v → none = v) :
    j = j₂ ∧ A = A₂ := by
  rcases lt_trichotomy j j₂ with hlt | heq | hgt
  · exact absurd (ihj V₂ none (hmid₂ j hkj hlt helig)) (by simp)
  · subst heq
    exact ⟨rfl, Option.some.inj (ihj V₂ (some A₂) hj₂)⟩
  · exact absurd (ihmid j₂ hkj₂ hgt helig₂ V₂ (some A₂) hj₂) (by simp)

/-- Two tie-break choices at two rungs from one anchor are one block: at
one rung by `link_unique`, and at different rungs the higher rung's
emptiness premise contradicts the lower rung's link. -/
theorem eq_of_indirect (hl : R.Laws I) (hI : I S U) {k j i₁ i₂ : ℕ} {L₁ L₂ A : BlockId}
    (hL₁ : IsLeaderBlock U k L₁) (hL₂ : IsLeaderBlock U k L₂)
    (hA : IsLeaderBlock U j A) (helig : R.Eligible k j)
    (hi₁ : i₁ < R.rungs) (hemp₁ : ∀ i', i' < i₁ → R.RungEmpty U A i' k)
    (hlink₁ : R.Link i₁ U A L₁ S k) (hmin₁ : R.Least U A i₁ k L₁)
    (hi₂ : i₂ < R.rungs) (hemp₂ : ∀ i', i' < i₂ → R.RungEmpty U A i' k)
    (hlink₂ : R.Link i₂ U A L₂ S k) (hmin₂ : R.Least U A i₂ k L₂) :
    L₁ = L₂ := by
  rcases lt_trichotomy i₁ i₂ with hlt | rfl | hgt
  · exact absurd hlink₁ (hemp₂ i₁ hlt L₁ hL₁)
  · exact hl.link_unique hI hL₁ hL₂ hA helig hi₁ hemp₁ hlink₁ hlink₂ hmin₁ hmin₂
  · exact absurd hlink₂ (hemp₁ i₂ hgt L₂ hL₂)

/-- **Agreement.** No two validators reach conflicting decisions for a
slot, whatever views they hold and whichever routes they took. Structural
induction on the first derivation: every commit-against-commit case
closes by a uniqueness law, the direct-against-indirect crossings by
visibility or by the skip law, and the one real case — indirect against
indirect — by comparing the two anchors. -/
theorem decided_unique (hl : R.Laws I) (hI : I S U) {V₁ : U.View} {k : ℕ} {v₁ : Option BlockId}
    (h₁ : R.Decided U V₁ k v₁) :
    ∀ (V₂ : U.View) (v₂ : Option BlockId), R.Decided U V₂ k v₂ → v₁ = v₂ := by
  induction h₁ with
  | @directCommit k L hL h =>
    intro V₂ v₂ h₂
    cases h₂ with
    | directCommit hL₂ h₂ => exact congrArg some (hl.commit_unique hI hL hL₂ h h₂)
    | directSkip hskip => exact absurd (hl.commit_skip hI hL h hskip) not_false
    | @indirectCommit _ j A L₂ i _ helig hj _ hi hemp hL₂ hlink hmin =>
      exact congrArg some (hl.commit_link_unique hI hL hL₂ h (isLeaderBlock_of_decided hj) helig
        hi hemp hlink hmin)
    | @indirectSkip _ j A _ helig hj _ hnone =>
      obtain ⟨i, hi, hlink⟩ := hl.commit_link hI hL h (isLeaderBlock_of_decided hj) helig
      exact absurd hlink (hnone i hi L hL)
  | @directSkip k hskip =>
    intro V₂ v₂ h₂
    cases h₂ with
    | directCommit hL₂ h₂ => exact absurd (hl.commit_skip hI hL₂ h₂ hskip) not_false
    | directSkip _ => rfl
    | indirectCommit _ _ _ _ hi _ hL₂ hlink _ => exact absurd hlink (hl.skip_link hI hskip hL₂ hi)
    | indirectSkip _ _ _ _ _ => rfl
  | @indirectCommit k j A L i hkj helig hj hmid hi hemp hL hlink hmin ihj ihmid =>
    intro V₂ v₂ h₂
    cases h₂ with
    | directCommit hL₂ h₂ =>
      exact congrArg some (hl.commit_link_unique hI hL₂ hL h₂ (isLeaderBlock_of_decided hj) helig
        hi hemp hlink hmin).symm
    | directSkip hskip₂ => exact absurd hlink (hl.skip_link hI hskip₂ hL hi)
    | @indirectCommit _ j₂ A₂ L₂ i₂ hkj₂ helig₂ hj₂ hmid₂ hi₂ hemp₂ hL₂ hlink₂ hmin₂ =>
      obtain ⟨rfl, rfl⟩ := anchor_eq hkj helig hkj₂ helig₂ hj₂ hmid₂ ihj ihmid
      exact congrArg some (eq_of_indirect hl hI hL hL₂ (isLeaderBlock_of_decided hj) helig
        hi hemp hlink hmin hi₂ hemp₂ hlink₂ hmin₂)
    | @indirectSkip _ j₂ A₂ hkj₂ helig₂ hj₂ hmid₂ hnone₂ =>
      obtain ⟨rfl, rfl⟩ := anchor_eq hkj helig hkj₂ helig₂ hj₂ hmid₂ ihj ihmid
      exact absurd hlink (hnone₂ i hi L hL)
  | @indirectSkip k j A hkj helig hj hmid hnone ihj ihmid =>
    intro V₂ v₂ h₂
    cases h₂ with
    | directCommit hL₂ h₂ =>
      obtain ⟨i, hi, hlink⟩ := hl.commit_link hI hL₂ h₂ (isLeaderBlock_of_decided hj) helig
      exact absurd hlink (hnone i hi _ hL₂)
    | directSkip _ => rfl
    | @indirectCommit _ j₂ A₂ L₂ i₂ hkj₂ helig₂ hj₂ hmid₂ hi₂ _ hL₂ hlink₂ _ =>
      obtain ⟨rfl, rfl⟩ := anchor_eq hkj helig hkj₂ helig₂ hj₂ hmid₂ ihj ihmid
      exact absurd hlink₂ (hnone i₂ hi₂ _ hL₂)
    | indirectSkip _ _ _ _ _ => rfl

/-- Agreement, in the shape callers want. -/
theorem decided_agree (hl : R.Laws I) (hI : I S U) {V₁ V₂ : U.View} {k : ℕ} {v₁ v₂ : Option BlockId}
    (h₁ : R.Decided U V₁ k v₁) (h₂ : R.Decided U V₂ k v₂) : v₁ = v₂ :=
  decided_unique hl hI h₁ V₂ v₂ h₂

/-- No two validators commit *different* blocks for one slot. -/
theorem eq_of_decided_commit (hl : R.Laws I) (hI : I S U) {V₁ V₂ : U.View} {k : ℕ} {L₁ L₂ : BlockId}
    (h₁ : R.Decided U V₁ k (some L₁)) (h₂ : R.Decided U V₂ k (some L₂)) : L₁ = L₂ :=
  Option.some.inj (decided_agree hl hI h₁ h₂)

/-- No validator commits a slot another has skipped. -/
theorem not_decided_skip_of_decided_commit (hl : R.Laws I) (hI : I S U)
    {V₁ V₂ : U.View} {k : ℕ}
    {L : BlockId} (h₁ : R.Decided U V₁ k (some L)) (h₂ : R.Decided U V₂ k none) : False := by
  simpa using decided_agree hl hI h₁ h₂

/-! ## Monotonicity in the view -/

/-- **Decisions are monotone in the view.** The direct cases are the
monotonicity laws; the indirect cases rebuild themselves from the
inductive hypotheses, their link premises unchanged. -/
theorem decided_mono (hl : R.Laws I) (hI : I S U) {V V' : U.View} (hsub : V.ids ⊆ V'.ids) {k : ℕ}
    {v : Option BlockId} (h : R.Decided U V k v) : R.Decided U V' k v := by
  induction h with
  | directCommit hL hdc => exact Decided.directCommit hL (hl.commit_mono hI hsub hdc)
  | directSkip hall => exact Decided.directSkip (hl.skip_mono hI hsub hall)
  | indirectCommit hkj helig _ _ hi hemp hL hlink hmin ihj ihmid =>
      exact Decided.indirectCommit hkj helig ihj ihmid hi hemp hL hlink hmin
  | indirectSkip hkj helig _ _ hnone ihj ihmid =>
      exact Decided.indirectSkip hkj helig ihj ihmid hnone

/-- Whatever any validator decides on any view, the same verdict holds on
the full view. -/
theorem decided_full (hl : R.Laws I) (hI : I S U) {V : U.View} {k : ℕ} {v : Option BlockId}
    (h : R.Decided U V k v) : R.Decided U (BlockRecord.View.full U) k v :=
  decided_mono hl hI V.subset_ids h

/-! ## The ledger -/

/-- **The committed-leader sequence is agreed.** -/
theorem commitSeq_agree (hl : R.Laws I) (hI : I S U) {V₁ V₂ : U.View} {n : ℕ} {g₁ g₂ : ℕ → Option BlockId}
    (h₁ : ∀ k, k < n → R.Decided U V₁ k (g₁ k))
    (h₂ : ∀ k, k < n → R.Decided U V₂ k (g₂ k)) :
    commitSeq g₁ n = commitSeq g₂ n :=
  commitSeq_agree_of fun k hk => decided_agree hl hI (h₁ k hk) (h₂ k hk)

/-- **Two validators output the same blocks.** -/
theorem ledgerSet_agree (hl : R.Laws I) (hI : I S U) {V₁ V₂ : U.View} {n : ℕ} {g₁ g₂ : ℕ → Option BlockId}
    (h₁ : ∀ k, k < n → R.Decided U V₁ k (g₁ k))
    (h₂ : ∀ k, k < n → R.Decided U V₂ k (g₂ k)) :
    ledgerSet U g₁ n = ledgerSet U g₂ n :=
  ledgerSet_agree_of fun k hk => decided_agree hl hI (h₁ k hk) (h₂ k hk)

/-- **And validators agree on which slot a block enters at.** -/
theorem outputAt_agree (hl : R.Laws I) (hI : I S U) {V₁ V₂ : U.View} {n : ℕ} {g₁ g₂ : ℕ → Option BlockId}
    {b : BlockId} {k : ℕ}
    (h₁ : ∀ j, j < n → R.Decided U V₁ j (g₁ j))
    (h₂ : ∀ j, j < n → R.Decided U V₂ j (g₂ j))
    (hk : k < n) (ho : OutputAt U g₁ b k) : OutputAt U g₂ b k :=
  outputAt_agree_of (fun j hj => decided_agree hl hI (h₁ j hj) (h₂ j hj)) hk ho

end AnchoredRule

end LeanDag
