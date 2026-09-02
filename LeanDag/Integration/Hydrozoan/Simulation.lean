import LeanDag.Integration.Hydrozoan.ChopDecided
import LeanDag.Integration.Hydrozoan.FillDecided

/-!
# The transformer interface

`docs/hydrozoan-integration.md` §9's deferred item. P7 and P8 each
carried Hydrozoan's decision relation across a universe transformer,
three times in all, and each time by the same six-constructor induction
over a family of predicate-level agreements — differing only in which
transformer's arithmetic the agreements threaded. This file states the
agreements once and does the induction once.

**The content is that the rule reads the universe only through a fixed
list.** `Decided` inspects a universe through candidacy, anchor
eligibility, the three direct rules in view, and the two rung tests, and
through nothing else. So a map between universes that preserves those
preserves verdicts, whatever it did to the blocks. `Simulates` is that
list, and `Simulates.decided` is the induction.

**Slots correspond by a relation, not a function.** `R n k` says slot
`n` of the source is slot `k` of the target. A relation is what the
three directions need in common: the cut forwards relates `d + k` to
`k`, and the cut backwards relates `n` to `d + n` — the same
correspondence read the other way, which a relation permits and a
function does not. Three fields govern it: `ord` makes it respect the
order both ways, `lift` finds the target slot for an anchor of the
source, and `drop` finds a source slot for an intermediate slot of the
target. Nothing else about the numbering is used.

**One parameter separates the two kinds of transformer.** A cut removes
blocks, so every candidate of the truncation is a candidate of the
original; a fill adds them, so the extension has candidates the original
lacks. `Novel` names those, and the two `novel_*` fields say what the
graded rungs need of them — that neither rung reaches a new candidate.
For a cut `Novel` is empty and those fields are vacuous; for a fill it
is "fresh", and they are `not_certifiedInHZ_fresh` and its `WeakLinked`
counterpart.

All three transport directions are instances, and none carries an
induction of its own: `decided_chopHZ_of_decided`,
`decided_of_decided_chopHZ` and `decided_fillHZ` are recovered as
corollaries below. The bespoke proofs in `ChopDecided.lean` and
`FillDecided.lean` are retained because `Stack.lean` and `Liveness.lean`
consume them, and `docs/integration.md` §4.2's rule is to generalise
with the old statements kept as corollaries rather than to rewrite
working code.

`docs/transformer-interface.md` records what generalising this beyond
Hydrozoan would take.
-/

namespace LeanDag

namespace Integration

namespace Hydrozoan

variable {Replica : Type} [Fintype Replica] [DecidableEq Replica]
variable {BlockId : Type} [DecidableEq BlockId] [LinearOrder BlockId]
variable [LeanDag.Hydrozoan.Faults Replica]

/-- **`U'` simulates `U` along the slot correspondence `R`.** Every
field is one of the predicates `Decided` inspects, and there are no
others: that is the claim the structure makes and the induction below
consumes.

`R n k` reads "slot `n` of the source is slot `k` of the target".
`Novel` names the identifiers the target has and the source does not.
The rung fields are stated for anchors of the source, which is where
every anchor of a derivation over the source lives. -/
structure Simulates
    (U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId)
    (V : LeanDag.Hydrozoan.View U) (S : LeanDag.Hydrozoan.Slots Replica)
    (U' : LeanDag.Hydrozoan.BlockUniverse Replica BlockId)
    (V' : LeanDag.Hydrozoan.View U') (S' : LeanDag.Hydrozoan.Slots Replica)
    (R : ℕ → ℕ → Prop) (Novel : BlockId → Prop) : Prop where
  /-- An anchor above a corresponding slot has a corresponding slot of
  its own, above it. -/
  lift : ∀ n k m, R n k → n < m → ∃ j, R m j ∧ k < j
  /-- The correspondence respects the order, in both directions. -/
  ord : ∀ n k m j, R n k → R m j → (n < m ↔ k < j)
  /-- And a target slot above a corresponding one comes from a source
  slot — what the intermediate slots of an indirect derivation need. -/
  drop : ∀ n k j, R n k → k < j → ∃ m, R m j ∧ n < m
  /-- A candidate of the source is a candidate of the target. -/
  leader_fwd : ∀ n k L, R n k → @LeanDag.Hydrozoan.IsLeaderBlock _ _ _ _ _ S U n L →
    @LeanDag.Hydrozoan.IsLeaderBlock _ _ _ _ _ S' U' k L
  /-- And a candidate of the target is one of the source, or novel. -/
  leader_bwd : ∀ n k L, R n k → @LeanDag.Hydrozoan.IsLeaderBlock _ _ _ _ _ S' U' k L →
    @LeanDag.Hydrozoan.IsLeaderBlock _ _ _ _ _ S U n L ∨ Novel L
  /-- Anchor eligibility agrees, both slots moving together. -/
  elig : ∀ n k m j, R n k → R m j →
    (@LeanDag.Hydrozoan.EligibleAsAnchor Replica S n m ↔
      @LeanDag.Hydrozoan.EligibleAsAnchor Replica S' k j)
  /-- The three direct rules carry forward. -/
  fast : ∀ n k L, R n k → LeanDag.Hydrozoan.FastCommitInView U V L (S.slotRound n) →
    LeanDag.Hydrozoan.FastCommitInView U' V' L (S'.slotRound k)
  slow : ∀ n k L, R n k → LeanDag.Hydrozoan.SlowCommitInView U V L (S.slotRound n) →
    LeanDag.Hydrozoan.SlowCommitInView U' V' L (S'.slotRound k)
  skip : ∀ n k, R n k → @LeanDag.Hydrozoan.SkippedLeaderInView _ _ _ _ _ _ S U V n →
    @LeanDag.Hydrozoan.SkippedLeaderInView _ _ _ _ _ _ S' U' V' k
  /-- The two rung tests agree at an anchor of the source. -/
  cert : ∀ n k A L, R n k → A ∈ U.ids →
    (LeanDag.Hydrozoan.CertifiedIn U' A L (S'.slotRound k) ↔
      LeanDag.Hydrozoan.CertifiedIn U A L (S.slotRound n))
  weak : ∀ n k A L, R n k → A ∈ U.ids →
    (LeanDag.Hydrozoan.WeakLinked U' A L (S'.slotRound k) ↔
      LeanDag.Hydrozoan.WeakLinked U A L (S.slotRound n))
  /-- Neither rung reaches a novel candidate. Vacuous when nothing is
  novel, which is the case for a cut. -/
  novel_cert : ∀ n k A L, R n k → A ∈ U.ids → Novel L →
    ¬ LeanDag.Hydrozoan.CertifiedIn U' A L (S'.slotRound k)
  novel_weak : ∀ n k A L, R n k → A ∈ U.ids → Novel L →
    ¬ LeanDag.Hydrozoan.WeakLinked U' A L (S'.slotRound k)

namespace Simulates

variable {U U' : LeanDag.Hydrozoan.BlockUniverse Replica BlockId}
  {V : LeanDag.Hydrozoan.View U} {V' : LeanDag.Hydrozoan.View U'}
  {S S' : LeanDag.Hydrozoan.Slots Replica} {R : ℕ → ℕ → Prop} {Novel : BlockId → Prop}

/-- **Simulation transports verdicts.** The six-constructor induction,
once. Every case is a field of the structure applied; nothing about any
particular transformer appears. -/
theorem decided (h : Simulates U V S U' V' S' R Novel) {n : ℕ} {v : Option BlockId}
    (hd : @LeanDag.Hydrozoan.Decided _ _ _ _ _ _ _ S U V n v) :
    ∀ k, R n k → @LeanDag.Hydrozoan.Decided _ _ _ _ _ _ _ S' U' V' k v := by
  induction hd with
  | @directFast n L hL hc =>
      intro k hR
      exact LeanDag.Hydrozoan.Decided.directFast (S := S') (h.leader_fwd n k L hR hL)
        (h.fast n k L hR hc)
  | @directSlow n L hL hc =>
      intro k hR
      exact LeanDag.Hydrozoan.Decided.directSlow (S := S') (h.leader_fwd n k L hR hL)
        (h.slow n k L hR hc)
  | @directSkip n hskip =>
      intro k hR
      exact LeanDag.Hydrozoan.Decided.directSkip (S := S') (h.skip n k hR hskip)
  | @indirectCert n j A L hkj helig hanchor hmid hL hcert ihj ihmid =>
      intro k hR
      obtain ⟨j', hRj, hkj'⟩ := h.lift n k j hR hkj
      have hA : A ∈ U.ids := (isLeaderBlock_of_decidedHZ hanchor).1
      refine LeanDag.Hydrozoan.Decided.indirectCert (S := S') hkj'
        ((h.elig n k j j' hR hRj).mp helig) (ihj j' hRj) ?_ (h.leader_fwd n k L hR hL)
        ((h.cert n k A L hR hA).mpr hcert)
      intro i' h1 h2 he
      obtain ⟨m, hRm, hnm⟩ := h.drop n k i' hR h1
      exact ihmid m hnm ((h.ord m i' j j' hRm hRj).mpr h2)
        ((h.elig n k m i' hR hRm).mpr he) i' hRm
  | @indirectWeak n j A L hkj helig hanchor hmid hnocert hL hweak hmin ihj ihmid =>
      intro k hR
      obtain ⟨j', hRj, hkj'⟩ := h.lift n k j hR hkj
      have hA : A ∈ U.ids := (isLeaderBlock_of_decidedHZ hanchor).1
      refine LeanDag.Hydrozoan.Decided.indirectWeak (S := S') hkj'
        ((h.elig n k j j' hR hRj).mp helig) (ihj j' hRj) ?_ ?_ (h.leader_fwd n k L hR hL)
        ((h.weak n k A L hR hA).mpr hweak) ?_
      · intro i' h1 h2 he
        obtain ⟨m, hRm, hnm⟩ := h.drop n k i' hR h1
        exact ihmid m hnm ((h.ord m i' j j' hRm hRj).mpr h2)
          ((h.elig n k m i' hR hRm).mpr he) i' hRm
      · intro L' hL' hc
        rcases h.leader_bwd n k L' hR hL' with hold | hnov
        · exact hnocert L' hold ((h.cert n k A L' hR hA).mp hc)
        · exact h.novel_cert n k A L' hR hA hnov hc
      · intro L' hL' hw
        rcases h.leader_bwd n k L' hR hL' with hold | hnov
        · exact hmin L' hold ((h.weak n k A L' hR hA).mp hw)
        · exact absurd hw (h.novel_weak n k A L' hR hA hnov)
  | @indirectSkip n j A hkj helig hanchor hmid hnocert hnoweak ihj ihmid =>
      intro k hR
      obtain ⟨j', hRj, hkj'⟩ := h.lift n k j hR hkj
      have hA : A ∈ U.ids := (isLeaderBlock_of_decidedHZ hanchor).1
      refine LeanDag.Hydrozoan.Decided.indirectSkip (S := S') hkj'
        ((h.elig n k j j' hR hRj).mp helig) (ihj j' hRj) ?_ ?_ ?_
      · intro i' h1 h2 he
        obtain ⟨m, hRm, hnm⟩ := h.drop n k i' hR h1
        exact ihmid m hnm ((h.ord m i' j j' hRm hRj).mpr h2)
          ((h.elig n k m i' hR hRm).mpr he) i' hRm
      · intro L' hL' hc
        rcases h.leader_bwd n k L' hR hL' with hold | hnov
        · exact hnocert L' hold ((h.cert n k A L' hR hA).mp hc)
        · exact h.novel_cert n k A L' hR hA hnov hc
      · intro L' hL' hw
        rcases h.leader_bwd n k L' hR hL' with hold | hnov
        · exact hnoweak L' hold ((h.weak n k A L' hR hA).mp hw)
        · exact absurd hw (h.novel_weak n k A L' hR hA hnov)

/-! ## The three transport directions as simulations

Each is the structure's fields, assembled from the transfer lemmas P7
and P8 already prove. None carries an induction of its own. -/

section Instances

variable {U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId}
  {hsp : SelfParenting U} {V : LeanDag.Hydrozoan.View U}
variable [Fact (HybridCommittee Replica)]

omit [LinearOrder BlockId] in
/-- **The fill is a simulation** along the identity on slots, with the
fresh identifiers as the novel ones. -/
theorem simulates_fill (sk : SkipMsg (toCore U hsp)) (S : LeanDag.Hydrozoan.Slots Replica) :
    Simulates U V S (skipFillHZ U hsp sk) (liftViewHZ U hsp sk V) S (fun n k => n = k)
      (fun L => L ∉ U.ids) where
  lift := fun _ _ m _ _ => ⟨m, rfl, by omega⟩
  ord := fun _ _ _ _ h1 h2 => by subst h1; subst h2; rfl
  drop := fun _ _ j _ _ => ⟨j, rfl, by omega⟩
  leader_fwd := fun _ _ _ hR h => by subst hR; exact isLeaderBlockHZ_fill h
  leader_bwd := fun _ _ L hR h => by
    subst hR
    by_cases hL : L ∈ U.ids
    · exact Or.inl (isLeaderBlockHZ_fill_old hL h)
    · exact Or.inr hL
  elig := fun _ _ _ _ h1 h2 => by subst h1; subst h2; exact Iff.rfl
  fast := fun n _ L hR h => by
    subst hR; exact (fastCommitInView_fill (V := V) L (S.slotRound n)).mpr h
  slow := fun n _ L hR h => by
    subst hR; exact (slowCommitInView_fill (V := V) L (S.slotRound n)).mpr h
  skip := fun n _ hR h => by subst hR; exact (skippedLeaderInView_fill (V := V) n).mpr h
  cert := fun _ _ _ _ hR hA => by subst hR; exact certifiedInHZ_fill hA
  weak := fun _ _ _ _ hR hA => by subst hR; exact weakLinkedHZ_fill hA
  novel_cert := fun _ _ _ _ hR hA hL => by subst hR; exact not_certifiedInHZ_fresh hA hL
  novel_weak := fun _ _ _ _ hR hA hL => by subst hR; exact not_weakLinkedHZ_fresh hA hL

/-- **Verdicts survive the fill**, now as a corollary. -/
theorem decided_fill_of_simulates [S : LeanDag.Hydrozoan.Slots Replica]
    (sk : SkipMsg (toCore U hsp)) {k : ℕ} {v : Option BlockId}
    (h : LeanDag.Hydrozoan.Decided U V k v) :
    LeanDag.Hydrozoan.Decided (skipFillHZ U hsp sk) (liftViewHZ U hsp sk V) k v :=
  (simulates_fill sk S).decided h k rfl

omit [LinearOrder BlockId] in
/-- **The cut is a simulation** along `d + k ↦ k`, with nothing novel: a
truncation adds no identifier. -/
theorem simulates_chop [S : LeanDag.Hydrozoan.Slots Replica] {d G : ℕ}
    (hd : G ≤ S.slotRound d) :
    Simulates U V S (chopHZ U hsp G) (View.chopHZ V hsp G) (slotsChopHZ hd)
      (fun n k => n = d + k) (fun _ => False) where
  lift := fun _ _ m _ hm => ⟨m - d, by omega, by omega⟩
  ord := fun _ _ _ _ h1 h2 => by subst h1; subst h2; omega
  drop := fun _ _ j _ hj => ⟨d + j, rfl, by omega⟩
  leader_fwd := fun _ _ _ hR h => by subst hR; exact (isLeaderBlockHZ_chop hd).mpr h
  leader_bwd := fun _ _ _ hR h => by subst hR; exact Or.inl ((isLeaderBlockHZ_chop hd).mp h)
  elig := fun _ _ _ _ h1 h2 => by subst h1; subst h2; exact (eligibleAsAnchorHZ_chop hd).symm
  fast := fun _ k L hR h => by
    subst hR
    refine (fastCommitInView_chopHZ (V := V) L ((slotsChopHZ hd).slotRound k)).mpr ?_
    rwa [chopRound_add hd k]
  slow := fun _ k L hR h => by
    subst hR
    refine (slowCommitInView_chopHZ (V := V) L ((slotsChopHZ hd).slotRound k)).mpr ?_
    rwa [chopRound_add hd k]
  skip := fun _ k hR h => by subst hR; exact (skippedLeaderInView_chopHZ (V := V) hd k).mpr h
  cert := fun _ k _ _ hR hA => by subst hR; exact certifiedIn_chopHZ hd hA k
  weak := fun _ k _ _ hR hA => by subst hR; exact weakLinked_chopHZ hd hA k
  novel_cert := fun _ _ _ _ _ _ hL => absurd hL not_false
  novel_weak := fun _ _ _ _ _ _ hL => absurd hL not_false

/-- **Verdicts survive the cut**, now as a corollary. -/
theorem decided_chop_of_simulates [S : LeanDag.Hydrozoan.Slots Replica] {d G : ℕ}
    (hd : G ≤ S.slotRound d) {k : ℕ} {v : Option BlockId}
    (h : LeanDag.Hydrozoan.Decided U V (d + k) v) :
    LeanDag.Hydrozoan.Decided (S := slotsChopHZ hd) (chopHZ U hsp G)
      (View.chopHZ V hsp G) k v :=
  (simulates_chop hd).decided h k rfl

omit [LinearOrder BlockId] in
/-- **And the cut read backwards is a simulation too** — the same
correspondence, `n ↦ d + n`, taken from the truncation to the universe
it came from. This is the direction a function-valued slot map could not
state, `k ↦ k - d` being partial. -/
theorem simulates_chop_bwd [S : LeanDag.Hydrozoan.Slots Replica] {d G : ℕ}
    (hd : G ≤ S.slotRound d) :
    Simulates (chopHZ U hsp G) (View.chopHZ V hsp G) (slotsChopHZ hd) U V S
      (fun n k => k = d + n) (fun _ => False) where
  lift := fun _ _ m _ hm => ⟨d + m, rfl, by omega⟩
  ord := fun _ _ _ _ h1 h2 => by subst h1; subst h2; omega
  drop := fun _ _ j _ hj => ⟨j - d, by omega, by omega⟩
  leader_fwd := fun _ _ _ hR h => by subst hR; exact (isLeaderBlockHZ_chop hd).mp h
  leader_bwd := fun _ _ _ hR h => by subst hR; exact Or.inl ((isLeaderBlockHZ_chop hd).mpr h)
  elig := fun _ _ _ _ h1 h2 => by subst h1; subst h2; exact eligibleAsAnchorHZ_chop hd
  fast := fun n _ L hR h => by
    subst hR
    have h2 := (fastCommitInView_chopHZ (V := V) L ((slotsChopHZ hd).slotRound n)).mp h
    rwa [chopRound_add hd n] at h2
  slow := fun n _ L hR h => by
    subst hR
    have h2 := (slowCommitInView_chopHZ (V := V) L ((slotsChopHZ hd).slotRound n)).mp h
    rwa [chopRound_add hd n] at h2
  skip := fun n _ hR h => by subst hR; exact (skippedLeaderInView_chopHZ (V := V) hd n).mp h
  cert := fun n _ _ _ hR hA => by
    subst hR; exact (certifiedIn_chopHZ hd (mem_chopHZ_ids.mp hA).1 n).symm
  weak := fun n _ _ _ hR hA => by
    subst hR; exact (weakLinked_chopHZ hd (mem_chopHZ_ids.mp hA).1 n).symm
  novel_cert := fun _ _ _ _ _ _ hL => absurd hL not_false
  novel_weak := fun _ _ _ _ _ _ hL => absurd hL not_false

/-- **A verdict of the truncation is a verdict of the universe it came
from**, now as a corollary. -/
theorem decided_of_decided_chop_of_simulates [S : LeanDag.Hydrozoan.Slots Replica] {d G : ℕ}
    (hd : G ≤ S.slotRound d) {k : ℕ} {v : Option BlockId}
    (h : LeanDag.Hydrozoan.Decided (S := slotsChopHZ hd) (chopHZ U hsp G)
      (View.chopHZ V hsp G) k v) :
    LeanDag.Hydrozoan.Decided U V (d + k) v :=
  (simulates_chop_bwd hd).decided h (d + k) rfl

end Instances

end Simulates

end Hydrozoan

end Integration

end LeanDag
