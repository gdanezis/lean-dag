import LeanDag.Integration.Hydrozoan.ChopDecided
import LeanDag.Integration.Hydrozoan.FillDecided

/-!
# The transformer interface

`docs/hydrozoan-integration.md` §9's deferred item, built. P7 and P8
each carried Hydrozoan's decision relation across a universe
transformer, and each did it by the same six-constructor induction over
a family of predicate-level agreements — differing only in which
transformer's arithmetic the agreements threaded. This file states the
agreements once and does the induction once.

**The content is that the rule reads the universe only through a fixed
list.** `Decided` inspects a universe through candidacy, anchor
eligibility, the three direct rules in view, and the two rung tests,
and through nothing else. So a map between universes that preserves
those preserves verdicts, whatever it did to the blocks. `Simulates`
is that list, and `decided_of_simulates` is the induction.

**One parameter separates the two transformers.** A cut removes blocks,
so every candidate of the truncation is a candidate of the original; a
fill adds them, so the extension has candidates the original lacks.
`Novel` names those, and the two `novel_*` fields say what the graded
rungs need of them — that neither rung reaches a new candidate. For a
cut `Novel` is empty and those fields are vacuous; for a fill it is
"fresh", and they are `not_certifiedInHZ_fresh` and its `WeakLinked`
counterpart.

**What this does not yet cover.** The direction from a truncation *back*
to the original still needs its own argument, because the slot map
there is `k ↦ d + k` and reading it backwards is partial. `σ` is a
total function, so `decided_of_decided_chopHZ` stays bespoke; the two
directions this file does subsume are `decided_chopHZ_of_decided` and
`decided_fillHZ`.
-/

namespace LeanDag

namespace Integration

namespace Hydrozoan

variable {Replica : Type} [Fintype Replica] [DecidableEq Replica]
variable {BlockId : Type} [DecidableEq BlockId] [LinearOrder BlockId]
variable [LeanDag.Hydrozoan.Faults Replica]

/-- **`U'` simulates `U` along the slot map `σ`.** Every field is one of
the predicates `Decided` inspects, and there are no others: that is the
claim the structure makes and the induction below consumes.

`Novel` names the identifiers the target has and the source does not.
The rung fields are stated for anchors of the source, which is where
every anchor of a derivation over the source lives. -/
structure Simulates
    (U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId)
    (V : LeanDag.Hydrozoan.View U) (S : LeanDag.Hydrozoan.Slots Replica)
    (U' : LeanDag.Hydrozoan.BlockUniverse Replica BlockId)
    (V' : LeanDag.Hydrozoan.View U') (S' : LeanDag.Hydrozoan.Slots Replica)
    (σ : ℕ → ℕ) (Novel : BlockId → Prop) : Prop where
  /-- Slots above one in the image are images, at a larger index — what
  the anchor and the intermediate slots of an indirect derivation need. -/
  lift : ∀ k n, σ k < n → ∃ j, σ j = n ∧ k < j
  /-- And the map respects the order, for the other side of that. -/
  mono : ∀ i j, i < j → σ i < σ j
  /-- A candidate of the source is a candidate of the target. -/
  leader_fwd : ∀ k L, @LeanDag.Hydrozoan.IsLeaderBlock _ _ _ _ _ S U (σ k) L →
    @LeanDag.Hydrozoan.IsLeaderBlock _ _ _ _ _ S' U' k L
  /-- And a candidate of the target is one of the source, or novel. -/
  leader_bwd : ∀ k L, @LeanDag.Hydrozoan.IsLeaderBlock _ _ _ _ _ S' U' k L →
    @LeanDag.Hydrozoan.IsLeaderBlock _ _ _ _ _ S U (σ k) L ∨ Novel L
  /-- Anchor eligibility agrees, both slots moving together. -/
  elig : ∀ k j, @LeanDag.Hydrozoan.EligibleAsAnchor Replica S (σ k) (σ j) ↔
    @LeanDag.Hydrozoan.EligibleAsAnchor Replica S' k j
  /-- The three direct rules carry forward. -/
  fast : ∀ k L, LeanDag.Hydrozoan.FastCommitInView U V L (S.slotRound (σ k)) →
    LeanDag.Hydrozoan.FastCommitInView U' V' L (S'.slotRound k)
  slow : ∀ k L, LeanDag.Hydrozoan.SlowCommitInView U V L (S.slotRound (σ k)) →
    LeanDag.Hydrozoan.SlowCommitInView U' V' L (S'.slotRound k)
  skip : ∀ k, @LeanDag.Hydrozoan.SkippedLeaderInView _ _ _ _ _ _ S U V (σ k) →
    @LeanDag.Hydrozoan.SkippedLeaderInView _ _ _ _ _ _ S' U' V' k
  /-- The two rung tests agree at an anchor of the source. -/
  cert : ∀ k A L, A ∈ U.ids →
    (LeanDag.Hydrozoan.CertifiedIn U' A L (S'.slotRound k) ↔
      LeanDag.Hydrozoan.CertifiedIn U A L (S.slotRound (σ k)))
  weak : ∀ k A L, A ∈ U.ids →
    (LeanDag.Hydrozoan.WeakLinked U' A L (S'.slotRound k) ↔
      LeanDag.Hydrozoan.WeakLinked U A L (S.slotRound (σ k)))
  /-- Neither rung reaches a novel candidate. Vacuous when nothing is
  novel, which is the case for a cut. -/
  novel_cert : ∀ k A L, A ∈ U.ids → Novel L →
    ¬ LeanDag.Hydrozoan.CertifiedIn U' A L (S'.slotRound k)
  novel_weak : ∀ k A L, A ∈ U.ids → Novel L →
    ¬ LeanDag.Hydrozoan.WeakLinked U' A L (S'.slotRound k)

namespace Simulates

variable {U U' : LeanDag.Hydrozoan.BlockUniverse Replica BlockId}
  {V : LeanDag.Hydrozoan.View U} {V' : LeanDag.Hydrozoan.View U'}
  {S S' : LeanDag.Hydrozoan.Slots Replica} {σ : ℕ → ℕ} {Novel : BlockId → Prop}

/-- **Simulation transports verdicts.** The six-constructor induction,
once. Every case is a field of the structure applied; nothing about any
particular transformer appears. -/
theorem decided (h : Simulates U V S U' V' S' σ Novel) {n : ℕ} {v : Option BlockId}
    (hd : @LeanDag.Hydrozoan.Decided _ _ _ _ _ _ _ S U V n v) :
    ∀ k, n = σ k → @LeanDag.Hydrozoan.Decided _ _ _ _ _ _ _ S' U' V' k v := by
  induction hd with
  | @directFast n L hL hc =>
      rintro k rfl
      exact LeanDag.Hydrozoan.Decided.directFast (S := S') (h.leader_fwd k L hL)
        (h.fast k L hc)
  | @directSlow n L hL hc =>
      rintro k rfl
      exact LeanDag.Hydrozoan.Decided.directSlow (S := S') (h.leader_fwd k L hL)
        (h.slow k L hc)
  | @directSkip n hskip =>
      rintro k rfl
      exact LeanDag.Hydrozoan.Decided.directSkip (S := S') (h.skip k hskip)
  | @indirectCert n j A L hkj helig hanchor hmid hL hcert ihj ihmid =>
      rintro k rfl
      obtain ⟨j', rfl, hkj'⟩ := h.lift k j hkj
      have hA : A ∈ U.ids := (isLeaderBlock_of_decidedHZ hanchor).1
      refine LeanDag.Hydrozoan.Decided.indirectCert (S := S') hkj'
        ((h.elig k j').mp helig) (ihj j' rfl) ?_ (h.leader_fwd k L hL)
        ((h.cert k A L hA).mpr hcert)
      intro i' h1 h2 he
      exact ihmid (σ i') (h.mono k i' h1) (h.mono i' j' h2) ((h.elig k i').mpr he) i' rfl
  | @indirectWeak n j A L hkj helig hanchor hmid hnocert hL hweak hmin ihj ihmid =>
      rintro k rfl
      obtain ⟨j', rfl, hkj'⟩ := h.lift k j hkj
      have hA : A ∈ U.ids := (isLeaderBlock_of_decidedHZ hanchor).1
      refine LeanDag.Hydrozoan.Decided.indirectWeak (S := S') hkj'
        ((h.elig k j').mp helig) (ihj j' rfl) ?_ ?_ (h.leader_fwd k L hL)
        ((h.weak k A L hA).mpr hweak) ?_
      · intro i' h1 h2 he
        exact ihmid (σ i') (h.mono k i' h1) (h.mono i' j' h2) ((h.elig k i').mpr he) i' rfl
      · intro L' hL' hc
        rcases h.leader_bwd k L' hL' with hold | hnov
        · exact hnocert L' hold ((h.cert k A L' hA).mp hc)
        · exact h.novel_cert k A L' hA hnov hc
      · intro L' hL' hw
        rcases h.leader_bwd k L' hL' with hold | hnov
        · exact hmin L' hold ((h.weak k A L' hA).mp hw)
        · exact absurd hw (h.novel_weak k A L' hA hnov)
  | @indirectSkip n j A hkj helig hanchor hmid hnocert hnoweak ihj ihmid =>
      rintro k rfl
      obtain ⟨j', rfl, hkj'⟩ := h.lift k j hkj
      have hA : A ∈ U.ids := (isLeaderBlock_of_decidedHZ hanchor).1
      refine LeanDag.Hydrozoan.Decided.indirectSkip (S := S') hkj'
        ((h.elig k j').mp helig) (ihj j' rfl) ?_ ?_ ?_
      · intro i' h1 h2 he
        exact ihmid (σ i') (h.mono k i' h1) (h.mono i' j' h2) ((h.elig k i').mpr he) i' rfl
      · intro L' hL' hc
        rcases h.leader_bwd k L' hL' with hold | hnov
        · exact hnocert L' hold ((h.cert k A L' hA).mp hc)
        · exact h.novel_cert k A L' hA hnov hc
      · intro L' hL' hw
        rcases h.leader_bwd k L' hL' with hold | hnov
        · exact hnoweak L' hold ((h.weak k A L' hA).mp hw)
        · exact absurd hw (h.novel_weak k A L' hA hnov)

/-! ## The two transformers as simulations

Each is the structure's fields, assembled from the transfer lemmas P7
and P8 already prove. Neither carries an induction of its own. -/

section Instances

variable {U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId}
  {hsp : SelfParenting U} {V : LeanDag.Hydrozoan.View U}
variable [Fact (HybridCommittee Replica)]

/-- **The fill is a simulation** along the identity on slots, with the
fresh identifiers as the novel ones. -/
theorem simulates_fill (sk : SkipMsg (toCore U hsp)) (S : LeanDag.Hydrozoan.Slots Replica) :
    Simulates U V S (skipFillHZ U hsp sk) (liftViewHZ U hsp sk V) S id
      (fun L => L ∉ U.ids) where
  lift := fun _ n h => ⟨n, rfl, h⟩
  mono := fun _ _ h => h
  leader_fwd := fun _ _ h => isLeaderBlockHZ_fill h
  leader_bwd := fun _ L h => by
    by_cases hL : L ∈ U.ids
    · exact Or.inl (isLeaderBlockHZ_fill_old hL h)
    · exact Or.inr hL
  elig := fun _ _ => Iff.rfl
  fast := fun k L h => (fastCommitInView_fill (V := V) L (S.slotRound k)).mpr h
  slow := fun k L h => (slowCommitInView_fill (V := V) L (S.slotRound k)).mpr h
  skip := fun k h => (skippedLeaderInView_fill (V := V) k).mpr h
  cert := fun _ _ _ hA => certifiedInHZ_fill hA
  weak := fun _ _ _ hA => weakLinkedHZ_fill hA
  novel_cert := fun _ _ _ hA hL => not_certifiedInHZ_fresh hA hL
  novel_weak := fun _ _ _ hA hL => not_weakLinkedHZ_fresh hA hL

/-- **Verdicts survive the fill**, now as a corollary. -/
theorem decided_fill_of_simulates [S : LeanDag.Hydrozoan.Slots Replica]
    (sk : SkipMsg (toCore U hsp)) {k : ℕ} {v : Option BlockId}
    (h : LeanDag.Hydrozoan.Decided U V k v) :
    LeanDag.Hydrozoan.Decided (skipFillHZ U hsp sk) (liftViewHZ U hsp sk V) k v :=
  (simulates_fill sk S).decided h k rfl

/-- **The cut is a simulation** along `k ↦ d + k`, with nothing novel:
a truncation adds no identifier. -/
theorem simulates_chop [S : LeanDag.Hydrozoan.Slots Replica] {d G : ℕ}
    (hd : G ≤ S.slotRound d) :
    Simulates U V S (chopHZ U hsp G) (View.chopHZ V hsp G) (slotsChopHZ hd)
      (fun k => d + k) (fun _ => False) where
  lift := fun _ n h => ⟨n - d, by omega, by omega⟩
  mono := fun _ _ h => by omega
  leader_fwd := fun _ _ h => (isLeaderBlockHZ_chop hd).mpr h
  leader_bwd := fun _ _ h => Or.inl ((isLeaderBlockHZ_chop hd).mp h)
  elig := fun k j => (eligibleAsAnchorHZ_chop hd).symm
  fast := fun k L h => by
    refine (fastCommitInView_chopHZ (V := V) L ((slotsChopHZ hd).slotRound k)).mpr ?_
    rwa [chopRound_add hd k]
  slow := fun k L h => by
    refine (slowCommitInView_chopHZ (V := V) L ((slotsChopHZ hd).slotRound k)).mpr ?_
    rwa [chopRound_add hd k]
  skip := fun k h => (skippedLeaderInView_chopHZ (V := V) hd k).mpr h
  cert := fun k _ _ hA => certifiedIn_chopHZ hd hA k
  weak := fun k _ _ hA => weakLinked_chopHZ hd hA k
  novel_cert := fun _ _ _ _ hL => absurd hL not_false
  novel_weak := fun _ _ _ _ hL => absurd hL not_false

/-- **Verdicts survive the cut**, in the direction the simulation
covers, now as a corollary. -/
theorem decided_chop_of_simulates [S : LeanDag.Hydrozoan.Slots Replica] {d G : ℕ}
    (hd : G ≤ S.slotRound d) {k : ℕ} {v : Option BlockId}
    (h : LeanDag.Hydrozoan.Decided U V (d + k) v) :
    LeanDag.Hydrozoan.Decided (S := slotsChopHZ hd) (chopHZ U hsp G)
      (View.chopHZ V hsp G) k v :=
  (simulates_chop hd).decided h k rfl

end Instances

end Simulates

end Hydrozoan

end Integration

end LeanDag
