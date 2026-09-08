import LeanDag.Properties.Band
/-!
# What follows from the band

`docs/target-properties.md` §3.8 and §4. Nothing here is an obligation:
every theorem discharges one property from `Banded`, once and
generically, so a protocol proving it need not prove any of them —
though a protocol may still prove one directly, as Hydrozoan does for
`Persist`. What a protocol or mechanism must show is `Causal`, `Agree`,
`Banded`, `ViewSound`, `LocalTruncate`, `LeaderCommits`, `Descends` and
`Sustains`; the rest of `Properties/` is vocabulary, a consequence
(here), or optional (`Optional/`).
-/

namespace LeanDag

namespace Properties

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {R : DagRule Validator BlockId Payload}

/-- **Persistence falls out.** An extension carries every band and adds
only blocks; a larger view holds everything the band names. -/
theorem Persist.of_banded (h : Banded R) : Persist R := by
  intro S U U' he V V' hV k v hd
  obtain ⟨top, htop⟩ := h S U V k v hd
  exact htop 0 0 0 0 S U' V' k (by omega) (fun m m' hm => by
      have : m = m' := by omega
      subst this; rfl)
    (fun m m' hm _ => by have : m = m' := by omega
                         subst this; rfl)
    (AgreeBand.of_extends he _ _) (fun b hb _ _ => hV hb)

/-- **And monotonicity in the view.** Fix the universe and the band
carries itself; a larger view holds everything the band names. The
core's L2 is a four-case induction, and this is the same statement with
none. -/
theorem decided_mono_of_banded (h : Banded R) {S : Slots Validator} {U : R.Universe}
    {V V' : R.View U} (hsub : R.viewIds V ⊆ R.viewIds V') {k : ℕ} {v : Option BlockId}
    (hd : R.Decided S V k v) : R.Decided S V' k v := by
  obtain ⟨top, htop⟩ := h S U V k v hd
  exact htop 0 0 0 0 S U V' k (by omega) (fun m m' hm => by
      have : m = m' := by omega
      subst this; rfl)
    (fun m m' hm _ => by have : m = m' := by omega
                         subst this; rfl)
    AgreeBand.refl (fun b hb _ _ => hsub hb)

/-- **A bound falls out of the band.** The slots sitting at or below a
round are finitely many, since the round structure is monotone and
unbounded, so the band's top names a slot bound and the verdict is
unchanged by reassignment above it.

The bound is not tight: it is every slot the band's rounds can hold,
where a derivation may have named fewer. A mechanism wanting a tight
bound asks the protocol for one (`Commit.lean`); this is what a rule
gets for nothing. -/
theorem exists_decidedBelow (h : Banded R) {S : Slots Validator} {U : R.Universe}
    {V : R.View U} {k : ℕ} {v : Option BlockId} (hd : R.Decided S V k v) :
    ∃ B, DecidedBelow R S B V k v := by
  obtain ⟨top, ht⟩ := h S U V k v hd
  obtain ⟨B₀, hB₀⟩ := S.unbounded (top + 1)
  refine ⟨max (k + 1) B₀, lt_of_lt_of_le (Nat.lt_succ_self k) (le_max_left _ _), hd, ?_⟩
  intro S' hround hlead
  refine ht 0 0 0 0 S' U V k (by omega) ?_ ?_ AgreeBand.refl (fun b hb _ _ => hb)
  · intro m m' hm
    have hmm : m = m' := by omega
    subst hmm
    simp only [Nat.add_zero]
    rw [hround]
  · intro m m' hm hb
    have hmm : m = m' := by omega
    subst hmm
    refine (hlead m ?_).symm
    by_contra hge
    push_neg at hge
    have hB : B₀ ≤ m := le_trans (le_max_right _ _) hge
    have := S.mono hB
    omega

end Properties

end LeanDag
