import LeanDag.Mysticeti.Liveness
import LeanDag.DoS.Counting
import LeanDag.Common.Persistence
/-!
# Safety and the DoS condition do not interact

`dos-equivocation-and-growth.md` §4, **D14**.

The claim is that every safety result holds unchanged under `DoSValid`, and
that this is not a theorem to prove but a property of how the condition was
*stated*: a predicate on the universe rather than a field of `ValidWrt`. Had it
been a field, every block universe would have a different type, every existing
proof would be re-elaborated, and every witness rebuilt.

Being free, the claim is also easy to make hollow — so it is worth pinning
down. Each result below is stated with `DoSValid U` in scope and discharged by
the *existing* theorem, with the hypothesis unused. That is what "untouched"
means, and it is checkable: if `DoSValid` were ever folded into validity, or if
a safety result grew a dependency on it, these would stop elaborating.

**What this does not say.** The theorems are untouched; whether their
hypotheses remain *satisfiable* under `DoSValid` is a separate question, and a
live one — §4 is about exactly that, and D15a says the
answer is not comfortable. Nothing here speaks to it.
-/

namespace LeanDagTest

open LeanDag

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {U : BlockUniverse Validator BlockId Payload}

/-! ## Phase 1 — non-equivocation and persistence -/

/-- **T1** under the condition. -/
example (_hdos : DoSValid U) {v : Validator} {i j : BlockId}
    (hi : i ∈ U.ids) (hj : j ∈ U.ids) (hv : v ∈ (Correct : Finset Validator))
    (hic : (U.block i).creator = v) (hjc : (U.block j).creator = v)
    (hround : (U.block i).round = (U.block j).round) : i = j :=
  U.eq_of_creator_eq hi hj hv hic hjc hround

/-- **T2** under the condition. -/
example (_hdos : DoSValid U) {c b : BlockId} (hc : c ∈ U.ids) (h : Reaches U c b) :
    (U.block b).round ≤ (U.block c).round :=
  round_le_of_reaches hc h

/-- **T3 (persistence)** under the condition. -/
example (_hdos : DoSValid U) {b : BlockId} {r : ℕ} {Q : Finset BlockId} (hQ : Q ⊆ U.ids)
    (hQround : ∀ q ∈ Q, (U.block q).round = r + 1)
    (hQref : ∀ q ∈ Q, b ∈ (U.block q).refs)
    (hQquorum : Fintype.card Validator - F.f ≤ (creatorsOf U.block Q).card)
    {c : BlockId} (hc : c ∈ U.ids) (hcr : r + 2 ≤ (U.block c).round) :
    Reaches U c b :=
  reaches_of_quorum_support hQ hQround hQref hQquorum hc hcr

/-! ## Phase 2 — the Mysticeti commit rules -/

/-- **M3** under the condition: a directly skipped block has no certificate
anywhere. -/
example (_hdos : DoSValid U) {L : BlockId} {r : ℕ} (h : DirectSkip U L r) :
    certificates U L r = ∅ :=
  certificates_eq_empty_of_directSkip h

/-- **M5′** under the condition — the one place `distinct_creators` does real
work, and the DoS condition neither helps nor hinders it. -/
example (_hdos : DoSValid U) {L₁ L₂ : BlockId} {r : ℕ}
    (h₁ : (certificates U L₁ r).Nonempty) (h₂ : (certificates U L₂ r).Nonempty)
    (hcreator : (U.block L₁).creator = (U.block L₂).creator) : L₁ = L₂ :=
  eq_of_certificates_nonempty h₁ h₂ hcreator

/-! ## Phase 2 — decisions

Including a liveness-flavoured one (L2), to make the point that it is the
*theorems* that are untouched, whatever happens to the satisfiability of their
hypotheses. -/

variable [S : Slots Validator]

/-- **M6 (agreement)** under the condition. -/
example (_hdos : DoSValid U) {V₁ V₂ : View Validator BlockId Payload U} {k : ℕ}
    {v₁ v₂ : Option BlockId} (h₁ : Decided U V₁ k v₁) (h₂ : Decided U V₂ k v₂) : v₁ = v₂ :=
  AnchoredRule.decided_agree coreLaws trivial h₁ h₂

/-- **L2 (decisions are monotone in the view)** under the condition. -/
example (_hdos : DoSValid U) {V V' : View Validator BlockId Payload U}
    (hsub : V.ids ⊆ V'.ids) {k : ℕ} {v : Option BlockId} (h : Decided U V k v) :
    Decided U V' k v :=
  AnchoredRule.decided_mono coreLaws trivial hsub h

/-! ## And in the other direction

The new results are equally indifferent to the machinery they sit beside: D19a
holds of any universe, whether or not it satisfies `DoSValid`, since it asks
only that a particular history expose nobody. -/

example {b : BlockId} (hb : b ∈ U.ids) (h : ∀ X, ¬ ExposedIn U b X) :
    (history U b).card ≤ Fintype.card Validator * ((U.block b).round + 1) :=
  card_history_le_of_not_exposed hb h

end LeanDagTest
