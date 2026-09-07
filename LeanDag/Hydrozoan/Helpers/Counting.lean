import LeanDag.Hydrozoan.Model.DirectRules
import LeanDag.Hydrozoan.Helpers.Faults
/-!
# The quorum-counting toolkit

Generated proof infrastructure: membership unfoldings for the rule
sets, the "guilty replica is Byzantine" collapse lemmas, and the
quorum-intersection arithmetic. Nothing here is part of the audit
surface.
-/

namespace LeanDag

namespace Hydrozoan


variable {Replica BlockId : Type*} [Fintype Replica] [DecidableEq Replica]
  [DecidableEq BlockId] [F : LeanDag.Hydrozoan.Faults Replica]
  {U : BlockUniverse Replica BlockId}

/-- A slow commit requires at least one certificate (`q_slow ≥ 1`). -/
theorem certificates_nonempty_of_slowCommit {L : BlockId} {r : ℕ}
    (h : SlowCommit U L r) : (certificates U L r).Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  intro hempty
  simp only [SlowCommit, certifiers, hempty, creatorsOf, Finset.image_empty,
    Finset.card_empty, qSlow] at h
  omega

/-- `n + f < 2·q_fast` — no two conflicting fast quorums. -/
theorem nf_lt_two_qFast : Fintype.card Replica + F.f < 2 * qFast Replica := by
  have := F.card_replicas
  simp only [qFast, p]
  omega

/-- `n + f < 2·q_cert` — certificate uniqueness. -/
theorem nf_lt_two_qCert : Fintype.card Replica + F.f < 2 * qCert Replica := by
  have := F.card_replicas
  simp only [qCert]
  omega

/-- The rung ordering: the weak quorum never exceeds the certificate
quorum. -/
theorem qWeak_le_qCert : qWeak Replica ≤ qCert Replica := by
  have := F.card_replicas
  simp only [qWeak, qCert, p]
  omega

/-- `n + f < q_fast + q_cert` — the fast path starves every conflicting
certificate. -/
theorem nf_lt_qFast_add_qCert :
    Fintype.card Replica + F.f < qFast Replica + qCert Replica := by
  have := F.card_replicas
  simp only [qFast, qCert, p]
  omega

end Hydrozoan

end LeanDag
