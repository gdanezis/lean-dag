import LeanDag.RedSnapper.Helpers.Propagation
import LeanDag.RedSnapper.Helpers.Dead
import LeanDag.RedSnapper.CertificateExclusion.Proof

/-!
# Verdict lemmas

Generated infrastructure for `TxAgreement/Proof.lean`: monotonicity of
inclusion, candidacy, conflict and certificates along reachability;
the certificate behind every finalization; and the two "no anchor is
ever release-ready" inductions — from a consensusless quorum of
certificates (via propagation and the round-bounded exclusions of RS2)
and from a live certificate at an anchor (via chaining). Nothing here is
part of the audit surface.
-/

namespace LeanDag

namespace RedSnapper

variable {Validator BlockId Tx Obj : Type*} [Fintype Validator] [DecidableEq Validator]
  [DecidableEq BlockId] [F : Faults Validator] [T : Transactions Tx Obj]
  {U : Universe Validator BlockId Tx Obj}

omit [DecidableEq BlockId] T in
theorem includes_mono {b b' : BlockId} {tx : Tx} (hr : Reaches U b b')
    (h : Includes U b' tx) : Includes U b tx :=
  let ⟨c, hc, htx, hrc⟩ := h
  ⟨c, hc, htx, hr.trans hrc⟩

omit [DecidableEq BlockId] in
theorem isCandidate_mono {b b' : BlockId} {o : Obj} {tx : Tx} (hr : Reaches U b b')
    (h : IsCandidate U b' o tx) : IsCandidate U b o tx :=
  ⟨h.1, h.2.1, includes_mono hr h.2.2⟩

omit [DecidableEq BlockId] in
theorem conflicted_mono {b b' : BlockId} {o : Obj} (hr : Reaches U b b')
    (h : Conflicted U b' o) : Conflicted U b o :=
  let ⟨tx, tx', h1, h2, hne⟩ := h
  ⟨tx, tx', isCandidate_mono hr h1, isCandidate_mono hr h2, hne⟩

omit [DecidableEq BlockId] in
theorem hasCert_mono {b b' : BlockId} {tx : Tx} (hr : Reaches U b b')
    (h : HasCert U b' tx) : HasCert U b tx :=
  let ⟨C, hC, hc, hrC⟩ := h
  ⟨C, hC, hc, hr.trans hrC⟩

omit [DecidableEq BlockId] in
/-- A certified transaction is a candidate wherever the certificate is
reachable. -/
theorem isCandidate_of_hasCert {b : BlockId} {tx : Tx} (h : HasCert U b tx) :
    IsCandidate U b (T.input tx) tx :=
  let ⟨_, _, hc, hrC⟩ := h
  ⟨hc.1.1, rfl, includes_mono hrC hc.1.2.1⟩

/-- Every finalization carries a certificate. -/
theorem cert_of_finalized {A : Anchors U} {V : View U} {tx : Tx}
    (h : TxVerdict U A V tx Fate.finalized) : ∃ C ∈ U.ids, IsFastCert U C tx := by
  cases h with
  | fastFinal ho hq =>
      obtain ⟨C, hCmem, hC⟩ := exists_of_atLeast quorum_pos hq
      exact ⟨C, mem_ids_of_mem_blocksAt (Finset.mem_inter.mp hCmem).1, hC⟩
  | finalizeOnCommit hi hcand hnc hcert =>
      obtain ⟨C, hC, hc, -⟩ := hcert
      exact ⟨C, hC, hc⟩
  | resolveCommit hi hconf hcand hcert hlive =>
      obtain ⟨C, hC, hc, -⟩ := hcert
      exact ⟨C, hC, hc⟩

omit [DecidableEq BlockId] in
/-- The redundancy claim of `finalizeOnCommit`'s docstring, certified:
at an anchor, every disjunct of `Dead` forces a visible conflict on a
candidate's input — a certified rival is a second candidate, a skip
certificate carries skip votes that saw the conflict, and a release
lifts the earlier anchor's conflict through the chain. -/
theorem conflicted_of_deadGiven {A : Anchors U} {i : ℕ} {a : BlockId} {tx : Tx}
    (hia : A.seq[i]? = some a) (hcand : IsCandidate U a (T.input tx) tx)
    (hdead : DeadGiven U a (ReleasedBelow U A i) tx) :
    Conflicted U a (T.input tx) := by
  rcases hdead with ⟨tx', hconf, hcert⟩ | ⟨C, hC, hskip, hr⟩ | hrel
  · exact ⟨tx, tx', hcand, hconf.2.symm ▸ isCandidate_of_hasCert hcert, hconf.1⟩
  · obtain ⟨p, hp, hskipvote⟩ := exists_of_atLeast half_pos hskip
    exact conflicted_mono (hr.trans (Reaches.single hp)) hskipvote.1.2
  · obtain ⟨j, hj, aj, hja, hconfj, -, -⟩ := releasedBelow_iff_exists.mp hrel
    exact conflicted_mono (anchor_reaches (le_of_lt hj) hja hia) hconfj

open CertificateExclusion

omit [DecidableEq BlockId] in
/-- No anchor is ever release-ready for the input of a transaction with
a consensusless quorum of certificates: anchors above the quorum's round
see a live certificate by propagation; anchors at or below it would need
release evidence that RS2's round-bounded exclusions forbid. -/
theorem no_ready_of_fastQuorum (hdisc : StanceDiscipline U) {A : Anchors U} {r : ℕ}
    {tx : Tx}
    (hq : AtLeast U (quorum Validator) (blocksAt U r) fun C => IsFastCert U C tx) :
    ∀ i, ¬ ResolveReadyAt U A i (T.input tx) := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
      rintro ⟨a, hia, hconf, hdead, C', hC', hcert', hrC'⟩
      have ha : a ∈ U.ids := anchor_mem_ids hia
      obtain ⟨C0, hC0mem, hC0⟩ := exists_of_atLeast quorum_pos hq
      have hC0id : C0 ∈ U.ids := mem_ids_of_mem_blocksAt hC0mem
      have hC0r : (U.block C0).round = r := (Finset.mem_filter.mp hC0mem).2
      by_cases har : r < (U.block a).round
      · obtain ⟨C, hCid, hCert, hreach⟩ := quorum_propagation hq a ha har
        have hHas : HasCert U a tx := ⟨C, hCid, hCert, hreach⟩
        rcases hdead tx (isCandidate_of_hasCert hHas) hHas with
          ⟨tx', hconf', hcert'⟩ | ⟨Cs, hCs, hskip, -⟩ | hrel
        · obtain ⟨C₁, hC₁, hc₁, -⟩ := hcert'
          exact certUniqueness hdisc C hCid C₁ hC₁ tx tx' hconf' hCert hc₁
        · exact ackSkipExclusion hdisc C hCid Cs hCs tx hCert hskip
        · obtain ⟨j, hj, hready⟩ := releasedBelow_iff_exists.mp hrel
          exact ih j hj hready
      · have hC'round : (U.block C').round ≤ r :=
          le_trans (round_le_of_reaches ha hrC') (by omega)
        rcases hcert' with hskip | hunlock
        · exact ackSkipExclusion hdisc C0 hC0id C' hC' tx hC0 hskip
        · exact ackUnlockExclusionBelow hdisc C0 hC0id C' hC' tx hC0 hunlock (by omega)

omit [DecidableEq BlockId] in
/-- No anchor is ever release-ready for the input of a transaction with
a live certificate at anchor `j`, once nothing below `j` is ready:
anchors from `j` on see the certificate through the chain, and it stays
alive by induction. -/
theorem no_ready_of_anchor_cert (hdisc : StanceDiscipline U) {A : Anchors U} {j : ℕ}
    {aj : BlockId} {tx : Tx} (hj : A.seq[j]? = some aj) (hcert : HasCert U aj tx)
    (hlow : ∀ i < j, ¬ ResolveReadyAt U A i (T.input tx)) :
    ∀ i, ¬ ResolveReadyAt U A i (T.input tx) := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
      intro hready
      rcases Nat.lt_or_ge i j with hij | hij
      · exact hlow i hij hready
      · obtain ⟨a, hia, hconf, hdead, C', hC', hcert', hrC'⟩ := hready
        obtain ⟨C, hCid, hCert, hrC⟩ := hasCert_mono (anchor_reaches hij hj hia) hcert
        rcases hdead tx (isCandidate_of_hasCert ⟨C, hCid, hCert, hrC⟩)
            ⟨C, hCid, hCert, hrC⟩ with
          ⟨tx', hconf', hcert''⟩ | ⟨Cs, hCs, hskip, -⟩ | hrel
        · obtain ⟨C₁, hC₁, hc₁, -⟩ := hcert''
          exact certUniqueness hdisc C hCid C₁ hC₁ tx tx' hconf' hCert hc₁
        · exact ackSkipExclusion hdisc C hCid Cs hCs tx hCert hskip
        · obtain ⟨k, hk, hready'⟩ := releasedBelow_iff_exists.mp hrel
          exact ih k (by omega) hready'

end RedSnapper

end LeanDag
