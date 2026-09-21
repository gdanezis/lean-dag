import LeanDag.RedSnapper.Helpers.Chain
import LeanDag.RedSnapper.Model.Votes

/-!
# The exclusivity cores

Generated: the vote-level lemmas behind RS2 — a declaring block reads
its own declaration, an ACK declaration below a block makes
`AckedBefore`, and the three impossible pairs at one correct author: two
fast votes for conflicting transactions, a fast vote with a `⊥` stance
at or below its round, and a fast vote with a skip vote. Each is the
paper's argument with the quorum stripped away; the counting is applied
in `CertificateExclusion/Proof.lean`. Nothing here is part of the audit
surface.
-/

namespace LeanDag

namespace RedSnapper

variable {Validator BlockId Tx Obj : Type*} [Fintype Validator] [DecidableEq Validator]
  [F : Faults Validator] [T : Transactions Tx Obj] {U : Universe Validator BlockId Tx Obj}

omit T in
/-- A declaring block reads its own declaration as its stance: it is its
own unique latest declarer. -/
theorem stanceIs_self_of_declares {e : BlockId} {o : Obj} {s : Stance Tx}
    (he : e ∈ U.ids) (hd : (U.block e).declares o = some s) :
    StanceIs U (U.block e).author o e (some s) := by
  have hdecl : Declaring U (U.block e).author o e e :=
    ⟨he, rfl, Reaches.refl, by simp [hd]⟩
  refine ⟨e, ⟨hdecl, ?_⟩, hd, ?_⟩
  · intro b'' hb''
    exact round_le_of_reaches he hb''.2.2.1
  · intro b'' hb''
    by_contra hne
    have h1 := round_lt_of_reaches_ne he hb''.1.2.2.1 hne
    have h2 := hb''.2 e hdecl
    omega

omit T in
/-- An own ACK declaration in the history makes `AckedBefore`. -/
theorem ackedBefore_of_declares {id : Validator} {o : Obj} {b e : BlockId} {tx : Tx}
    (he : e ∈ U.ids) (ha : (U.block e).author = id) (hr : Reaches U b e)
    (hd : (U.block e).declares o = some (Stance.ack tx)) : AckedBefore U id o b :=
  ⟨e, tx, he, ha, hr, ha ▸ stanceIs_self_of_declares he hd⟩

/-- The latest ACK declarer behind a fast vote. -/
theorem exists_ack_declarer {c : BlockId} {tx : Tx} (hv : IsFastVote U c tx) :
    ∃ e, e ∈ U.ids ∧ (U.block e).author = (U.block c).author ∧ Reaches U c e ∧
      (U.block e).declares (T.input tx) = some (Stance.ack tx) ∧
      ∀ b'', Declaring U (U.block c).author (T.input tx) c b'' →
        (U.block b'').round ≤ (U.block e).round := by
  obtain ⟨-, -, hs⟩ := hv
  obtain ⟨e, hL, hd, -⟩ := hs
  exact ⟨e, hL.1.1, hL.1.2.1, hL.1.2.2.1, hd, hL.2⟩

omit T in
/-- The latest `⊥` declarer behind a `⊥` stance. -/
theorem exists_bot_declarer {d : BlockId} {o : Obj} {id : Validator}
    (hs : StanceIs U id o d (some Stance.bot)) :
    ∃ e, e ∈ U.ids ∧ (U.block e).author = id ∧ Reaches U d e ∧
      (U.block e).declares o = some Stance.bot := by
  obtain ⟨e, hL, hd, -⟩ := hs
  exact ⟨e, hL.1.1, hL.1.2.1, hL.1.2.2.1, hd⟩

/-- Lemma single-ack at the vote level: one correct author, two fast
votes, conflicting transactions — impossible. -/
theorem no_conflicting_fast_votes (hdisc : StanceDiscipline U)
    {c c' : BlockId} {tx tx' : Tx}
    (hcor : (U.block c).author ∈ (Correct : Finset Validator))
    (ha : (U.block c').author = (U.block c).author)
    (hconf : Conflict tx tx') (hv : IsFastVote U c tx) (hv' : IsFastVote U c' tx') :
    False := by
  obtain ⟨hne, hin⟩ := hconf
  obtain ⟨e, he, hae, -, hde, -⟩ := exists_ack_declarer hv
  obtain ⟨e', he', hae', -, hde', -⟩ := exists_ack_declarer hv'
  rw [← hin] at hde'
  have hae'' : (U.block e').author = (U.block e).author := by rw [hae', ha, hae]
  have hecor : (U.block e).author ∈ (Correct : Finset Validator) := hae.symm ▸ hcor
  have heq : e = e' → False := by
    intro h
    rw [h, hde'] at hde
    exact hne (Stance.ack.inj (Option.some.inj hde)).symm
  rcases own_comparable he he' hecor hae'' with hr | hr
  · exact hne (hdisc.no_switch e he hecor e' he' hae'' hr (fun h => heq h.symm)
      (T.input tx) tx tx' hde hde').symm
  · exact hne (hdisc.no_switch e' he' (hae''.symm ▸ hecor) e he hae''.symm hr heq
      (T.input tx) tx' tx hde' hde)

/-- A fast vote and a `⊥` stance at or below its round, one correct
author — impossible: the `⊥` declarer sits below the latest ACK
declarer, and `⊥` is absorbing. -/
theorem no_fast_vote_and_bot_below (hdisc : StanceDiscipline U)
    {c d : BlockId} {tx : Tx} (hc : c ∈ U.ids) (hd : d ∈ U.ids)
    (hcor : (U.block c).author ∈ (Correct : Finset Validator))
    (ha : (U.block d).author = (U.block c).author)
    (hround : (U.block d).round ≤ (U.block c).round)
    (hv : IsFastVote U c tx)
    (hs : StanceIs U (U.block d).author (T.input tx) d (some Stance.bot)) : False := by
  obtain ⟨e, he, hae, -, hde, hmax⟩ := exists_ack_declarer hv
  obtain ⟨d₀, hd₀, had₀, hrd₀, hdd₀⟩ := exists_bot_declarer hs
  have had₀' : (U.block d₀).author = (U.block c).author := had₀.trans ha
  have h1 : (U.block d₀).round ≤ (U.block c).round :=
    le_trans (round_le_of_reaches hd hrd₀) hround
  have hcd₀ : Reaches U c d₀ := reaches_own_of_round_le hc hd₀ hcor had₀' h1
  have h2 : (U.block d₀).round ≤ (U.block e).round :=
    hmax d₀ ⟨hd₀, had₀', hcd₀, by simp [hdd₀]⟩
  have hne : e ≠ d₀ := by
    intro h
    rw [h, hdd₀] at hde
    simp at hde
  have hecor : (U.block e).author ∈ (Correct : Finset Validator) := hae.symm ▸ hcor
  have hred₀ : Reaches U e d₀ :=
    reaches_own_of_round_le he hd₀ hecor (had₀'.trans hae.symm) h2
  exact hdisc.no_return e he hecor d₀ hd₀ (had₀'.trans hae.symm) hred₀ hne.symm
    (T.input tx) tx hde hdd₀

/-- Lemma univalent at the vote level: one correct author, a fast vote
and a skip vote on the transaction's input — impossible. -/
theorem no_fast_vote_and_skip_vote (hdisc : StanceDiscipline U)
    {c d : BlockId} {tx : Tx} (hc : c ∈ U.ids) (hd : d ∈ U.ids)
    (hcor : (U.block c).author ∈ (Correct : Finset Validator))
    (ha : (U.block d).author = (U.block c).author)
    (hv : IsFastVote U c tx) (hskip : IsSkipVote U d (T.input tx)) : False := by
  obtain ⟨⟨hs, -⟩, hnacked⟩ := hskip
  by_cases h : (U.block d).round ≤ (U.block c).round
  · exact no_fast_vote_and_bot_below hdisc hc hd hcor ha h hv hs
  · obtain ⟨e, he, hae, hre, hde, -⟩ := exists_ack_declarer hv
    have hdc : Reaches U d c :=
      reaches_own_of_round_le hd hc (ha.symm ▸ hcor) ha.symm (by omega)
    exact hnacked (ackedBefore_of_declares he (hae.trans ha.symm) (hdc.trans hre) hde)

end RedSnapper

end LeanDag
