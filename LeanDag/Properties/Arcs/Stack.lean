import LeanDag.Properties.Compose
import LeanDag.Properties.Arcs.Liveness
/-!
# The composition theorem: every stack of mechanisms is one mechanism

`docs/target-properties.md` §11.11. Each DAG-transforming mechanism
delivers a `Rebased`: a rebase of the universe above a settling round,
and of the schedule. `Stack` is a finite sequence of them, and
`Stack.rebased` says the sequence is one `Rebased` — offsets and base
slots add, the settling round is the latest read in the first
universe's frame — with no restriction on which mechanisms or in what
order. `Stack.safe_and_live` is the claim: for any rule with `Banded`,
`Agree` and a support, every verdict above the composite settling round
transports, agrees across views, and the liveness precondition
carries. Two view hypotheses, since they are different facts: safety
asks the views agree above the settling round, liveness asks the
composite's view cover the horizon, which includes blocks the
mechanisms added.
-/

namespace LeanDag

namespace Properties

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {R : DagRule Validator BlockId Payload}

/-- **A stack of mechanisms**: a finite sequence, each step a `Rebased`.
The indices carry the composite's offset, settling round and base slot,
accumulated as `Rebased.trans` accumulates them. -/
inductive Stack (R : DagRule Validator BlockId Payload) :
    R.Universe → Slots Validator → R.Universe → Slots Validator → ℕ → ℕ → ℕ → Prop
  | nil {U : R.Universe} {S : Slots Validator} : Stack R U S U S 0 0 0
  | step {U U' U'' : R.Universe} {S S' S'' : Slots Validator} {G R₀ d G' R₀' d' : ℕ} :
      Rebased R U U' S S' G R₀ d → Stack R U' S' U'' S'' G' R₀' d' →
      Stack R U S U'' S'' (G + G') (max R₀ (R₀' + G)) (d + d')

/-- **A stack is one mechanism.** -/
theorem Stack.rebased {U U' : R.Universe} {S S' : Slots Validator} {G R₀ d : ℕ} :
    Stack R U S U' S' G R₀ d → Rebased R U U' S S' G R₀ d
  | .nil => Rebased.refl
  | .step h st => h.trans st.rebased

/-! ## Liveness across a rebase -/

namespace Support

variable (sp : Support R)

/-- **`live` survives any rebase**, at the rebased numbering, for a
window above the settling round. `live_of_truncates` at a cut,
`live_of_sustains` at a fill; here the two are one statement. -/
theorem live_of_rebased {rel : Reliability Validator} (hloc : sp.Local)
    (hr : Rebased R U U' S S' G R₀ d) {V : R.View U} {V' : R.View U'}
    {T : Finset Validator} {lo K : ℕ}
    (hlive : sp.live rel S V T lo K) (hR₀ : R₀ ≤ S.slotRound lo) (hlo : d ≤ lo) (hK : lo < K)
    (hV' : ∀ N, G ≤ N → CoversUpto R V N → CoversUpto R V' (N - G))
    (hw : ∀ r, G ≤ r → sp.waveAt (r - G) = sp.waveAt r) :
    sp.live rel S' V' T (lo - d) (K - d) := by
  obtain ⟨hq, N, hcov, hN, hslot⟩ := hlive
  have hGN : G ≤ N := by
    have := hN lo hK
    have := hr.base
    have := S.mono hlo
    omega
  refine ⟨hq, N - G, hV' N hGN hcov, ?_, ?_⟩
  · intro k' hk'
    have hs := hr.slotRound k'
    have := hN (d + k') (by omega)
    have hGk : G ≤ S.slotRound (d + k') := le_trans hr.base (S.mono (Nat.le_add_right d k'))
    have hsr : S'.slotRound k' = S.slotRound (d + k') - G := by omega
    rw [hsr, hw _ hGk]
    omega
  · intro k' hlo' hK' hlead'
    have hs := hr.slotRound k'
    have hl := hr.leader k'
    have hlead : S.leader (d + k') ∈ T := by rw [← hl]; exact hlead'
    obtain ⟨hpop, hcert⟩ := hslot (d + k') (by omega) (by omega) hlead
    have hGk : G ≤ S.slotRound (d + k') := le_trans hr.base (S.mono (Nat.le_add_right d k'))
    have hRk : R₀ ≤ S.slotRound (d + k') := le_trans hR₀ (S.mono (by omega))
    have hsr : S'.slotRound k' = S.slotRound (d + k') - G := by omega
    refine ⟨?_, ?_⟩
    · intro n' h1 h2
      rw [hsr, hw _ hGk] at h2
      have := hr.toRebasedAbove.populatedOn_of (T := T) (r := n' + G) (by omega) (by omega)
        (hpop (n' + G) (by omega) (by omega))
      rwa [Nat.add_sub_cancel] at this
    · rintro L ⟨hL', hLr', hLc'⟩
      obtain ⟨hLU, hround⟩ := hr.toRebasedAbove.of_mem' hL' (by omega)
      have hLr : (R.block U L).round = S.slotRound (d + k') := by omega
      have hLc : (R.block U L).creator = S.leader (d + k') := by
        rw [← hr.creator L hLU (by omega), hLc']; exact hl
      have := sp.certifiesAt_of_rebased hloc hr.toRebasedAbove (T := T)
        (r := S.slotRound (d + k')) hRk hGk (hw _ hGk) hLU hLr (hcert L ⟨hLU, hLr, hLc⟩)
      have e : S.slotRound (d + k') - G = S'.slotRound k' := by omega
      rwa [e] at this

end Support

/-! ## The composition theorem -/

/-- **Every stack of mechanisms keeps safety and liveness**, for any rule
with `Banded`, `Agree` and a support. Above the composite settling
round: verdicts transport to the composite's numbering, any view of
the composite agrees with the original, and the liveness precondition
carries. Nothing is assumed about which mechanisms are stacked or in
what order, only that the support's wave is the same at a round and at
its shift by the composite's `G`. -/
theorem Stack.safe_and_live (hb : Banded R) (ha : Agree R) (sp : Support R) (hloc : sp.Local)
    (st : Stack R U S U' S' G R₀ d) {V : R.View U} {V' : R.View U'}
    (hv : ViewAgreeAbove R V V' R₀) (hw : ∀ r, G ≤ r → sp.waveAt (r - G) = sp.waveAt r) :
    (∀ (k : ℕ) (v : Option BlockId), R₀ ≤ S.slotRound (d + k) →
        (R.Decided S V (d + k) v ↔ R.Decided S' V' k v)) ∧
    (∀ (W : R.View U') (k : ℕ) (w v : Option BlockId), R₀ ≤ S.slotRound (d + k) →
        R.Decided S' W k w → R.Decided S V (d + k) v → w = v) ∧
    (∀ {rel : Reliability Validator} {T : Finset Validator} {lo K : ℕ},
        sp.live rel S V T lo K → R₀ ≤ S.slotRound lo → d ≤ lo → lo < K →
        (∀ N, G ≤ N → CoversUpto R V N → CoversUpto R V' (N - G)) →
        sp.live rel S' V' T (lo - d) (K - d)) :=
  ⟨fun k v hk => decided_of_rebased hb st.rebased hv k hk v,
   fun _ k _ _ hk hW hV => decided_agree_rebased ha hb st.rebased hv hk hW hV,
   fun hlive hR₀ hlo hK hV' => sp.live_of_rebased hloc st.rebased hlive hR₀ hlo hK hV' hw⟩

end Properties

end LeanDag
