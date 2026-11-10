import LeanDag.Scheme.Equiv.Statement
import LeanDag.Scheme.Helpers.VoteFree
import LeanDag.Scheme.Helpers.Variants
import LeanDag.Scheme.Helpers.Buffered
/-!
# The scheme's rows as carriers — proof

Each row reads what its rule reads (`Helpers/Rows.lean`,
`Helpers/Variants.lean`, `Helpers/Buffered.lean`), so the decision
relations are equal (`AnchoredRule.ReadAlike.decided_iff`) and so are the carriers
(`AnchoredRule.toDagRule_eq`).
-/

namespace LeanDag

namespace Scheme

namespace Equiv

theorem mysticetiRow : MysticetiRow := by
  intro Validator BlockId Payload _ _ F _ σ
  exact AnchoredRule.toDagRule_eq fun S U V k v => (readAlike_mysticeti (S := S) σ U).decided_iff

theorem blueBottlePSRow : BlueBottlePSRow := by
  intro Validator BlockId Payload _ _ F _ σ
  exact AnchoredRule.toDagRule_eq fun S U V k v => (readAlike_blueBottlePS (S := S) σ U).decided_iff

theorem orcaellaRow : OrcaellaRow := by
  intro Validator BlockId Payload _ _ H _ σ hn
  exact AnchoredRule.toDagRuleOn_eq _ fun S U _ V k v => (readAlike_orcaella (S := S) σ U hn).decided_iff

theorem cordialMinersPSRow : CordialMinersPSRow := by
  intro Validator BlockId Payload _ _ F _ σ
  have h := AnchoredRule.toDagRule_eq fun S U V k v => (readAlike_cordial (S := S) σ U).decided_iff
  exact ⟨h, h ▸ AnchoredRule.agree cordialLaws⟩

theorem nemoNemoRow : NemoNemoRow := by
  intro Validator BlockId Payload _ _ _ σ c hn
  have h := AnchoredRule.toDagRule_eq fun S U V k v => (readAlike_nemo (S := S) σ U hn).decided_iff
  exact ⟨h, h ▸ AnchoredRule.agree nemoBlameLaws⟩

theorem mahiMahiRow : MahiMahiRow := by
  intro Validator BlockId Payload _ _ F _ w hw
  exact AnchoredRule.toDagRule_eq fun S U V k v => (readAlike_mahiMahi (S := S) hw U).decided_iff

theorem blueBottleAsyncRow : BlueBottleAsyncRow := by
  intro Validator BlockId Payload _ _ F _
  exact AnchoredRule.toDagRule_eq fun S U V k v => (readAlike_blueBottleAsync (S := S) U).decided_iff

theorem cordialMinersAsyncRow : CordialMinersAsyncRow := by
  intro Validator BlockId Payload _ _ F _
  have h := AnchoredRule.toDagRule_eq fun S U V k v => (readAlike_cordialAsync (Validator := Validator)
    (BlockId := BlockId) (Payload := Payload) (S := S) U).decided_iff
  exact ⟨h, h ▸ AnchoredRule.agree (cordialAsyncLaws (Validator := Validator) (BlockId := BlockId)
    (Payload := Payload) (w := 5) (by omega))⟩

theorem voteFree : VoteFree := by
  intro Validator BlockId Payload _ _ _ P _ honest p σ σ'
  exact AnchoredRule.toDagRuleOn_eq _ fun S U hU V k v => (readAlike_noEquiv (S := S) p σ σ' hU).decided_iff

theorem bufferedRowsNoEquiv : BufferedRowsNoEquiv := by
  intro Validator BlockId Payload _ _ _
  refine ⟨fun σ w hw => ?_, fun σ => ?_, fun σ => ?_⟩
  · exact AnchoredRule.toDagRuleOn_eq _ fun S U hU V k v =>
      ((readAlike_noEquiv (S := S) _ σ leastSel hU).decided_iff).trans
        (readAlike_mahiMahi (S := S) hw U).decided_iff
  · exact AnchoredRule.toDagRuleOn_eq _ fun S U hU V k v =>
      ((readAlike_noEquiv (S := S) _ σ leastSel hU).decided_iff).trans
        (readAlike_blueBottleAsync (S := S) U).decided_iff
  · exact AnchoredRule.toDagRuleOn_eq _ fun S U hU V k v =>
      ((readAlike_noEquiv (S := S) _ σ leastSel hU).decided_iff).trans
        (readAlike_cordialAsync (Validator := Validator) (BlockId := BlockId)
          (Payload := Payload) (S := S) U).decided_iff

theorem holds : Statement :=
  ⟨mysticetiRow, blueBottlePSRow, orcaellaRow, cordialMinersPSRow, nemoNemoRow,
    mahiMahiRow, blueBottleAsyncRow, cordialMinersAsyncRow, voteFree, bufferedRowsNoEquiv⟩

end Equiv

end Scheme

end LeanDag
