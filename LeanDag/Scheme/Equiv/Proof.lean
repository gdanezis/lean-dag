import LeanDag.Scheme.Equiv.Statement
import LeanDag.Scheme.Helpers.Variants
import LeanDag.Scheme.Helpers.Buffered
/-!
# The scheme's rows as carriers — proof

Each row reads what its rule reads (`Helpers/Rows.lean`,
`Helpers/Variants.lean`, `Helpers/Buffered.lean`), so the decision
relations are equal (`ReadAlike.decided_iff`) and so are the carriers
(`toDagRule_eq`).
-/

namespace LeanDag

namespace Scheme

namespace Equiv

theorem mysticetiRow : MysticetiRow := by
  intro Validator BlockId Payload _ _ F _ σ
  exact toDagRule_eq fun S U V k v => (readAlike_mysticeti (S := S) σ U).decided_iff

theorem blueBottlePSRow : BlueBottlePSRow := by
  intro Validator BlockId Payload _ _ F _ σ
  exact toDagRule_eq fun S U V k v => (readAlike_blueBottlePS (S := S) σ U).decided_iff

theorem orcaellaRow : OrcaellaRow := by
  intro Validator BlockId Payload _ _ H _ σ hn
  exact toDagRuleOn_eq _ fun S U _ V k v => (readAlike_orcaella (S := S) σ U hn).decided_iff

theorem cordialMinersPSRow : CordialMinersPSRow := by
  intro Validator BlockId Payload _ _ F _ σ
  have h := toDagRule_eq fun S U V k v => (readAlike_cordial (S := S) σ U).decided_iff
  exact ⟨h, h ▸ AnchoredRule.agree cordialLaws⟩

theorem nemoNemoRow : NemoNemoRow := by
  intro Validator BlockId Payload _ _ _ σ c hn
  have h := toDagRule_eq fun S U V k v => (readAlike_nemo (S := S) σ U hn).decided_iff
  exact ⟨h, h ▸ AnchoredRule.agree nemoBlameLaws⟩

theorem mahiMahiRow : MahiMahiRow := by
  intro Validator BlockId Payload _ _ F _ w hw
  exact toDagRule_eq fun S U V k v => (readAlike_mahiMahi (S := S) hw U).decided_iff

theorem blueBottleAsyncRow : BlueBottleAsyncRow := by
  intro Validator BlockId Payload _ _ F _
  exact toDagRule_eq fun S U V k v => (readAlike_blueBottleAsync (S := S) U).decided_iff

theorem cordialMinersAsyncRow : CordialMinersAsyncRow := by
  intro Validator BlockId Payload _ _ F _
  have h := toDagRule_eq fun S U V k v => (readAlike_cordialAsync (Validator := Validator)
    (BlockId := BlockId) (Payload := Payload) (S := S) U).decided_iff
  exact ⟨h, h ▸ AnchoredRule.agree (cordialAsyncLaws (Validator := Validator) (BlockId := BlockId)
    (Payload := Payload) (w := 5) (by omega))⟩

theorem holds : Statement :=
  ⟨mysticetiRow, blueBottlePSRow, orcaellaRow, cordialMinersPSRow, nemoNemoRow,
    mahiMahiRow, blueBottleAsyncRow, cordialMinersAsyncRow⟩

end Equiv

end Scheme

end LeanDag
