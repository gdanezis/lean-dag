import LeanDag.Integration.Margin
import LeanDag.CommonCore

/-!
# I19 — Safe Skip against a common-core target

The design question report §16.8 leaves open is which reference
discipline the protocol should state, and the residual worry behind it
is *availability*: a validator that cites blocks it does not hold
cannot serve them, however sound the storage accounting is
(§16.7's I17).

Choosing the fill's target from the **common core** removes the worry
at its source rather than trading it away. Report §5.2's T3c produces,
at every round, a correct-authored block that *every* block two rounds
later reaches (`exists_common_correct_ancestor`) — so a validator
holding any recent block already has it, and everything below it, in
its own causal past. A fill whose donor line is built from such blocks
therefore cites only material every producing validator already holds.

Three consequences, and they are the ones the mechanism wants:

* **No transmission.** The message names the target; every recipient
  reconstructs the filled blocks from its own DAG, because the blocks
  the fill cites are already in its cone.
* **The recovering validator holds what it cites.** After bootstrap it
  has the common core like everyone else, so the tight, author-
  attributed discipline is satisfiable rather than something to weaken.
* **The choice of §16.8 stops mattering in practice.** Either clause is
  met, so the specification can state whichever it prefers on other
  grounds.

The common core is not a new assumption. T3c is a counting theorem of
report §5.2 with no synchrony hypothesis and no progress hypothesis —
it holds of every universe, which is what makes this a restriction on
*how a message chooses its target*, not on the executions the protocol
admits.
-/

namespace LeanDag

namespace Integration

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {U : BlockUniverse Validator BlockId Payload}

/-- A block is **common at round `r`** when every block two rounds
above it reaches it. Report §5.2's T3c supplies one at every round, of
correct authorship, with no assumption whatever. -/
def CommonAt (U : BlockUniverse Validator BlockId Payload)
    (b : BlockId) (r : ℕ) : Prop :=
  b ∈ U.ids ∧ (U.block b).round = r ∧
    ∀ c ∈ U.ids, (U.block c).round = r + 2 → Reaches U c b

/-- **Common blocks exist at every round**, and are correct-authored —
T3c restated in the vocabulary above. The hypothesis is only that some
block exists two rounds up, which is what having a round to fill
means. -/
theorem exists_commonAt {r : ℕ} {c₀ : BlockId} (hc₀ : c₀ ∈ U.ids)
    (hc₀r : (U.block c₀).round = r + 2) :
    ∃ b, CommonAt U b r ∧ (U.block b).creator ∈ (Correct : Finset Validator) := by
  obtain ⟨bw, hbw, hbwr, hbwc, hbws⟩ := exists_common_correct_ancestor hc₀ hc₀r
  exact ⟨bw, ⟨hbw, hbwr, hbws⟩, hbwc⟩

/-- **Everyone holds a common block.** Any validator with a block two
rounds above has it in its own causal past. -/
theorem mem_history_of_commonAt {b c : BlockId} {r : ℕ}
    (hcom : CommonAt U b r) (hc : c ∈ U.ids) (hcr : (U.block c).round = r + 2) :
    b ∈ history U c :=
  (mem_history_iff hc).mpr (hcom.2.2 c hc hcr)

/-- **And everything it cites.** Cones nest, so a common block's
references — the very blocks a fill would copy — are in every later
validator's past too.

This is the statement the mechanism needs: the material a fill against
a common target reproduces is material its recipients already have. -/
theorem refs_mem_history_of_commonAt {b c : BlockId} {r : ℕ}
    (hcom : CommonAt U b r) (hc : c ∈ U.ids) (hcr : (U.block c).round = r + 2)
    {i : BlockId} (hi : i ∈ (U.block b).refs) :
    i ∈ history U c :=
  (mem_history_iff hc).mpr
    ((hcom.2.2 c hc hcr).tail hi)

/-- **I19 — a fill against a common donor line transmits nothing.**
Every reference the fill copies at a gap round lies in the causal past
of every validator holding a block two rounds above that round.

So the recipients need no blocks they lack: naming the target suffices,
and each reconstructs the filled blocks from its own DAG. The `prev`
reference is the recovering validator's own chain, supplied by the fill
itself, so the copied references are the whole of what would otherwise
have to be sent. -/
theorem fill_refs_available (sk : SkipMsg U)
    (hcom : ∀ k, sk.r0 < k → k ≤ sk.r → CommonAt U (sk.line k) k)
    {k : ℕ} (hk1 : sk.r0 < k) (hk2 : k ≤ sk.r)
    {c : BlockId} (hc : c ∈ U.ids) (hcr : (U.block c).round = k + 2)
    {i : BlockId} (hi : i ∈ (U.block (sk.line k)).refs) :
    i ∈ history U c :=
  refs_mem_history_of_commonAt (hcom k hk1 hk2) hc hcr hi

/-- The filled block's own references, split: the copied ones are
universally held (`fill_refs_available`), and the remaining one is the
self reference, which is the recovering validator's own block. -/
theorem fill_refs_eq (sk : SkipMsg U) {k : ℕ} :
    (sk.skipFill.block (sk.fresh k)).refs
      = insert (sk.prev k) (U.block (sk.line k)).refs := by
  rw [sk.skipFill_block_fresh]
  rfl

end Integration

end LeanDag
