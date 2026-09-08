import LeanDag.Integration.Retention
import LeanDag.GC.Horizon
import LeanDag.Properties.Compose
import LeanDag.Common.Record.Genesis
import LeanDag.Properties.Arcs.GC
import LeanDag.Mysticeti.Record
/-!
# Re-genesis: restarting a severed chain at the cut

`severed_of_pruned_anchor` showed that a validator whose whole history
fell below a horizon can produce nothing in the truncation, since P3′
demands a self-parent it no longer has. The repair is to let it start a
fresh chain at the cut with a reference-free block, which needs no new
justification: `chop`'s own validity proof already discharges a
reference-free block at round 0, and the very absence that stranded the
validator is what makes the new block unambiguous against
non-equivocation. The one condition this carries is that a re-genesis
block is valid in the truncation and not in the original universe, so
it is acceptable only to validators that have themselves pruned to at
least the same horizon (`integration.md` §3.3).
-/

namespace LeanDag

namespace Integration

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}

/-! **Re-genesis** — a universe extended with one reference-free block at
round `0`, for a validator that has none — is the block record's
(`Record/Genesis.lean`). -/
export BlockRecord (addGenesis addGenesis_block_old addGenesis_block_new mem_addGenesis)

variable {V : BlockUniverse Validator BlockId Payload} {v : Validator}
variable {g : BlockId} {p : Payload}

/-! ## Re-genesis through the properties: two witnesses and nothing
else — `Extends` because re-genesis only adds a block, and `Sustains`
from round one because the block it adds sits at round zero. -/

section Properties

variable {hg : g ∉ V.ids} {hsev : ∀ b ∈ V.ids, (V.block b).creator ≠ v}

/-- **Re-genesis is an extension.** It adds one block and touches no
other. -/
theorem extends_addGenesis :
    Properties.Extends (MysticetiProperties.mysticetiRule (Payload := Payload))
      V (addGenesis V v g p hg hsev) :=
  MysticetiProperties.onRecord.extends_addGenesis (U := V) (v := v) (g := g) (p := p)
    (hg := hg) (hsev := hsev)

/-- **And it rebases from round one at no offset.** The block it adds
sits at round zero, so at and above round one the two universes hold
the same blocks. -/
theorem sustains_addGenesis :
    Properties.Sustains (MysticetiProperties.mysticetiRule (Payload := Payload))
      V (addGenesis V v g p hg hsev) 0 1 :=
  MysticetiProperties.onRecord.sustains_addGenesis (U := V) (v := v) (g := g) (p := p)
    (hg := hg) (hsev := hsev)

theorem decided_addGenesis [S : Slots Validator]
    {W : View Validator BlockId Payload V}
    {W' : View Validator BlockId Payload (addGenesis V v g p hg hsev)}
    (hsub : W.ids ⊆ W'.ids) {k : ℕ} {u : Option BlockId}
    (h : Decided V W k u) :
    Decided (addGenesis V v g p hg hsev) W' k u :=
  MysticetiProperties.persist S V _ extends_addGenesis W W' hsub k u h

end Properties

/-- **The chain restarts.** After re-genesis the stranded validator has
a block at round `0`, so it is no longer severed, and an ordinary Safe
Skip anchored on the new block fills the rounds above. -/
theorem populatedOn_addGenesis {hg : g ∉ V.ids}
    {hsev : ∀ b ∈ V.ids, (V.block b).creator ≠ v} {T : Finset Validator}
    (hpop : PopulatedOn V T 0) :
    PopulatedOn (addGenesis V v g p hg hsev) (insert v T) 0 :=
  MysticetiProperties.populatedOn_toCore
    (Properties.populatedOn_insert_of_extends extends_addGenesis
      (fun w hw => by
        obtain rfl := Finset.mem_singleton.mp hw
        refine ⟨g, mem_addGenesis (v := w) (p := p) (hg := hg) (hsev := hsev), ?_, ?_⟩
        · show ((addGenesis V w g p hg hsev).block g).creator = w
          rw [addGenesis_block_new]
        · show ((addGenesis V w g p hg hsev).block g).round = 0
          rw [addGenesis_block_new])
      (MysticetiProperties.populatedOn_ofCore hpop))

/-- Re-genesis is available exactly to a stranded validator: the
absence hypothesis it needs is what `severed_of_pruned_anchor`
supplies. -/
def addGenesis_of_severed {U : BlockUniverse Validator BlockId Payload}
    {G : ℕ} (sk : SkipMsg U) (hG1 : sk.r0 < G) (hG2 : G ≤ sk.r)
    (g : BlockId) (p : Payload) (hg : g ∉ (chop U G).ids) :
    BlockUniverse Validator BlockId Payload :=
  addGenesis (chop U G) sk.v1 g p hg (severed_of_pruned_anchor sk hG1 hG2)

/-! ## I20 — the cut derives the genesis the fill already built: fill
first and truncate afterwards, with the horizon inside the gap, and
`chopBlock` rebases `v1`'s round-`G` block to a reference-free round-`0`
block — a genesis block with the identifier the message already
allocated. So the two routes agree with no fresh identifier needed. -/

section CutGenesis

variable {U : BlockUniverse Validator BlockId Payload} (sk : SkipMsg U) {G : ℕ}

/-- **The cut turns the boundary fill block into a genesis block.** At a
horizon inside the gap, `v1`'s filled block at round `G` is retained,
rebased to round `0`, and stripped of its references. -/
theorem stack_block_fresh_horizon (hG1 : sk.r0 < G) (hG2 : G ≤ sk.r) :
    sk.fresh G ∈ (chop sk.skipFill G).ids ∧
      (chop sk.skipFill G).block (sk.fresh G) =
        ⟨0, sk.v1, ∅, (U.block (sk.line G)).payload⟩ := by
  have hmem : sk.fresh G ∈ sk.skipFill.ids :=
    Finset.mem_union_right _ (sk.mem_freshIds.mpr ⟨G, hG1, hG2, rfl⟩)
  have hround : (sk.skipFill.block (sk.fresh G)).round = G := by
    rw [sk.skipFill_block_fresh]; rfl
  refine ⟨mem_chop_ids.mpr ⟨hmem, by omega⟩, ?_⟩
  rw [chop_block]
  unfold chopBlk
  rw [sk.skipFill_block_fresh]
  simp only [SkipData.fillBlock, le_refl, if_pos, Nat.sub_self]

/-- **Re-genesis adds nothing the truncated fill lacks.** Every block of
the re-genesis universe over `chop U G` is present in `chop sk.skipFill G`,
with the same content. -/
theorem addGenesis_sub_stack (hG1 : sk.r0 < G) (hG2 : G ≤ sk.r)
    (hg : sk.fresh G ∉ (chop U G).ids)
    (hsev : ∀ b ∈ (chop U G).ids, ((chop U G).block b).creator ≠ sk.v1) :
    ∀ b ∈ (addGenesis (chop U G) sk.v1 (sk.fresh G)
            (U.block (sk.line G)).payload hg hsev).ids,
      b ∈ (chop sk.skipFill G).ids ∧
        (chop sk.skipFill G).block b
          = (addGenesis (chop U G) sk.v1 (sk.fresh G)
              (U.block (sk.line G)).payload hg hsev).block b := by
  obtain ⟨hfmem, hfblk⟩ := stack_block_fresh_horizon sk hG1 hG2
  intro b hb
  rcases Finset.mem_insert.mp hb with rfl | hbo
  · exact ⟨hfmem, by rw [hfblk, addGenesis_block_new]⟩
  · -- an old block: the fill leaves it alone, so both cuts agree on it
    obtain ⟨hbU, hbr⟩ := mem_chop_ids.mp hbo
    have hfill : sk.skipFill.block b = U.block b := sk.skipFill_block_old hbU
    refine ⟨mem_chop_ids.mpr ⟨Finset.mem_union_left _ hbU, by rw [hfill]; exact hbr⟩, ?_⟩
    rw [addGenesis_block_old hbo, chop_block, chop_block]
    unfold chopBlk
    rw [hfill]

/-- **A restart is a genesis block, necessarily.** If a validator has any
block at all in a universe, it has one at round `0` with no references. So
a validator absent from `V` can be returned to production only by an
extension carrying exactly the block `addGenesis` supplies. -/
theorem genesis_forced {W : BlockUniverse Validator BlockId Payload}
    {v : Validator} {b : BlockId} (hb : b ∈ W.ids) (hbc : (W.block b).creator = v) :
    ∃ g ∈ W.ids, (W.block g).creator = v ∧ (W.block g).round = 0 ∧
      (W.block g).refs = ∅ := by
  by_contra hcon
  simp only [not_exists, not_and] at hcon
  have hgen : ∀ c ∈ W.ids, (W.block c).creator = v → (W.block c).round ≠ 0 := by
    intro c hc hcc hr0
    exact hcon c hc hcc hr0 (W.causal.refs_empty_of_round_zero hc hr0)
  exact no_blocks_of_no_genesis hgen b hb hbc

end CutGenesis

/-! ## I19 — the exposure condition survives re-genesis: the re-genesis
block has no references at all, so it cannot cite an exposed author and
enters no other block's cone. `DoSValid` is untouched in both
directions, the sharpest contrast with the fill's `fillBlock`, whose
self reference enlarges the cone (I1). -/

section Exposure

variable {V : BlockUniverse Validator BlockId Payload} {v : Validator}
variable {g : BlockId} {p : Payload}
variable {hg : g ∉ V.ids} {hsev : ∀ b ∈ V.ids, (V.block b).creator ≠ v}

/-- Reachability is unchanged among old blocks: the new block
references nothing, and nothing references it. -/
theorem reaches_addGenesis {b i : BlockId} (hb : b ∈ V.ids) :
    Reaches (addGenesis V v g p hg hsev) b i ↔ Reaches V b i :=
  Properties.Extends.reaches_iff (extends_addGenesis (v := v) (g := g) (p := p) (hg := hg) (hsev := hsev)) hb

/-- Cones are unchanged, so every cone-based condition reads the same. -/
theorem history_addGenesis {b : BlockId} (hb : b ∈ V.ids) :
    history (addGenesis V v g p hg hsev) b = history V b := by
  ext i
  rw [mem_history_iff (Finset.mem_insert_of_mem hb), mem_history_iff hb]
  exact reaches_addGenesis hb

/-- **I19a.** Re-genesis preserves the exposure condition. A block with
no references can neither cite an exposed author nor enlarge anyone
else's cone. -/
theorem dosValid_addGenesis (hdos : DoSValid V) :
    DoSValid (addGenesis V v g p hg hsev) := by
  intro b hb i hi hexp
  rcases Finset.mem_insert.mp hb with rfl | ho
  · -- the new block references nothing
    rw [addGenesis_block_new] at hi
    exact absurd hi (Finset.notMem_empty i)
  · -- an old block: its cone, and every block in it, reads as before
    rw [addGenesis_block_old ho] at hi
    obtain ⟨x, hx, y, hy, hxy⟩ := hexp
    rw [history_addGenesis ho] at hx hy
    refine hdos b ho i hi ⟨x, hx, y, hy, ?_⟩
    obtain ⟨hne, hxc, hyc, hr⟩ := hxy
    have hxo : x ∈ V.ids := mem_ids_of_reaches ho ((mem_history_iff ho).mp hx)
    have hyo : y ∈ V.ids := mem_ids_of_reaches ho ((mem_history_iff ho).mp hy)
    rw [addGenesis_block_old hxo] at hxc hr
    rw [addGenesis_block_old hyo] at hyc hr
    rw [addGenesis_block_old (V.complete b ho i hi)] at *
    exact ⟨hne, hxc, hyc, hr⟩

end Exposure

/-! ## Convergence: local derivation needs no agreement. If each
validator synthesises a genesis for any absent validator as a
deterministic function of its own horizon, nothing is sent and nothing
can be rejected — the derivations converge, since a further-truncating
validator's own derived genesis is pruned by the cut, leaving exactly
the same base the same derivation runs on. -/

section Convergence

variable {V : BlockUniverse Validator BlockId Payload} {v : Validator}
variable {g : BlockId} {p : Payload} {d : ℕ}

/-- **A derived genesis is pruned by the next cut, without trace.** Any
further truncation removes the round-`0` block and leaves the ordinary
truncation of what lay beneath. -/
theorem chop_addGenesis (hd : 0 < d)
    {hg : g ∉ V.ids} {hsev : ∀ b ∈ V.ids, (V.block b).creator ≠ v} :
    (chop (addGenesis V v g p hg hsev) d).ids = (chop V d).ids
      ∧ ∀ b ∈ (chop V d).ids,
          (chop (addGenesis V v g p hg hsev) d).block b = (chop V d).block b := by
  constructor
  · ext b
    rw [mem_chop_ids, mem_chop_ids]
    constructor
    · rintro ⟨hb, hbr⟩
      rcases Finset.mem_insert.mp hb with rfl | ho
      · rw [addGenesis_block_new] at hbr
        change d ≤ 0 at hbr
        omega
      · rw [addGenesis_block_old ho] at hbr
        exact ⟨ho, hbr⟩
    · rintro ⟨hb, hbr⟩
      exact ⟨Finset.mem_insert_of_mem hb, by rw [addGenesis_block_old hb]; exact hbr⟩
  · intro b hb
    rw [mem_chop_ids] at hb
    simp only [chop_block, chopBlk, addGenesis_block_old hb.1]

/-- **The convergence.** A validator at horizon `G₁`, truncating on to a
later horizon `G₂`, holds exactly the blocks of a validator that cut at
`G₂` directly. -/
theorem regenesis_converges {U : BlockUniverse Validator BlockId Payload}
    {G₁ G₂ : ℕ} (hG : G₁ < G₂)
    {hg : g ∉ (chop U G₁).ids}
    {hsev : ∀ b ∈ (chop U G₁).ids, ((chop U G₁).block b).creator ≠ v} :
    (chop (addGenesis (chop U G₁) v g p hg hsev) (G₂ - G₁)).ids
        = (chop U G₂).ids
      ∧ ∀ b ∈ (chop U G₂).ids,
          (chop (addGenesis (chop U G₁) v g p hg hsev) (G₂ - G₁)).block b
            = (chop U G₂).block b := by
  obtain ⟨hids, hblk⟩ := chop_addGenesis (V := chop U G₁) (v := v) (g := g)
    (p := p) (d := G₂ - G₁) (by omega) (hg := hg) (hsev := hsev)
  rw [chop_chop (le_of_lt hG)] at hids hblk
  exact ⟨hids, hblk⟩

end Convergence

/-! ## Re-genesis and Safe Skip compose: the full recovery. A long
outage uses all three mechanisms in order: bootstrap to read
(`bootstrap_agree`), re-genesis to write (`addGenesis`), Safe Skip to
catch up, anchored on the re-genesis block. `hsev`, the total absence
that licensed re-genesis, is exactly what discharges `hB1uniq`. -/

section Recovery

variable {V : BlockUniverse Validator BlockId Payload} {v : Validator}
variable {g : BlockId} {p : Payload}
variable {hg : g ∉ V.ids} {hsev : ∀ b ∈ V.ids, (V.block b).creator ≠ v}

/-- **The re-genesis block is a lawful Safe Skip anchor.** Uniqueness at
its round is immediate from the absence that licensed it. -/
theorem hB1uniq_of_addGenesis :
    ∀ j ∈ (addGenesis V v g p hg hsev).ids,
      ((addGenesis V v g p hg hsev).block j).creator = v →
      ((addGenesis V v g p hg hsev).block j).round
        = ((addGenesis V v g p hg hsev).block g).round → j = g := by
  intro j hj hjc _
  rcases Finset.mem_insert.mp hj with rfl | ho
  · rfl
  · rw [addGenesis_block_old ho] at hjc
    exact absurd hjc (hsev j ho)

/-- **The catch-up fill.** After re-genesis the returning validator
rejoins production with one message: a `SkipMsg` anchored on its new
genesis block, filling every round from the cut to the target. -/
def recoveryMsg (r : ℕ) (line fresh : ℕ → BlockId) (idx : BlockId → ℕ)
    (v2 : Validator) (hv12 : v ≠ v2)
    (hline_mem : ∀ k, k ≤ r → line k ∈ V.ids)
    (hline_creator : ∀ k, k ≤ r → (V.block (line k)).creator = v2)
    (hline_round : ∀ k, k ≤ r →
      (V.block (line k)).round = ((addGenesis V v g p hg hsev).block g).round + k)
    (hline_chain : ∀ k, 0 < k → k ≤ r → line (k - 1) ∈ (V.block (line k)).refs)
    (hfresh_new : ∀ k, fresh k ∉ (addGenesis V v g p hg hsev).ids)
    (hidx : ∀ k, idx (fresh k) = k) :
    SkipMsg (addGenesis V v g p hg hsev) where
  v1 := v
  B1 := g
  v2 := v2
  r := ((addGenesis V v g p hg hsev).block g).round + r
  line k := line (k - ((addGenesis V v g p hg hsev).block g).round)
  fresh := fresh
  idx := idx
  hB1uniq := hB1uniq_of_addGenesis
  hv12 := hv12
  hB1 := mem_addGenesis
  hB1c := by rw [addGenesis_block_new]
  hline_mem := by
    intro k hk1 hk2
    exact Finset.mem_insert_of_mem (hline_mem _ (by omega))
  hline_creator := by
    intro k hk1 hk2
    rw [addGenesis_block_old (hline_mem _ (by omega))]
    exact hline_creator _ (by omega)
  hline_round := by
    intro k hk1 hk2
    rw [addGenesis_block_old (hline_mem _ (by omega))]
    rw [hline_round _ (by omega)]
    omega
  hline_chain := by
    intro k hk1 hk2
    rw [addGenesis_block_old (hline_mem _ (by omega))]
    have := hline_chain (k - ((addGenesis V v g p hg hsev).block g).round)
      (by omega) (by omega)
    have hidx' : k - ((addGenesis V v g p hg hsev).block g).round - 1
        = k - 1 - ((addGenesis V v g p hg hsev).block g).round := by omega
    rwa [hidx'] at this
  hfresh_new := hfresh_new
  hidx := hidx
  hgap := by
    intro b hb hbc _ _
    rcases Finset.mem_insert.mp hb with rfl | ho
    · rw [addGenesis_block_new] at *
      omega
    · rw [addGenesis_block_old ho] at hbc
      exact absurd hbc (hsev b ho)

/-! ### Rejoining from the truncated universe alone: given the
truncation, a donor line inside it, and fresh identifiers, the
returning validator obtains a block at every round from `0` to the
target, checkable with the history a recipient retains. -/
theorem rejoin_populated (msg : SkipMsg (addGenesis V v g p hg hsev))
    (hB1 : msg.B1 = g) :
    ∀ k ≤ msg.r, ∃ b ∈ msg.skipFill.ids,
      (msg.skipFill.block b).creator = v ∧ (msg.skipFill.block b).round = k := by
  have hr0 : msg.r0 = 0 := by
    show ((addGenesis V v g p hg hsev).block msg.B1).round = 0
    rw [hB1, addGenesis_block_new]
  have hv : msg.v1 = v := by
    have h := msg.hB1c
    rw [hB1, addGenesis_block_new] at h
    exact h.symm
  intro k hk
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · refine ⟨g, Finset.mem_union_left _ mem_addGenesis, ?_, ?_⟩
    · rw [msg.skipFill_block_old mem_addGenesis, addGenesis_block_new]
    · rw [msg.skipFill_block_old mem_addGenesis, addGenesis_block_new]
  · refine ⟨msg.fresh k,
      Finset.mem_union_right _ (msg.mem_freshIds.mpr ⟨k, by omega, hk, rfl⟩), ?_, ?_⟩
    · rw [msg.skipFill_block_fresh]
      show msg.v1 = v
      exact hv
    · rw [msg.skipFill_block_fresh]
      rfl

end Recovery

end Integration

end LeanDag
