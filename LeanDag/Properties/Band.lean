import LeanDag.Properties.Agreement
import LeanDag.Properties.Extends
import LeanDag.Properties.Derived.Persist
import LeanDag.Properties.Bounded
/-!
# The band a verdict reads

`docs/target-properties.md` §3.8. Locality and persistence are shadows
of one statement: given a verdict at slot `k`, there is a range of
rounds — from the slot's own round up to some finite top — such that
the blocks a view holds there already carry the verdict, and any
universe and view agreeing on that range decide the slot the same way.
The top is variable, since an indirect verdict's anchor may sit
arbitrarily high; what the property claims is that it exists.

`Derived/FromBand.lean` draws persistence, locality, view monotonicity
and the adaptive fixpoint's slot bound from one induction per protocol.
Truncation renumbers as well as restricts, which no agreement
hypothesis states, so `LocalTruncate` stays separate (`Truncate.lean`).
-/

namespace LeanDag

namespace Properties

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {R : DagRule Validator BlockId Payload}

/-- **`U'` carries `U`'s band, up to a shift.** Every block `U` holds
whose round lies in `[lo, hi]` once `g` is added is a block of `U'`, at
the round the shift names and with the same author, and above the floor
with the same references. The two offsets `g, g'` put both universes in
one frame of rounds; at `g = g' = 0` this is agreement on the nose, and
at `g = 0, g' = G` it is a truncation by `G`. Membership is
one-directional — `U'` may hold blocks `U` does not, as a fill does —
and the references clause stops at the floor, since a rule reads a vote
from a parent and a truncation empties the bottom layer's refs. -/
structure AgreeBand (R : DagRule Validator BlockId Payload) (U U' : R.Universe)
    (lo hi g g' : ℕ) : Prop where
  /-- A block of the band is a block of `U'`. -/
  mem : ∀ b, b ∈ R.ids U → lo ≤ (R.block U b).round + g →
    (R.block U b).round + g ≤ hi → b ∈ R.ids U'
  /-- A block sitting in the band on either side keeps its place in the
  common frame, and its author. -/
  block : ∀ b, b ∈ R.ids U →
    ((lo ≤ (R.block U b).round + g ∧ (R.block U b).round + g ≤ hi) ∨
      (b ∈ R.ids U' ∧ lo ≤ (R.block U' b).round + g' ∧
        (R.block U' b).round + g' ≤ hi)) →
    (R.block U' b).round + g' = (R.block U b).round + g ∧
      (R.block U' b).creator = (R.block U b).creator
  /-- Strictly above the floor, its references too. -/
  refs : ∀ b, b ∈ R.ids U → lo < (R.block U b).round + g →
    (R.block U b).round + g ≤ hi → (R.block U' b).refs = (R.block U b).refs

namespace AgreeBand

/-- A universe carries its own bands, at any offset. -/
theorem refl {U : R.Universe} {lo hi g : ℕ} : AgreeBand R U U lo hi g g where
  mem := fun _ hb _ _ => hb
  block := fun _ _ _ => ⟨rfl, rfl⟩
  refs := fun _ _ _ _ => rfl

/-- An extension carries every band, since it moves nothing. -/
theorem of_extends {U U' : R.Universe} (he : Extends R U U') (lo hi : ℕ) :
    AgreeBand R U U' lo hi 0 0 where
  mem := fun b hb _ _ => he.subset b hb
  block := fun b hb _ => by rw [he.block b hb]; exact ⟨rfl, rfl⟩
  refs := fun b hb _ _ => by rw [he.block b hb]

/-- Agreement above a round carries every band whose floor is at or
above it. -/
theorem of_agreeAbove {U U' : R.Universe} {r lo hi : ℕ} (h : AgreeAbove R U U' r)
    (hr : r ≤ lo) : AgreeBand R U U' lo hi 0 0 where
  mem := fun b hb hlo _ => ((h.mem b).mp ⟨hb, by omega⟩).1
  block := fun b hb hband => by
    have hU : r ≤ (R.block U b).round := by
      rcases hband with ⟨h1, -⟩ | ⟨hmem', h1, -⟩
      · omega
      · exact ((h.mem b).mpr ⟨hmem', by omega⟩).2
    have hr := h.round b hb hU
    exact ⟨by omega, h.creator b hb hU⟩
  refs := fun b hb hlo _ => h.refs b hb (by omega)

/-- Agreement on a band gives agreement on any narrower one. -/
theorem mono {U U' : R.Universe} {lo hi lo' hi' g g' : ℕ} (h : AgreeBand R U U' lo hi g g')
    (hlo : lo ≤ lo') (hhi : hi' ≤ hi) : AgreeBand R U U' lo' hi' g g' where
  mem := fun b hb h1 h2 => h.mem b hb (by omega) (by omega)
  block := fun b hb hband => by
    refine h.block b hb ?_
    rcases hband with ⟨h1, h2⟩ | ⟨hm, h1, h2⟩
    · exact Or.inl ⟨by omega, by omega⟩
    · exact Or.inr ⟨hm, by omega, by omega⟩
  refs := fun b hb h1 h2 => h.refs b hb (by omega) (by omega)

variable {U U' : R.Universe} {lo hi g g' : ℕ}

/-- **Causal history inside the band is the same history.** The floor is
included: a path *into* it reads the layer above, which the band
preserves, even though the floor's own references need not be
preserved. Mahi-Mahi needs exactly this, its votes reading a cone at
the slot's propose round, the floor itself. -/
theorem reaches_of (h : AgreeBand R U U' lo hi g g')
    {A : BlockId} (hA : A ∈ R.ids U) (hAhi : (R.block U A).round + g ≤ hi) :
    ∀ {C : BlockId}, ReachesFrom (R.block U) A C → lo ≤ (R.block U C).round + g →
      ReachesFrom (R.block U') A C := by
  intro C hre
  induction hre with
  | refl => intro _; exact Relation.ReflTransGen.refl
  | @tail b c hAb hstep ih =>
      intro hcr
      have hb : b ∈ R.ids U := (R.causal U).mem_ids_of_reaches hA hAb
      have hstep' : c ∈ (R.block U b).refs := hstep
      have hround := (R.causal U).refs_round b hb c hstep'
      have hbhi : (R.block U b).round + g ≤ hi := by
        have := (R.causal U).round_le_of_reaches hA hAb
        omega
      refine (ih (by omega)).tail ?_
      show c ∈ (R.block U' b).refs
      rw [h.refs b hb (by omega) hbhi]
      exact hstep'

/-- **And a path of `U'` that stays above the floor is a path of `U`.** -/
theorem reaches_old (h : AgreeBand R U U' lo hi g g')
    {A : BlockId} (hA : A ∈ R.ids U) (hAlo : lo ≤ (R.block U A).round + g)
    (hAhi : (R.block U A).round + g ≤ hi) :
    ∀ {C : BlockId}, ReachesFrom (R.block U') A C →
      lo ≤ (R.block U' C).round + g' →
      C ∈ R.ids U ∧ ReachesFrom (R.block U) A C ∧
        (R.block U C).round + g = (R.block U' C).round + g' := by
  intro C hre
  induction hre with
  | refl =>
      intro _
      exact ⟨hA, Relation.ReflTransGen.refl, (h.block A hA (Or.inl ⟨hAlo, hAhi⟩)).1.symm⟩
  | @tail b c hAb hstep ih =>
      intro hcr
      have hstep' : c ∈ (R.block U' b).refs := hstep
      have hbU' : b ∈ R.ids U' :=
        (R.causal U').mem_ids_of_reaches (h.mem A hA hAlo hAhi) hAb
      have hround' := (R.causal U').refs_round b hbU' c hstep'
      obtain ⟨hbU, hbre, hbeq⟩ := ih (by omega)
      have hbhi : (R.block U b).round + g ≤ hi := by
        have := (R.causal U).round_le_of_reaches hA hbre
        omega
      have hrefs : (R.block U' b).refs = (R.block U b).refs :=
        h.refs b hbU (by omega) hbhi
      rw [hrefs] at hstep'
      have hroundU := (R.causal U).refs_round b hbU c hstep'
      exact ⟨(R.causal U).complete b hbU c hstep', hbre.tail hstep', by omega⟩

/-! ## Reading a band, at any carrier

Five projections every rule's band proof needs: three are the
structure's own fields, and the two that matter are that a round layer
lands on the layer the shift names, and a set inside the band keeps its
authors. -/

variable {U U' : R.Universe} {lo hi g g' : ℕ}

/-- A block inside the band is a block of the other universe. -/
theorem mem_band (h : AgreeBand R U U' lo hi g g') {b : BlockId}
    (hb : b ∈ R.ids U) (h1 : lo ≤ (R.block U b).round + g)
    (h2 : (R.block U b).round + g ≤ hi) : b ∈ R.ids U' := h.mem b hb h1 h2

/-- At the shifted round, with the author it had. -/
theorem block_band (h : AgreeBand R U U' lo hi g g') {b : BlockId}
    (hb : b ∈ R.ids U) (h1 : lo ≤ (R.block U b).round + g)
    (h2 : (R.block U b).round + g ≤ hi) :
    (R.block U' b).round + g' = (R.block U b).round + g ∧
      (R.block U' b).creator = (R.block U b).creator :=
  h.block b hb (Or.inl ⟨h1, h2⟩)

/-- The same, read from the other side: a block the shift already
placed inside the band. -/
theorem block_band' (h : AgreeBand R U U' lo hi g g') {b : BlockId}
    (hb : b ∈ R.ids U) (hb' : b ∈ R.ids U')
    (h1 : lo ≤ (R.block U' b).round + g') (h2 : (R.block U' b).round + g' ≤ hi) :
    (R.block U' b).round + g' = (R.block U b).round + g ∧
      (R.block U' b).creator = (R.block U b).creator :=
  h.block b hb (Or.inr ⟨hb', h1, h2⟩)

/-- And, strictly above the floor, referencing what it referenced. -/
theorem refs_band (h : AgreeBand R U U' lo hi g g') {b : BlockId}
    (hb : b ∈ R.ids U) (h1 : lo < (R.block U b).round + g)
    (h2 : (R.block U b).round + g ≤ hi) :
    (R.block U' b).refs = (R.block U b).refs := h.refs b hb h1 h2

/-- **A round layer lands on the layer the shift names.** Stated over the
filter rather than over any protocol's `blocksAt`, which is that filter
under a name. -/
theorem layer_band (h : AgreeBand R U U' lo hi g g') {r r' : ℕ}
    (hrr : r + g = r' + g') (h1 : lo ≤ r + g) (h2 : r + g ≤ hi) :
    (R.ids U).filter (fun b => (R.block U b).round = r) ⊆
      (R.ids U').filter (fun b => (R.block U' b).round = r') := by
  intro b hb
  rw [Finset.mem_filter] at hb ⊢
  have hbb := block_band h hb.1 (by omega) (by omega)
  exact ⟨mem_band h hb.1 (by omega) (by omega), by omega⟩

/-- **And a set inside the band has the authors it had.** -/
theorem creators_band (h : AgreeBand R U U' lo hi g g') {s : Finset BlockId}
    (hs : ∀ b ∈ s, b ∈ R.ids U ∧ lo ≤ (R.block U b).round + g ∧
      (R.block U b).round + g ≤ hi) :
    s.image (fun i => (R.block U' i).creator) = s.image (fun i => (R.block U i).creator) :=
  Finset.image_congr fun i hi' => (block_band h (hs i hi').1 (hs i hi').2.1 (hs i hi').2.2).2

end AgreeBand

/-- **Every verdict reads a band of rounds.** From the slot's own round
up to some top, the blocks the view holds and the leaders of the slots
sitting there already carry the verdict: any universe carrying the band
up to a shift, any view holding those blocks, and any schedule whose
slots correspond and whose leaders match inside the band, decides the
corresponding slot the same way. `g, g'` put the two universes in one
frame of rounds and `d, d'` the two schedules in one frame of slots
(slot `m` of `S` answering to `m'` of `S'` when `m + d' = m' + d`); all
four are zero for persistence, locality and view monotonicity, and a
truncation by `G` from base slot `d` uses `g = 0, g' = G, d' = 0`. -/
def Banded (R : DagRule Validator BlockId Payload) : Prop :=
  ∀ (S : Slots Validator) (U : R.Universe) (V : R.View U) (k : ℕ) (v : Option BlockId),
    R.Decided S V k v →
      ∃ top : ℕ, ∀ (g g' d d' : ℕ) (S' : Slots Validator) (U' : R.Universe)
        (V' : R.View U') (k' : ℕ),
        k + d' = k' + d →
        (∀ m m', m + d' = m' + d → S.slotRound m + g = S'.slotRound m' + g') →
        (∀ m m', m + d' = m' + d → S.slotRound m ≤ top → S.leader m = S'.leader m') →
        AgreeBand R U U' (S.slotRound k + g) (top + g) g g' →
        (∀ b, b ∈ R.viewIds V → S.slotRound k ≤ (R.block U b).round →
          (R.block U b).round ≤ top → b ∈ R.viewIds V') →
        R.Decided S' V' k' v

end Properties

end LeanDag
