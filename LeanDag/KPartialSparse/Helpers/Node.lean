import LeanDag.KPartialSparse.Model.Node
import LeanDag.KPartialSparse.Helpers.Rule
import LeanDag.KPartialDag.Helpers.Node
/-!
# Sparse K-partial DAG — what a node reads, helpers

`docs/kpartial-sparse.md` §5. The node's tests read only what it holds
(`AnchoredIn.congr`, `linkedIn_congr`, `fetchedIn_congr`); the sub-DAG read
on `H` lies in the record's (`availIn_subset`), and fetched down to a round it
is the record's above that round (`avail_subset_availIn`); holding the
sub-DAG fetches it (`fetchedIn_of_subset`); and a node's decisions are the
commit rule's (`NodeDecided.decided`) and agree (`NodeDecided.agree`).
-/

namespace LeanDag

namespace KPartialSparse

open KPartialDag Scheme

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator] [F : Faults Validator]
variable [Cr : Crashes Validator] [Ld : Leaders Validator]
variable {BlockId : Type*} [LinearOrder BlockId] {Payload : Type*}
variable {U U' : SRecord Validator BlockId Payload} {K : ℕ} {H : Finset BlockId} {A : BlockId}

/-! ## Reading only what is held

Two records agree on `H` when they give the blocks of `H` alike and the
references of those blocks the same rounds (`hr`): a reference names its round. -/

section WindowFrom

variable {blk blk' : BlockId → Block Validator BlockId Payload}

omit [Fintype Validator] [DecidableEq Validator] Ld in
/-- One step beyond a held window is read alike. -/
theorem windowFrom_succ_eq (hb : ∀ i ∈ H, blk i = blk' i)
    (hr : ∀ i ∈ H, ∀ j ∈ (blk i).refs, (blk' j).round = (blk j).round) :
    ∀ (n lo : ℕ) (b : BlockId), windowFrom blk n lo b ⊆ H →
      windowFrom blk' (n + 1) lo b = windowFrom blk (n + 1) lo b := by
  intro n
  induction n with
  | zero =>
    intro lo b h
    have hbH : b ∈ H := h mem_windowFrom_self
    have hf : ((blk' b).refs.filter fun j => lo ≤ (blk' j).round) =
        (blk b).refs.filter fun j => lo ≤ (blk j).round := by
      rw [← hb b hbH]; exact Finset.filter_congr fun j hj => by rw [hr b hbH j hj]
    simp only [windowFrom, hf]
  | succ n ih =>
    intro lo b h
    have hbH : b ∈ H := h mem_windowFrom_self
    have hf : ((blk' b).refs.filter fun j => lo ≤ (blk' j).round) =
        (blk b).refs.filter fun j => lo ≤ (blk j).round := by
      rw [← hb b hbH]; exact Finset.filter_congr fun j hj => by rw [hr b hbH j hj]
    change insert b (((blk' b).refs.filter fun j => lo ≤ (blk' j).round).biUnion
      (windowFrom blk' (n + 1) lo)) =
      insert b (((blk b).refs.filter fun j => lo ≤ (blk j).round).biUnion
        (windowFrom blk (n + 1) lo))
    rw [hf]
    refine congrArg (insert b) (Finset.biUnion_congr rfl fun j hj => ih lo j fun z hz => h ?_)
    obtain ⟨hj, hjr⟩ := Finset.mem_filter.mp hj
    exact mem_windowFrom_succ.mpr (Or.inr ⟨j, hj, hjr, hz⟩)

omit [Fintype Validator] [DecidableEq Validator] Ld in
/-- A held window is read alike. -/
theorem windowFrom_eq_of_subset (hb : ∀ i ∈ H, blk i = blk' i)
    (hr : ∀ i ∈ H, ∀ j ∈ (blk i).refs, (blk' j).round = (blk j).round) :
    ∀ (n lo : ℕ) (b : BlockId), windowFrom blk n lo b ⊆ H →
      windowFrom blk' n lo b = windowFrom blk n lo b
  | 0, _, _, _ => rfl
  | n + 1, lo, b, h => windowFrom_succ_eq hb hr n lo b
      ((windowFrom_mono (by omega) le_rfl b).trans h)

end WindowFrom

variable (hb : ∀ i ∈ H, U.block i = U'.block i)
  (hr : ∀ i ∈ H, ∀ j ∈ (U.block i).refs, (U'.block j).round = (U.block j).round)

include hb hr

/-- A held window of a record is read alike on a record agreeing on what is
held. -/
theorem window_eq_of_subset {n : ℕ} {y : BlockId} (h : window U n y ⊆ H) :
    window U' n y = window U n y := by
  unfold window
  rw [← hb y (h self_mem_window)]
  exact windowFrom_eq_of_subset hb hr n _ y h

/-- A held interior is read alike. -/
theorem interior_eq_of_subset {i : ℕ} {b : BlockId} (hbH : b ∈ H) (h : interior U i b ⊆ H) :
    interior U' i b = interior U i b := by
  unfold interior
  rw [← hb b hbH]
  exact windowFrom_eq_of_subset hb hr _ _ b h

/-- **A block reached through a held interior is read alike**: the window to
depth `i` of a block whose interior is held. -/
theorem window_eq_of_path {i : ℕ} {b : BlockId} (hbH : b ∈ H) (h : 0 < i → interior U i b ⊆ H) :
    window U' i b = window U i b := by
  rcases Nat.eq_zero_or_pos i with rfl | hpos
  · rfl
  · obtain ⟨n, rfl⟩ : ∃ n, i = n + 1 := ⟨i - 1, by omega⟩
    unfold window
    rw [← hb b hbH]
    exact windowFrom_succ_eq hb hr n _ b (h hpos)

omit hb hr

/-- An anchor point read on `H` has the window it brings held. -/
theorem AnchoredIn.window {y : BlockId} {d : ℕ} (h : AnchoredIn U K H A y d) :
    window U d y ⊆ H := by
  cases h with
  | anchor h => exact h
  | reached _ _ _ _ _ _ _ _ _ _ _ _ _ _ hx => exact hx

/-- The sub-DAG read on `H` is held. -/
theorem availIn_subset_held {z : BlockId} (hz : z ∈ AvailIn U K H A) : z ∈ H := by
  obtain ⟨y, d, hy, hzy⟩ := hz
  exact hy.window hzy

include hb hr

/-- **Anchoring read on `H` reads only `H`.** -/
theorem AnchoredIn.congr {x : BlockId} {d : ℕ}
    (h : AnchoredIn U K H A x d) : AnchoredIn U' K H A x d := by
  induction h with
  | anchor h => exact AnchoredIn.anchor (by rw [window_eq_of_subset hb hr h]; exact h)
  | @reached x i S m y d y' d' hy hz hy' hmz hi hm hcard hx ih ih' =>
    have hzH : ∀ z ∈ S, z ∈ H := fun z hzS => (hy z hzS).window (hz z hzS)
    have hpath : ∀ z ∈ S, 0 < i → interior U i (m z) ⊆ H := fun z hzS hpos =>
      (hmz z hzS hpos).trans (hy' z hzS hpos).window
    have hmH : ∀ z ∈ S, 0 < i → m z ∈ H := fun z hzS hpos => hpath z hzS hpos mem_windowFrom_self
    refine AnchoredIn.reached i S m y d y' d' ih (fun z hzS => ?_) ih' (fun z hzS hpos => ?_) hi
      (fun z hzS => ?_) ?_ ?_
    · rw [window_eq_of_subset hb hr ((hy z hzS).window)]; exact hz z hzS
    · rw [window_eq_of_subset hb hr ((hy' z hzS hpos).window),
        interior_eq_of_subset hb hr (hmH z hzS hpos) (hpath z hzS hpos)]
      exact hmz z hzS hpos
    · have hz' := hb z (hzH z hzS)
      have hmr := hr z (hzH z hzS) (m z) (hm z hzS).1
      refine ⟨hz' ▸ (hm z hzS).1, ?_, by rw [hmr, ← hz']; exact (hm z hzS).2.2⟩
      rcases Nat.eq_zero_or_pos i with rfl | hpos
      · rw [mem_window_zero (hm z hzS).2.1]; exact self_mem_window
      · rw [window_eq_of_path hb hr (hmH z hzS hpos) (fun _ => hpath z hzS hpos)]
        exact (hm z hzS).2.1
    · have : creatorsOf U'.block S = creatorsOf U.block S :=
        Finset.image_congr fun z hzS => by rw [hb z (hzH z hzS)]
      rw [this]; exact hcard
    · rw [window_eq_of_subset hb hr hx]; exact hx

omit hb hr

/-- The sub-DAG read on `H` is read alike on a record agreeing on `H`. -/
theorem availIn_congr (hb : ∀ i ∈ H, U.block i = U'.block i)
    (hr : ∀ i ∈ H, ∀ j ∈ (U.block i).refs, (U'.block j).round = (U.block j).round) :
    AvailIn U K H A = AvailIn U' K H A := by
  have hb' : ∀ i ∈ H, U'.block i = U.block i := fun i hi => (hb i hi).symm
  have hr' : ∀ i ∈ H, ∀ j ∈ (U'.block i).refs, (U.block j).round = (U'.block j).round :=
    fun i hi j hj => (hr i hi j (hb i hi ▸ hj)).symm
  ext z
  constructor
  · rintro ⟨y, d, hy, hzy⟩
    exact ⟨y, d, hy.congr hb hr, by rw [window_eq_of_subset hb hr hy.window]; exact hzy⟩
  · rintro ⟨y, d, hy, hzy⟩
    exact ⟨y, d, hy.congr hb' hr', by rw [window_eq_of_subset hb' hr' hy.window]; exact hzy⟩

/-- **The fetch test reads only `H`.** -/
theorem fetchedIn_congr (hb : ∀ i ∈ H, U.block i = U'.block i)
    (hr : ∀ i ∈ H, ∀ j ∈ (U.block i).refs, (U'.block j).round = (U.block j).round) {ρ : ℕ}
    (h : FetchedIn U K H A ρ) : FetchedIn U' K H A ρ := by
  have hb' : ∀ i ∈ H, U'.block i = U.block i := fun i hi => (hb i hi).symm
  have hr' : ∀ i ∈ H, ∀ j ∈ (U'.block i).refs, (U.block j).round = (U'.block j).round :=
    fun i hi j hj => (hr i hi j (hb i hi ▸ hj)).symm
  refine ⟨by rw [window_eq_of_subset hb hr h.1]; exact h.1, fun i S m x hi hS hcard => ?_⟩
  have hav := availIn_congr (K := K) (A := A) hb hr
  have hzH : ∀ z ∈ S, z ∈ H := fun z hzS => availIn_subset_held (hav ▸ (hS z hzS).1)
  have hcard' : F.f + Cr.c + 1 ≤ (creatorsOf U.block S).card := by
    have : creatorsOf U'.block S = creatorsOf U.block S :=
      Finset.image_congr fun z hzS => by rw [hb z (hzH z hzS)]
    rwa [this] at hcard
  have hx := h.2 i S m x hi (fun z hzS => by
    obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := hS z hzS
    have hpath : 0 < i → interior U' i (m z) ⊆ H := fun hpos => by
      obtain ⟨y, d, hy, hmy⟩ := h₃ hpos
      exact hmy.trans hy.window
    have hmH : 0 < i → m z ∈ H := fun hpos => hpath hpos mem_windowFrom_self
    have hpath' : 0 < i → interior U i (m z) ⊆ H := fun hpos => by
      rw [interior_eq_of_subset hb' hr' (hmH hpos) (hpath hpos)]; exact hpath hpos
    refine ⟨hav ▸ h₁, by rw [hb z (hzH z hzS)]; exact h₂, fun hpos => ?_,
      by rw [hb z (hzH z hzS)]; exact h₄, ?_⟩
    · obtain ⟨y, d, hy, hmy⟩ := h₃ hpos
      refine ⟨y, d, hy.congr hb' hr', ?_⟩
      rw [interior_eq_of_subset hb' hr' (hmH hpos) (hpath hpos),
        window_eq_of_subset hb' hr' hy.window]
      exact hmy
    · refine ⟨?_, by rw [hr' z (hzH z hzS) (m z) h₄, hb z (hzH z hzS)]; exact h₆⟩
      rcases Nat.eq_zero_or_pos i with rfl | hpos
      · rw [mem_window_zero h₅]; exact self_mem_window
      · rw [← window_eq_of_path hb hr (hmH hpos) (fun _ => hpath' hpos)]; exact h₅) hcard'
  rw [window_eq_of_subset hb hr hx]; exact hx

variable [ClaimFormat BlockId Payload]

omit [LinearOrder BlockId] in
/-- Certifying reads only the certificate's block. -/
theorem certifies_congr {p : Params} {C L : BlockId} {r : ℕ} (hC : U.block C = U'.block C)
    (h : Certifies p U C L r) : Certifies p U' C L r := by
  unfold Certifies claimsOf at *
  rwa [← hC]

/-- **The link read on `H` reads only `H`.** -/
theorem linkedIn_congr (hb : ∀ i ∈ H, U.block i = U'.block i)
    (hr : ∀ i ∈ H, ∀ j ∈ (U.block i).refs, (U'.block j).round = (U.block j).round) {p : Params}
    {L : BlockId} {r : ℕ} (h : LinkedIn p U K H A L r) : LinkedIn p U' K H A L r := by
  obtain ⟨X, hX, hXn⟩ := h
  have hXH : ∀ C ∈ X, C ∈ H := fun C hC => availIn_subset_held (hX C hC).1
  refine ⟨X, fun C hC => ⟨availIn_congr hb hr ▸ (hX C hC).1,
    certifies_congr (hb C (hXH C hC)) (hX C hC).2⟩, ?_⟩
  have : creatorsOf U'.block X = creatorsOf U.block X :=
    Finset.image_congr fun C hC => by rw [hb C (hXH C hC)]
  rw [this]; exact hXn

omit [ClaimFormat BlockId Payload]

/-! ## The record's sub-DAG -/

/-- An anchor point read on `H` is an anchor point of the record. -/
theorem AnchoredIn.toAnchored {y : BlockId} {d : ℕ} (h : AnchoredIn U K H A y d) :
    Anchored U K A y d := by
  induction h with
  | anchor _ => exact Anchored.anchor
  | reached i S m y d y' d' _ hz _ hmz hi hm hcard _ ih ih' =>
    exact Anchored.reached i S m y d y' d' ih hz ih' hmz hi hm hcard

/-- The sub-DAG read on `H` lies in the record's. -/
theorem availIn_subset {z : BlockId} (hz : z ∈ AvailIn U K H A) : z ∈ Avail U K A := by
  obtain ⟨y, d, hy, hzy⟩ := hz
  exact ⟨y, d, hy.toAnchored, hzy⟩

/-- A block of a history lies at or below the block. -/
theorem round_le_of_mem_historyUpto : ∀ (n : ℕ) {y w : BlockId}, y ∈ U.ids →
    w ∈ historyUpto U n y → (U.block w).round ≤ (U.block y).round
  | 0, y, w, _, hw => by
    rw [historyUpto_zero, Finset.mem_singleton] at hw
    subst hw; exact le_rfl
  | n + 1, y, w, hy, hw => by
    rcases mem_historyUpto_succ.mp hw with rfl | ⟨j, hj, hwj⟩
    · exact le_rfl
    · have := (U.valid y hy).below j hj
      have := round_le_of_mem_historyUpto n (U.complete y hy j hj) hwj
      omega

/-- **The available sub-DAG lies at or below its anchor.** -/
theorem round_le_of_avail (hA : A ∈ U.ids) {z : BlockId} (hz : z ∈ Avail U K A) :
    (U.block z).round ≤ (U.block A).round := by
  obtain ⟨y, d, hy, hzy⟩ := hz
  suffices h : (U.block y).round ≤ (U.block A).round from
    (round_le_of_mem_historyUpto d (hy.mem hA) (window_subset_historyUpto hzy)).trans h
  clear hzy
  induction hy with
  | anchor => exact le_rfl
  | @reached x i S m y d y' d' hy hz hy' hmz hi hm hcard ih ih' =>
    obtain ⟨z, hzS⟩ : S.Nonempty := by
      rw [← Finset.card_pos]; exact lt_of_lt_of_le (by omega) (hcard.trans Finset.card_image_le)
    have hzi := window_subset_ids _ ((hy z hzS).mem hA) (hz z hzS)
    have hmi := U.complete z hzi _ (hm z hzS).1
    have := (U.valid z hzi).below _ (hm z hzS).1
    have := round_le_of_mem_historyUpto _ hmi (window_subset_historyUpto (hm z hzS).2.1)
    have := round_le_of_mem_historyUpto _ ((hy z hzS).mem hA) (window_subset_historyUpto (hz z hzS))
    have := ih z hzS
    omega

/-- **An anchor point of the record at or above `ρ` is read on a sub-DAG fetched
down to `ρ`.** -/
theorem Anchored.anchoredIn (hH : H ⊆ U.ids) {ρ : ℕ} (hf : FetchedIn U K H A ρ) {y : BlockId}
    {d : ℕ} (hy : Anchored U K A y d) : ρ ≤ (U.block y).round → AnchoredIn U K H A y d := by
  have hA : A ∈ U.ids := hH (hf.1 self_mem_window)
  induction hy with
  | anchor => exact fun _ => AnchoredIn.anchor hf.1
  | @reached x i S m y d y' d' hy hz hy' hmz hi hm hcard ih ih' =>
    intro hρx
    have hzr : ∀ z ∈ S, ρ < (U.block z).round ∧ ρ ≤ (U.block (y z)).round ∧
        ρ ≤ (U.block (m z)).round := fun z hzS => by
      have hzi := window_subset_ids _ ((hy z hzS).mem hA) (hz z hzS)
      have hmi := U.complete z hzi _ (hm z hzS).1
      have := (U.valid z hzi).below _ (hm z hzS).1
      have := round_le_of_mem_historyUpto _ hmi (window_subset_historyUpto (hm z hzS).2.1)
      have := round_le_of_mem_historyUpto _ ((hy z hzS).mem hA)
        (window_subset_historyUpto (hz z hzS))
      omega
    have i₁ : ∀ z ∈ S, AnchoredIn U K H A (y z) (d z) := fun z hzS => ih z hzS (hzr z hzS).2.1
    have i₂ : ∀ z ∈ S, 0 < i → AnchoredIn U K H A (y' z) (d' z) := fun z hzS hpos =>
      ih' z hzS hpos (le_trans (hzr z hzS).2.2
        (round_le_of_mem_historyUpto _ ((hy' z hzS hpos).mem hA)
          (window_subset_historyUpto (hmz z hzS hpos mem_windowFrom_self))))
    exact AnchoredIn.reached i S m y d y' d' i₁ hz i₂ hmz hi hm hcard
      (hf.2 i S m x hi (fun z hzS => ⟨⟨y z, d z, i₁ z hzS, hz z hzS⟩, (hzr z hzS).1,
        fun hpos => ⟨y' z, d' z, i₂ z hzS hpos, hmz z hzS hpos⟩, hm z hzS⟩) hcard)

/-- **A sub-DAG fetched down to round `ρ` is the record's at and above `ρ`.** -/
theorem avail_subset_availIn (hH : H ⊆ U.ids) {ρ : ℕ} (hf : FetchedIn U K H A ρ) {z : BlockId}
    (hz : z ∈ Avail U K A) (hρ : ρ ≤ (U.block z).round) : z ∈ AvailIn U K H A := by
  have hA : A ∈ U.ids := hH (hf.1 self_mem_window)
  obtain ⟨y, d, hy, hzy⟩ := hz
  exact ⟨y, d, hy.anchoredIn hH hf (le_trans hρ (round_le_of_mem_historyUpto d (hy.mem hA)
    (window_subset_historyUpto hzy))), hzy⟩

/-- **Holding what the record's anchor points bring fetches the sub-DAG**,
down to any round. -/
theorem fetchedIn_of_subset {ρ : ℕ}
    (hsub : ∀ y d, Anchored U K A y d → window U d y ⊆ H) : FetchedIn U K H A ρ := by
  classical
  refine ⟨hsub A K Anchored.anchor, fun i S m x hi hS hcard => hsub x (K - i) ?_⟩
  have h₁ : ∀ z ∈ S, z ∈ Avail U K A := fun z hzS => availIn_subset (hS z hzS).1
  have h₂ : ∀ z ∈ S, 0 < i → ∃ y d, Anchored U K A y d ∧
      interior U i (m z) ⊆ window U d y := fun z hzS hpos => by
    obtain ⟨y, d, hy, hmy⟩ := (hS z hzS).2.2.1 hpos
    exact ⟨y, d, hy.toAnchored, hmy⟩
  refine Anchored.reached i S m (fun z => if h : z ∈ S then (h₁ z h).choose else A)
    (fun z => if h : z ∈ S then (h₁ z h).choose_spec.choose else K)
    (fun z => if h : z ∈ S ∧ 0 < i then (h₂ z h.1 h.2).choose else A)
    (fun z => if h : z ∈ S ∧ 0 < i then (h₂ z h.1 h.2).choose_spec.choose else K)
    (fun z hz => ?_) (fun z hz => ?_) (fun z hz hpos => ?_) (fun z hz hpos => ?_) hi
    (fun z hz => (hS z hz).2.2.2) hcard
  · simp only [dif_pos hz]; exact (h₁ z hz).choose_spec.choose_spec.1
  · simp only [dif_pos hz]; exact (h₁ z hz).choose_spec.choose_spec.2
  · simp only [dif_pos (And.intro hz hpos)]; exact (h₂ z hz hpos).choose_spec.choose_spec.1
  · simp only [dif_pos (And.intro hz hpos)]; exact (h₂ z hz hpos).choose_spec.choose_spec.2

/-- **Fetching down to `ρ` reads only the last `K` rounds below `ρ`**: holding
the record's blocks from round `ρ − K` up to the anchor's round fetches the
sub-DAG down to `ρ`. -/
theorem fetchedIn_of_band (hA : A ∈ U.ids) {ρ : ℕ} (hρ : ρ ≤ (U.block A).round)
    (hH : ∀ b ∈ U.ids, ρ - K ≤ (U.block b).round → (U.block b).round ≤ (U.block A).round →
      b ∈ H) : FetchedIn U K H A ρ := by
  refine ⟨fun b hb => ?_, fun i S m x hi hS hcard => fun b hb => ?_⟩
  · have := round_of_mem_window hb
    exact hH b (window_subset_ids K hA hb) (by omega)
      (round_le_of_mem_historyUpto K hA (window_subset_historyUpto hb))
  · obtain ⟨z, hzS⟩ : S.Nonempty := by
      rw [← Finset.card_pos]; exact lt_of_lt_of_le (by omega) (hcard.trans Finset.card_image_le)
    obtain ⟨hzA, hρz, -, hmz, hxm, hmr⟩ := hS z hzS
    have hzA' := availIn_subset hzA
    have hzr := round_le_of_avail hA hzA'
    obtain ⟨y, d, hy, hzy⟩ := hzA'
    have hzi := window_subset_ids _ (hy.mem hA) hzy
    have hmi := U.complete z hzi _ hmz
    have hxi := window_subset_ids _ hmi hxm
    have h₁ := round_of_mem_window hxm
    have h₂ := round_le_of_mem_historyUpto _ hmi (window_subset_historyUpto hxm)
    have h₃ := round_of_mem_window hb
    have h₄ := round_le_of_mem_historyUpto _ hxi (window_subset_historyUpto hb)
    exact hH b (window_subset_ids _ hxi hb) (by omega) (by omega)

variable [ClaimFormat BlockId Payload]

omit [LinearOrder BlockId] in
/-- A certificate lies at its certificate round. -/
theorem round_of_certifies {p : Params} {C L : BlockId} {r : ℕ} (h : Certifies p U C L r) :
    (U.block C).round = certRound p r := by
  unfold Certifies at h
  unfold certRound
  split_ifs at h ⊢ <;> exact h.1

/-- A link read on `H` is the record's. -/
theorem linkedIn_certLinked (hH : H ⊆ U.ids) {p : Params} {L : BlockId} {r : ℕ}
    (h : LinkedIn p U K H A L r) : CertLinked p U K A L r := by
  obtain ⟨X, hX, hXn⟩ := h
  exact ⟨X, fun C hC => ⟨hH (availIn_subset_held (hX C hC).1), availIn_subset (hX C hC).1,
    (hX C hC).2⟩, hXn⟩

/-- **Fetched down to the round of the certificates, the record's link is read
on `H`.** -/
theorem certLinked_linkedIn (hH : H ⊆ U.ids) {p : Params} {L : BlockId} {r : ℕ}
    (hf : FetchedIn U K H A (certRound p r)) (h : CertLinked p U K A L r) :
    LinkedIn p U K H A L r := by
  obtain ⟨X, hX, hXn⟩ := h
  exact ⟨X, fun C hC => ⟨avail_subset_availIn hH hf (hX C hC).2.1
    (round_of_certifies (hX C hC).2.2).ge, (hX C hC).2.2⟩, hXn⟩

/-! ## Checks -/

omit [ClaimFormat BlockId Payload] in
/-- Backing reads only what is held. -/
theorem backs_congr (hb : ∀ i ∈ H, U.block i = U'.block i) {t : ℕ} {L : BlockId}
    (h : Backs U t H L) : Backs U' t H L := by
  obtain ⟨hL, hn⟩ := h
  refine ⟨hL, ?_⟩
  have hf : (H.filter fun b => (U'.block b).round = (U'.block L).round + 1 ∧
      L ∈ (U'.block b).refs) = H.filter fun b =>
        (U.block b).round = (U.block L).round + 1 ∧ L ∈ (U.block b).refs :=
    Finset.filter_congr fun b hbH => by rw [hb b hbH, hb L hL]
  have hc : creatorsOf U'.block (H.filter fun b => (U.block b).round = (U.block L).round + 1 ∧
      L ∈ (U.block b).refs) = creatorsOf U.block (H.filter fun b =>
        (U.block b).round = (U.block L).round + 1 ∧ L ∈ (U.block b).refs) :=
    Finset.image_congr fun b hbH => by rw [hb b (Finset.mem_filter.mp hbH).1]
  rw [hf, hc]; exact hn

omit [ClaimFormat BlockId Payload] in
/-- **A backed claim names a certified block**: the votes held are votes of the
record. -/
theorem certified_of_backs (hH : H ⊆ U.ids) {t : ℕ} {L : BlockId} (h : Backs U t H L) :
    Certified U t L := by
  refine h.2.trans (Finset.card_le_card (Finset.image_subset_image fun b hb => ?_))
  obtain ⟨hbH, hbr, hLb⟩ := Finset.mem_filter.mp hb
  exact mem_votesFor.mpr ⟨hH hbH, hbr, hLb⟩

/-- **Checking what they hold, correct authors check and claim truthfully.** -/
theorem checks_of_buildsChecked {t : ℕ} (h : BuildsChecked U K t) :
    Checks U K t ∧ Truthful U t := by
  refine ⟨fun z hz hzc m hm X hX L hL => ?_, fun C hC hCc L hL => ?_⟩
  · obtain ⟨H, hH, -, hrefs⟩ := h z hz hzc
    exact certified_of_backs hH ((hrefs m hm).2 X hX L hL)
  · obtain ⟨H, hH, hcl, -⟩ := h C hC hCc
    exact certified_of_backs hH (hcl L hL)

/-! ## Decisions -/

variable [S : Slots Validator]

omit S [ClaimFormat BlockId Payload] in
/-- Blocks a node holds are held by a view holding what the node holds. -/
theorem holdsAtLeast_of_held {V : U.View} (hHV : H ⊆ V.ids) {s : Finset BlockId} {t : ℕ}
    (h : t ≤ (creatorsOf U.block (s.filter (· ∈ H))).card) : HoldsAtLeast U V t s :=
  h.trans (Finset.card_le_card (Finset.image_subset_image fun b hb => by
    obtain ⟨hbs, hbH⟩ := Finset.mem_filter.mp hb
    exact Finset.mem_inter.mpr ⟨hbs, hHV hbH⟩))

/-- **A node's decision is a decision on every view holding what it holds**,
for a node holding blocks of the record. -/
theorem NodeDecided.decided {p : Params} (hH : H ⊆ U.ids) {V : U.View} (hHV : H ⊆ V.ids) {k : ℕ}
    {v : Option BlockId} (h : NodeDecided p U K H k v) : (sRule p K).Decided U V k v := by
  induction h with
  | directCommit hL hc => exact AnchoredRule.Decided.directCommit hL (holdsAtLeast_of_held hHV hc)
  | directSkip hs => exact AnchoredRule.Decided.directSkip (holdsAtLeast_of_held hHV hs)
  | indirectCommit hkj helig _ _ hf hL hlink hleast ihj ihm =>
    exact AnchoredRule.Decided.indirectCommit (i := 0) hkj helig ihj ihm Nat.one_pos
      (fun i' hi' => absurd hi' (Nat.not_lt_zero _)) hL (linkedIn_certLinked hH hlink)
      fun L' hL' hl' hlt => hleast L' hL' hlt (certLinked_linkedIn hH hf hl')
  | indirectSkip hkj helig _ _ hf hnone ihj ihm =>
    exact AnchoredRule.Decided.indirectSkip_single rfl hkj helig ihj ihm
      (fun L hL hlink => hnone L hL (certLinked_linkedIn hH hf hlink))

/-- **Two nodes decide each slot alike**, at a row and the depth the sub-DAG
needs, on a disciplined schedule and record. -/
theorem NodeDecided.agree {p : Params} (hrow : Row Validator p) (hdeep : Deep Validator K)
    (hI : Disciplined K p.certThreshold S U) {H₁ H₂ : Finset BlockId}
    (hH₁ : H₁ ⊆ U.ids) (hH₂ : H₂ ⊆ U.ids) {k : ℕ} {v₁ v₂ : Option BlockId}
    (h₁ : NodeDecided p U K H₁ k v₁) (h₂ : NodeDecided p U K H₂ k v₂) : v₁ = v₂ :=
  (sRule p K).decided_unique (sRule_laws hrow hdeep) hI
    (h₁.decided (V := View.full U) hH₁ hH₁) _ _ (h₂.decided (V := View.full U) hH₂ hH₂)

end KPartialSparse

end LeanDag
