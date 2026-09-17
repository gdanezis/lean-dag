import LeanDag.Steelhead.Liveness.Statement
import LeanDag.Steelhead.Properties
import LeanDag.MahiMahi.Helpers.Liveness
import LeanDag.Properties.Derived.Descent
/-!
# Helpers — the liveness layer

Generated lemma infrastructure for `Liveness/Statement.lean`; not part of
the audit surface. SH6 is the timed bridge at Steelhead's support, with
the descent from `Indirect`; SH7 is Mahi-Mahi's descent and bridge at the
chain schedule, where the identity rounds discharge the spanning
hypothesis; SH8 is an induction on the derivation, with the arithmetic of
the residue class `k − 1` done by hand since `omega` reads no variable
modulus.
-/

namespace LeanDag

namespace Steelhead

open LeanDag.Properties SteelheadProperties

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type} [LinearOrder BlockId] {Payload : Type}

/-- A correct quorum is a quorum of the core's fault model. -/
theorem isQuorum_core {T : Finset Validator} (hT : T ⊆ (Correct : Finset Validator))
    (hcard : quorumCard Validator ≤ T.card) : (coreReliability Validator).IsQuorum T :=
  ⟨hT, by change Fintype.card Validator - Faults.f Validator ≤ T.card; exact hcard⟩

/-! ## SH6h — the round-robin schedule -/

/-- Within one cycle a round is determined by the residue it leads and its distance below it. -/
theorem roundRobin_back {n a i : ℕ} (hn : 0 < n) (ha : a < n) (hi : i < n) :
    ((a + i) % n + n - i) % n = a := by
  rcases Nat.lt_or_ge (a + i) n with hlt | hge
  · rw [Nat.mod_eq_of_lt hlt, show a + i + n - i = a + n by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt ha]
  · have he : (a + i) % n = a + i - n := by
      have h2 : (a + i - n + n) % n = a + i - n := by
        rw [Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      rwa [show a + i - n + n = a + i by omega] at h2
    rw [he, show a + i - n + n - i = a by omega, Nat.mod_eq_of_lt ha]

/-- **SH6h.** A validator outside `T` leads one residue, which spoils the `c` windows ending at
it and no others, so `c · (n − |T|)` windows at most are spoilt; `n` windows open a cycle, so
one of them is wholly `T`-led, and the schedule repeats it past every round. -/
theorem roundRobin_fairRun {n : ℕ} (hn : 0 < n) {T : Finset (Fin n)} {c : ℕ}
    (h : c * (n - T.card) < n) :
    FairRunOn (S := Slots.identity fun r => (⟨r % n, Nat.mod_lt r hn⟩ : Fin n)) T c := by
  classical
  -- a window of `c` rounds, inside one cycle, that no validator outside `T` leads
  have key : ∃ a, a < n ∧ ∀ i, i < c → (⟨(a + i) % n, Nat.mod_lt _ hn⟩ : Fin n) ∈ T := by
    -- past `n` candidates the schedule repeats, so `c` may be taken below `n`
    rcases Nat.lt_or_ge c n with hc | hc
    · by_contra hcon
      have hcon' : ∀ a, a < n → ∃ i, i < c ∧ (⟨(a + i) % n, Nat.mod_lt _ hn⟩ : Fin n) ∉ T := by
        intro a ha
        by_contra hno
        exact hcon ⟨a, ha, fun i hi => by
          by_contra hnot
          exact hno ⟨i, hi, hnot⟩⟩
      set C : Finset (Fin n) := Finset.univ \ T with hC
      set back : Fin n → Finset (Fin n) := fun v =>
        (Finset.range c).image fun j => (⟨(v.val + n - j) % n, Nat.mod_lt _ hn⟩ : Fin n) with hback
      have hsub : (Finset.univ : Finset (Fin n)) ⊆ C.biUnion back := by
        intro a _
        obtain ⟨i, hi, hnot⟩ := hcon' a.val a.isLt
        refine Finset.mem_biUnion.mpr ⟨_, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hnot⟩, ?_⟩
        refine Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hi, ?_⟩
        exact Fin.ext (roundRobin_back hn a.isLt (by omega))
      have hcard : n ≤ C.card * c := by
        have h₁ : (Finset.univ : Finset (Fin n)).card ≤ ∑ _v ∈ C, c :=
          le_trans (le_trans (Finset.card_le_card hsub) Finset.card_biUnion_le)
            (Finset.sum_le_sum fun v _ => by
              refine le_trans Finset.card_image_le ?_
              rw [Finset.card_range])
        rw [Finset.card_univ, Fintype.card_fin, Finset.sum_const, smul_eq_mul] at h₁
        exact h₁
      have hCcard : C.card = n - T.card := by
        rw [hC, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
      rw [hCcard, Nat.mul_comm] at hcard
      omega
    · -- with `n ≤ c` the bound forces every validator into `T`
      refine ⟨0, hn, fun i _ => ?_⟩
      have hTn : T.card = n := by
        have hle : T.card ≤ n := by
          have := Finset.card_le_card (Finset.subset_univ T)
          rwa [Finset.card_univ, Fintype.card_fin] at this
        by_contra hne
        have hpos : 0 < n - T.card := by omega
        have := Nat.le_mul_of_pos_right c hpos
        omega
      have : T = Finset.univ := Finset.eq_univ_of_card T (by rw [hTn, Fintype.card_fin])
      rw [this]
      exact Finset.mem_univ _
  obtain ⟨a, -, ha⟩ := key
  intro k
  have hk : k ≤ n * k := Nat.le_mul_of_pos_left k hn
  refine ⟨a + n * k, by omega, fun i hi => ?_⟩
  have hmod : (a + n * k + i) % n = (a + i) % n := by
    rw [show a + n * k + i = a + i + n * k by omega, Nat.add_mul_mod_self_left]
  have hfin : (⟨(a + n * k + i) % n, Nat.mod_lt _ hn⟩ : Fin n)
      = ⟨(a + i) % n, Nat.mod_lt _ hn⟩ := Fin.ext hmod
  change (⟨(a + n * k + i) % n, Nat.mod_lt _ hn⟩ : Fin n) ∈ T
  rw [hfin]
  exact ha i hi

/-- **SH6h, the near half.** A window of `n − |T| + 1` consecutive rounds leads that many
distinct validators, more than lie outside `T`, so one of them is `T`'s. -/
theorem roundRobin_near {n : ℕ} (hn : 0 < n) {T : Finset (Fin n)} (hT : T.Nonempty) (r : ℕ) :
    ∃ a, r ≤ a ∧ a ≤ r + (n - T.card) ∧ (⟨a % n, Nat.mod_lt a hn⟩ : Fin n) ∈ T := by
  classical
  by_contra hcon
  have hTcard : T.card ≤ n := by
    have := Finset.card_le_card (Finset.subset_univ T)
    rwa [Finset.card_univ, Fintype.card_fin] at this
  have hTpos : 1 ≤ T.card := Finset.card_pos.mpr hT
  set f : ℕ → Fin n := fun i => (⟨(r + i) % n, Nat.mod_lt _ hn⟩ : Fin n) with hf
  have hbad : ∀ i ∈ Finset.range (n - T.card + 1), f i ∈ Finset.univ \ T := by
    intro i hi
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hmem => hcon ⟨r + i, by omega, ?_, hmem⟩⟩
    have := Finset.mem_range.mp hi
    omega
  -- a round of the window lies one cycle at most above the base, so its residue names it
  have key : ∀ t, t < n → (r + t) % n =
      if r % n + t < n then r % n + t else r % n + t - n := by
    intro t ht
    rw [Nat.add_mod r t n, Nat.mod_eq_of_lt ht]
    split
    · exact Nat.mod_eq_of_lt (by omega)
    · rename_i hge
      have hs : r % n < n := Nat.mod_lt _ hn
      have h2 : (r % n + t - n + n) % n = r % n + t - n := by
        rw [Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      rwa [show r % n + t - n + n = r % n + t by omega] at h2
  have hinj : Set.InjOn f (Finset.range (n - T.card + 1)) := by
    intro i hi j hj hij
    have hi' := Finset.mem_range.mp hi
    have hj' := Finset.mem_range.mp hj
    have hmod : (r + i) % n = (r + j) % n := congrArg Fin.val hij
    rw [key i (by omega), key j (by omega)] at hmod
    have hs : r % n < n := Nat.mod_lt _ hn
    split_ifs at hmod <;> omega
  have hcard := Finset.card_le_card_of_injOn f hbad hinj
  rw [Finset.card_range, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ,
    Fintype.card_fin] at hcard
  omega

/-! ## SH6i — the hop count -/

/-- The offset that carries a round to the next round of residue `k`, within one cycle. -/
theorem mod_add_offset {n : ℕ} (hn : 0 < n) (a k : ℕ) (hk : k < n) :
    (a + (k + n - a % n) % n) % n = k := by
  have hs : a % n < n := Nat.mod_lt _ hn
  rcases Nat.lt_or_ge k (a % n) with h | h
  · rw [Nat.mod_eq_of_lt (show k + n - a % n < n by omega), Nat.add_mod,
      show a % n + (k + n - a % n) % n = a % n + (k + n - a % n) from by
        rw [Nat.mod_eq_of_lt (show k + n - a % n < n by omega)],
      show a % n + (k + n - a % n) = k + n by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hk]
  · rw [show k + n - a % n = k - a % n + n by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (show k - a % n < n by omega), Nat.add_mod,
      show a % n + (k - a % n) % n = k from by
        rw [Nat.mod_eq_of_lt (show k - a % n < n by omega)]; omega,
      Nat.mod_eq_of_lt hk]

/-- A round between two landings of a chain lies in one of its hops. -/
theorem exists_hop_index {x : ℕ → ℕ} {i j t : ℕ} (hij : i < j) (ht : x i ≤ t) (htj : t < x j) :
    ∃ k, i ≤ k ∧ k < j ∧ x k ≤ t ∧ t < x (k + 1) := by
  have aux : ∀ d i', j = i' + d → 0 < d → x i' ≤ t →
      ∃ k, i' ≤ k ∧ k < j ∧ x k ≤ t ∧ t < x (k + 1) := by
    intro d
    induction d with
    | zero => intro _ _ hd; omega
    | succ d ih =>
      intro i' hji hd hi'
      rcases Nat.lt_or_ge t (x (i' + 1)) with hlt | hge
      · exact ⟨i', le_rfl, by omega, hi', hlt⟩
      · have hd' : 0 < d := by
          rcases Nat.eq_zero_or_pos d with rfl | hpos
          · exact absurd htj (by rw [show j = i' + 1 by omega]; omega)
          · exact hpos
        obtain ⟨k, hk1, hk2, hk3, hk4⟩ := ih (i' + 1) (by omega) hd' hge
        exact ⟨k, by omega, hk2, hk3, hk4⟩
  exact aux (j - i) i (by omega) (by omega) ht

omit F in
/-- **Two landings of the floor chain never share a residue.** A chain that advances by at least
`ws` rounds a hop, whose landings are led from outside `T` and whose rounds from a landing's floor
up to the next landing are too, cannot have two landings at one residue: between two such landings
lies a whole number of cycles, each holding `T.card` reliably led rounds, and every one of them
must fall in the `ws − 1` rounds a hop leaves free, which forces `n ≤ ws · (n − T.card)`. -/
theorem roundRobin_residues_distinct {n ws m : ℕ} (hn : 0 < n) (hws : 1 ≤ ws) {T : Finset Validator}
    {lead : Fin n → Validator} (hbij : Function.Bijective lead) {sched : ℕ → Validator}
    (hsched : ∀ t, sched t = lead ⟨t % n, Nat.mod_lt t hn⟩) (hlt : ws * (n - T.card) < n)
    {x : ℕ → ℕ} (hstep : ∀ i, i < m → x i + ws ≤ x (i + 1))
    (hbad : ∀ i, i ≤ m → sched (x i) ∉ T)
    (hmid : ∀ i, i < m → ∀ t, x i + ws ≤ t → t < x (i + 1) → sched t ∉ T) :
    ∀ i j, i < j → j ≤ m → x i % n ≠ x j % n := by
  classical
  set e : Fin n ≃ Validator := Equiv.ofBijective lead hbij with he
  have hcard : Fintype.card Validator = n := by
    have := Fintype.card_of_bijective hbij
    simpa using this.symm
  have hTcard : T.card ≤ n := by
    have := Finset.card_le_univ T
    rwa [hcard] at this
  -- the chain advances by `ws` a hop
  have hgrow : ∀ d i, i + d ≤ m → x i + d * ws ≤ x (i + d) := by
    intro d
    induction d with
    | zero => intro i _; simp
    | succ d ih =>
      intro i hi
      have h1 : x i + d * ws ≤ x (i + d) := ih i (by omega)
      have h2 : x (i + d) + ws ≤ x (i + d + 1) := hstep (i + d) (by omega)
      rw [show i + (d + 1) = i + d + 1 by omega, Nat.succ_mul]
      omega
  intro i j hij hjm hres
  have hab : x i + (j - i) * ws ≤ x j := by
    have := hgrow (j - i) i (by omega)
    rwa [show i + (j - i) = j by omega] at this
  have hdpos : 1 * 1 ≤ (j - i) * ws := Nat.mul_le_mul (by omega) hws
  have hltab : x i < x j := by omega
  obtain ⟨q, hq⟩ : ∃ q, x j - x i = n * q := by
    refine ⟨x j / n - x i / n, ?_⟩
    have h1 := Nat.div_add_mod (x i) n
    have h2 := Nat.div_add_mod (x j) n
    have h3 : n * (x i / n) ≤ n * (x j / n) :=
      Nat.mul_le_mul_left n (Nat.div_le_div_right (le_of_lt hltab))
    rw [Nat.mul_sub]
    omega
  have hq1 : 1 ≤ q := by
    rcases Nat.eq_zero_or_pos q with rfl | h
    · omega
    · exact h
  set Led : Finset ℕ := (Finset.Ico (x i) (x j)).filter fun t => sched t ∈ T with hLed
  -- every cycle of the span holds one round of each reliable validator's residue
  have hlow : T.card * q ≤ Led.card := by
    have hcardprod : (T ×ˢ Finset.range q).card = T.card * q := by
      rw [Finset.card_product, Finset.card_range]
    rw [← hcardprod]
    refine Finset.card_le_card_of_injOn
      (fun p : Validator × ℕ => x i + (↑(e.symm p.1) + n - x i % n) % n + n * p.2) ?_ ?_
    · rintro ⟨v, c⟩ hp
      obtain ⟨hv, hc⟩ := Finset.mem_product.mp hp
      have hcq : c < q := Finset.mem_range.mp hc
      have hstepn : n * (c + 1) ≤ n * q := Nat.mul_le_mul_left n (by omega)
      rw [Nat.mul_succ] at hstepn
      obtain ⟨off, hoffeq, hoff⟩ :
          ∃ off, (↑(e.symm v) + n - x i % n) % n = off ∧ off < n :=
        ⟨_, rfl, Nat.mod_lt _ hn⟩
      change x i + (↑(e.symm v) + n - x i % n) % n + n * c ∈ Led
      refine Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by rw [hoffeq]; omega, ?_⟩, ?_⟩
      · rw [hoffeq]
        omega
      · have hmod : (x i + (↑(e.symm v) + n - x i % n) % n + n * c) % n = ↑(e.symm v) := by
          rw [Nat.add_mul_mod_self_left]
          exact mod_add_offset hn _ _ (e.symm v).isLt
        rw [hsched]
        have : (⟨(x i + (↑(e.symm v) + n - x i % n) % n + n * c) % n, Nat.mod_lt _ hn⟩ :
            Fin n) = e.symm v := Fin.ext hmod
        rw [this]
        have : lead (e.symm v) = v := e.apply_symm_apply v
        rw [this]
        exact hv
    · rintro ⟨v, c⟩ hp ⟨v', c'⟩ hp' hff
      have hmod : (↑(e.symm v) : ℕ) = ↑(e.symm v') := by
        have h1 : (x i + (↑(e.symm v) + n - x i % n) % n + n * c) % n = ↑(e.symm v) := by
          rw [Nat.add_mul_mod_self_left]
          exact mod_add_offset hn _ _ (e.symm v).isLt
        have h2 : (x i + (↑(e.symm v') + n - x i % n) % n + n * c') % n = ↑(e.symm v') := by
          rw [Nat.add_mul_mod_self_left]
          exact mod_add_offset hn _ _ (e.symm v').isLt
        rw [← h1, ← h2]
        exact congrArg (· % n) hff
      have hvv : v = v' := by
        have : e.symm v = e.symm v' := Fin.ext hmod
        simpa using congrArg e this
      subst hvv
      have hcc : n * c = n * c' := by
        have := hff
        simp only at this
        omega
      have : c = c' := Nat.eq_of_mul_eq_mul_left hn hcc
      subst this
      rfl
  -- and each of those rounds falls in the rounds one hop leaves free
  have hup : Led.card ≤ (j - i) * (ws - 1) := by
    have hsub : Led ⊆ (Finset.Ico i j).biUnion fun k => Finset.Ioo (x k) (x k + ws) := by
      intro t ht
      obtain ⟨htIco, htT⟩ := Finset.mem_filter.mp ht
      obtain ⟨ht1, ht2⟩ := Finset.mem_Ico.mp htIco
      obtain ⟨k, hk1, hk2, hk3, hk4⟩ := exists_hop_index hij ht1 ht2
      refine Finset.mem_biUnion.mpr ⟨k, Finset.mem_Ico.mpr ⟨hk1, hk2⟩,
        Finset.mem_Ioo.mpr ⟨?_, ?_⟩⟩
      · rcases Nat.eq_or_lt_of_le hk3 with heq | hlt'
        · exact absurd (heq ▸ htT) (hbad k (by omega))
        · exact hlt'
      · by_contra hge
        exact hmid k (by omega) t (by omega) hk4 htT
    refine le_trans (Finset.card_le_card hsub) (le_trans Finset.card_biUnion_le ?_)
    calc ∑ k ∈ Finset.Ico i j, (Finset.Ioo (x k) (x k + ws)).card
        ≤ ∑ _k ∈ Finset.Ico i j, (ws - 1) :=
          Finset.sum_le_sum fun k _ => by rw [Nat.card_Ioo]; omega
      _ = (j - i) * (ws - 1) := by rw [Finset.sum_const, Nat.card_Ico, smul_eq_mul]
  -- the two counts meet only at `n ≤ ws · (n − T.card)`
  have hdn : (j - i) * ws ≤ n * q := by omega
  have h1 : ws * (T.card * q) ≤ ws * ((j - i) * (ws - 1)) :=
    Nat.mul_le_mul_left ws (le_trans hlow hup)
  have h2 : ws * ((j - i) * (ws - 1)) = ((j - i) * ws) * (ws - 1) := by
    rw [Nat.mul_comm ws ((j - i) * (ws - 1)), Nat.mul_assoc, Nat.mul_comm (ws - 1) ws,
      ← Nat.mul_assoc]
  have h3 : ((j - i) * ws) * (ws - 1) ≤ (n * q) * (ws - 1) :=
    Nat.mul_le_mul_right (ws - 1) hdn
  have h4 : q * (ws * T.card) ≤ q * (n * (ws - 1)) := by
    have hleft : ws * (T.card * q) = q * (ws * T.card) := by
      rw [Nat.mul_comm T.card q, ← Nat.mul_assoc, Nat.mul_comm ws q, Nat.mul_assoc]
    have hright : (n * q) * (ws - 1) = q * (n * (ws - 1)) := by
      rw [Nat.mul_comm n q, Nat.mul_assoc]
    rw [← hleft, ← hright]
    exact le_trans h1 (le_trans (le_of_eq h2) h3)
  have h5 : ws * T.card ≤ n * (ws - 1) := Nat.le_of_mul_le_mul_left h4 (by omega)
  have h6 : n * (ws - 1) = n * ws - n := by
    rw [Nat.mul_sub, Nat.mul_one]
  have h7 : ws * (n - T.card) = ws * n - ws * T.card := Nat.mul_sub ws n T.card
  have h8 : ws * n = n * ws := Nat.mul_comm ws n
  have h9 : ws * T.card ≤ ws * n := Nat.mul_le_mul_left ws hTcard
  have h10 : n ≤ n * ws := Nat.le_mul_of_pos_right n (by omega)
  omega

omit F in
/-- The residues a set of validators occupies on the round-robin schedule, counted through the
bijection: as many as the set has members. -/
theorem card_residues_of_bijective {n : ℕ} {lead : Fin n → Validator}
    (hbij : Function.Bijective lead) (X : Finset Validator) :
    (Finset.univ.filter fun k : Fin n => lead k ∈ X).card = X.card := by
  refine Finset.card_bij (fun k _ => lead k) (fun k hk => (Finset.mem_filter.mp hk).2)
    (fun a _ b _ hab => hbij.1 hab) fun v hv => ?_
  obtain ⟨k, hk⟩ := hbij.2 v
  exact ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk ▸ hv⟩, hk⟩

omit F in
/-- **The count that bounds the floor chain (SH6i).** The landings' residues are distinct
(`roundRobin_residues_distinct`), and only the `n − T.card` residues outside `T` are open to
them, so a chain of that many hops led from outside `T` throughout cannot exist. -/
theorem roundRobin_hop_bound {n ws m : ℕ} (hn : 0 < n) (hws : 1 ≤ ws) {T : Finset Validator}
    {lead : Fin n → Validator} (hbij : Function.Bijective lead) {sched : ℕ → Validator}
    (hsched : ∀ t, sched t = lead ⟨t % n, Nat.mod_lt t hn⟩) (hm : m = n - T.card)
    (hlt : ws * m < n) {x : ℕ → ℕ} (hstep : ∀ i, i < m → x i + ws ≤ x (i + 1))
    (hbad : ∀ i, i ≤ m → sched (x i) ∉ T)
    (hmid : ∀ i, i < m → ∀ t, x i + ws ≤ t → t < x (i + 1) → sched t ∉ T) : False := by
  classical
  have hcard : Fintype.card Validator = n := by
    have := Fintype.card_of_bijective hbij
    simpa using this.symm
  -- the residues the landings may take are the `m` the reliable set leaves free
  set Bad : Finset (Fin n) := Finset.univ.filter fun k => lead k ∉ T with hBad
  have hBadcard : Bad.card = m := by
    have hsplit : Bad.card + (Finset.univ.filter fun k : Fin n => lead k ∈ T).card =
        (Finset.univ : Finset (Fin n)).card := by
      rw [hBad, Nat.add_comm]
      exact Finset.card_filter_add_card_filter_not (s := Finset.univ)
        (p := fun k : Fin n => lead k ∈ T)
    rw [Finset.card_univ, Fintype.card_fin, card_residues_of_bijective hbij] at hsplit
    omega
  have hbad' : ∀ i, i ≤ m → lead ⟨x i % n, Nat.mod_lt _ hn⟩ ∉ T := by
    intro i hi
    have := hbad i hi
    rwa [hsched] at this
  -- two of the `m + 1` landings share a residue
  obtain ⟨i, hi, j, hj, hne, heq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to (s := Finset.range (m + 1)) (t := Bad)
      (f := fun i => (⟨x i % n, Nat.mod_lt _ hn⟩ : Fin n))
      (by rw [Finset.card_range, hBadcard]; omega)
      fun i hi => Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        hbad' i (by have := Finset.mem_range.mp hi; omega)⟩
  have hi' := Finset.mem_range.mp hi
  have hj' := Finset.mem_range.mp hj
  have hres : x i % n = x j % n := congrArg Fin.val heq
  have key := roundRobin_residues_distinct hn hws hbij hsched (hm ▸ hlt) hstep hbad hmid
  rcases Nat.lt_or_ge i j with h | h
  · exact key i j h (by omega) hres
  · exact key j i (by omega) (by omega) hres.symm

/-- **The count that bounds the floor chain by the Byzantine validators (SH6i′).** Landings led
by Byzantine validators occupy at most `|byzantine|` residues, and the landings' residues are
distinct (`roundRobin_residues_distinct`), so a chain of that many hops whose landings are all
Byzantine-led cannot exist. -/
theorem roundRobin_byzantine_hop_bound {n ws : ℕ} (hn : 0 < n) (hws : 1 ≤ ws)
    {T : Finset Validator} (hT : T ⊆ (Correct : Finset Validator)) {lead : Fin n → Validator}
    (hbij : Function.Bijective lead) {sched : ℕ → Validator}
    (hsched : ∀ t, sched t = lead ⟨t % n, Nat.mod_lt t hn⟩) (hlt : ws * (n - T.card) < n)
    {x : ℕ → ℕ} (hstep : ∀ i, i < F.byzantine.card → x i + ws ≤ x (i + 1))
    (hbyz : ∀ i, i ≤ F.byzantine.card → sched (x i) ∈ F.byzantine)
    (hmid : ∀ i, i < F.byzantine.card → ∀ t, x i + ws ≤ t → t < x (i + 1) → sched t ∉ T) :
    False := by
  classical
  -- a Byzantine validator is not reliable
  have hnotT : ∀ v, v ∈ F.byzantine → v ∉ T := by
    intro v hv hvT
    have := hT hvT
    rw [Correct, Finset.mem_compl] at this
    exact this hv
  have hbad : ∀ i, i ≤ F.byzantine.card → sched (x i) ∉ T :=
    fun i hi => hnotT _ (hbyz i hi)
  set Byz : Finset (Fin n) := Finset.univ.filter fun k => lead k ∈ F.byzantine with hByz
  have hByzcard : Byz.card = F.byzantine.card := card_residues_of_bijective hbij _
  have hbyz' : ∀ i, i ≤ F.byzantine.card → lead ⟨x i % n, Nat.mod_lt _ hn⟩ ∈ F.byzantine := by
    intro i hi
    have := hbyz i hi
    rwa [hsched] at this
  -- two of the `|byzantine| + 1` landings share a residue
  obtain ⟨i, hi, j, hj, hne, heq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to (s := Finset.range (F.byzantine.card + 1))
      (t := Byz) (f := fun i => (⟨x i % n, Nat.mod_lt _ hn⟩ : Fin n))
      (by rw [Finset.card_range, hByzcard]; omega)
      fun i hi => Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        hbyz' i (by have := Finset.mem_range.mp hi; omega)⟩
  have hi' := Finset.mem_range.mp hi
  have hj' := Finset.mem_range.mp hj
  have hres : x i % n = x j % n := congrArg Fin.val heq
  have key := roundRobin_residues_distinct hn hws hbij hsched hlt hstep hbad hmid
  rcases Nat.lt_or_ge i j with h | h
  · exact key i j h (by omega) hres
  · exact key j i (by omega) (by omega) hres.symm

section Slots

variable [S : Slots Validator]

/-! ## SH6 — the synchronous route -/

/-- **The descent**, under the spanning hypothesis at each slot's own wave:
`Descends.of_indirect` at `Eligible` read as the round inequality. -/
theorem descends {w : ℕ → ℕ} (hw : ∀ r, 1 ≤ w r) {c : ℕ}
    (hspan : (steelheadAnchored Validator BlockId Payload w).SpansEligible (S := S) c) :
    Descends (steelheadRule (Validator := Validator) (BlockId := BlockId) (Payload := Payload) w)
      S c := by
  have hc : 0 < c := by
    have := (steelheadAnchored Validator BlockId Payload w).lt_of_eligible (hspan 1 0 (by omega))
    omega
  intro U V b hrun i hi
  exact Descends.of_indirect (S := S) (indirect (Validator := Validator) (BlockId := BlockId)
    (Payload := Payload) hw) hc (fun b i hi => by
      have := (steelheadAnchored Validator BlockId Payload w).eligible_iff.mp (hspan b i hi)
      simp only [steelheadAnchored_waveAt] at this
      have := hw (S.slotRound i)
      change S.slotRound i + w (S.slotRound i) ≤ S.slotRound (b + c - 1)
      omega) V b hrun i hi

/-- **SH6a.** The bridge certifies the slot's candidate from every reliable block at its decision
round, which is the direct commit, in the view and at the slot's own wave. -/
theorem commitsOfSynchrony {U : BlockUniverse Validator BlockId Payload} {w : ℕ → ℕ}
    (hw : ∀ r, 3 ≤ w r) {T : Finset Validator} {V : View Validator BlockId Payload U}
    {R N k : ℕ} (hT : T ⊆ (Correct : Finset Validator)) (hcard : quorumCard Validator ≤ T.card)
    (hs : SynchronisedOn U T R) (hpop : ∀ r, R ≤ r → r ≤ N → PopulatedOn U T r)
    (hR : R ≤ S.slotRound k)
    (hN : ∀ j, j ≤ k → (steelheadAnchored Validator BlockId Payload w).decisionRound j ≤ N)
    (hV : V.CoversUpto N) (hlead : S.leader k ∈ T) :
    ∃ L, IsLeaderBlock U k L ∧
      MahiMahi.DirectCommitIn U V (w (S.slotRound k)) L (S.slotRound k) ∧
      Decided w U V k (some L) := by
  obtain ⟨-, -, -, -, h⟩ := Timed.live_of_coverage (shSupport w) (shSupport_ofCoverage hw)
    (isQuorum_core hT hcard) hs hpop S V (lo := k) (K := k + 1) hV hR
    (fun j hj => hN j (Nat.lt_succ_iff.mp hj))
  obtain ⟨hpopk, hcert⟩ := h k le_rfl (Nat.lt_succ_self k) hlead
  obtain ⟨L, hL, hin⟩ := shSupport_directCommitIn (fun r => by have := hw r; omega) S V
    hcard hpopk hcert (fun b hb hbr => hV b hb (le_trans hbr (hN k le_rfl))) hlead
  exact ⟨L, hL, hin, Decided.directCommit hL hin⟩

/-- **SH6b.** The timed descent below a fair run, at Steelhead's support. -/
theorem allDecidedBelowOfSynchrony {w : ℕ → ℕ} (hw : ∀ r, 3 ≤ w r) {T : Finset Validator}
    {c : ℕ} (hT : T ⊆ (Correct : Finset Validator)) (hcard : quorumCard Validator ≤ T.card)
    (hspan : (steelheadAnchored Validator BlockId Payload w).SpansEligible (S := S) c)
    (fair : FairRunOn T c) (R k : ℕ) :
    ∃ b, k ≤ b ∧ R ≤ S.slotRound b ∧
      ∀ (U : BlockUniverse Validator BlockId Payload) (V : View Validator BlockId Payload U)
        (N : ℕ),
        SynchronisedOn U T R → (∀ r, R ≤ r → r ≤ N → PopulatedOn U T r) →
        V.CoversUpto N →
        (∀ j, j < b + c → (steelheadAnchored Validator BlockId Payload w).decisionRound j ≤ N) →
        ∀ i, i < b → ∃ v, Decided w U V i v := by
  obtain ⟨b, hb, hRb, h⟩ := Timed.decidedBelow_of_fairRun (shSupport w) (shSupport_ofCoverage hw)
    (shSupport_commits fun r => by have := hw r; omega)
    (descends (fun r => by have := hw r; omega) hspan) (isQuorum_core hT hcard) fair R k
  refine ⟨b, hb, hRb, fun U V N hs hpop hV hN i hi => ?_⟩
  obtain ⟨v, hv⟩ := h V N hs hpop hV hN i hi
  exact ⟨v, hv.2.1⟩

/-- **SH6f.** The least committed slot at or above the floor is the anchor: the reliably led slot
commits directly (SH6a), so there is one, and every eligible slot below it is decided but not
committed, a skip. The indirect rule then decides the slot. -/
theorem decidedOfReliableAboveFloor {U : BlockUniverse Validator BlockId Payload} {w : ℕ → ℕ}
    (hw : ∀ r, 3 ≤ w r) (hid : ∀ t, S.slotRound t = t) {T : Finset Validator}
    {V : View Validator BlockId Payload U} {R N k a : ℕ} (hT : T ⊆ (Correct : Finset Validator))
    (hcard : quorumCard Validator ≤ T.card) (hs : SynchronisedOn U T R)
    (hpop : ∀ r, R ≤ r → r ≤ N → PopulatedOn U T r) (hR : R ≤ k) (hka : k + w k ≤ a)
    (hlead : S.leader a ∈ T) (hdec : ∀ j, k + w k ≤ j → j < a → ∃ v, Decided w U V j v)
    (hN : ∀ j, j ≤ a → (steelheadAnchored Validator BlockId Payload w).decisionRound j ≤ N)
    (hV : V.CoversUpto N) : ∃ v, Decided w U V k v := by
  classical
  -- the reliably led slot commits
  obtain ⟨A, -, -, hA⟩ := commitsOfSynchrony hw hT hcard hs hpop (by rw [hid]; omega) hN hV hlead
  -- the least committed slot at or above the floor
  have hex : ∃ j, k + w k ≤ j ∧ ∃ A, Decided w U V j (some A) := ⟨a, hka, A, hA⟩
  obtain ⟨hkj, A', hA'⟩ : k + w k ≤ Nat.find hex ∧ ∃ A, Decided w U V (Nat.find hex) (some A) :=
    Nat.find_spec hex
  have hja : Nat.find hex ≤ a := Nat.find_le ⟨hka, A, hA⟩
  -- every eligible slot between the floor and it is decided but not committed, so skipped
  have hmid : ∀ i', k < i' → i' < Nat.find hex →
      (fun sr i j => sr i + w (sr i) ≤ sr j) S.slotRound k i' → Decided w U V i' none := by
    intro i' _ hi'j helig
    simp only [hid] at helig
    have hnc : ¬ ∃ C, Decided w U V i' (some C) := fun hc => Nat.find_min hex hi'j ⟨helig, hc⟩
    obtain ⟨v, hv⟩ := hdec i' helig (by omega)
    cases v with
    | none => exact hv
    | some C => exact absurd ⟨C, hv⟩ hnc
  obtain ⟨v, hv⟩ := indirect (Validator := Validator) (BlockId := BlockId) (Payload := Payload)
    (fun r => by have := hw r; omega) S V k (Nat.find hex) A' (by simp only [hid]; exact hkj) hA'
    hmid
  exact ⟨v, hv S rfl rfl hA' hmid⟩

/-! ## SH6g — the floor chain -/

/-- A commit at or above a slot's floor, with every slot between the floor and it skipped,
decides the slot: the indirect rule reads the commit as the anchor and passes over the skips. -/
theorem decidedOfCommitAboveFloor {U : BlockUniverse Validator BlockId Payload} {w : ℕ → ℕ}
    (hw : ∀ r, 3 ≤ w r) (hid : ∀ t, S.slotRound t = t)
    {V : View Validator BlockId Payload U} {k a : ℕ} {A : BlockId} (hka : k + w k ≤ a)
    (hA : Decided w U V a (some A)) (hmid : ∀ j, k + w k ≤ j → j < a → Decided w U V j none) :
    ∃ v, Decided w U V k v := by
  have hmid' : ∀ i', k < i' → i' < a →
      (fun sr i j => sr i + w (sr i) ≤ sr j) S.slotRound k i' → Decided w U V i' none := by
    intro i' _ hi' helig
    simp only [hid] at helig
    exact hmid i' helig hi'
  obtain ⟨v, hv⟩ := indirect (Validator := Validator) (BlockId := BlockId) (Payload := Payload)
    (fun r => by have := hw r; omega) S V k a A (by simp only [hid]; exact hka) hA hmid'
  exact ⟨v, hv S rfl rfl hA hmid'⟩

/-- **SH6g.** Downward induction on the chain: the last landing is reliably led, so it commits
directly (SH6a); a landing whose successor commits is decided, the slots between them being the
skips the search passes over, and the hop leaves it unskipped, so it commits in turn and anchors
the landing below it. -/
theorem floorChainDecides {U : BlockUniverse Validator BlockId Payload} {w : ℕ → ℕ}
    (hw : ∀ r, 3 ≤ w r) (hid : ∀ t, S.slotRound t = t) {T : Finset Validator}
    {V : View Validator BlockId Payload U} {R N : ℕ} (hT : T ⊆ (Correct : Finset Validator))
    (hcard : quorumCard Validator ≤ T.card) (hs : SynchronisedOn U T R)
    (hpop : ∀ r, R ≤ r → r ≤ N → PopulatedOn U T r) (hV : V.CoversUpto N) :
    ∀ (h : ℕ) (x : ℕ → ℕ), R ≤ x 0 → (∀ i, i < h → FloorHop w U V (x i) (x (i + 1))) →
      S.leader (x h) ∈ T →
      (∀ j, j ≤ x h → (steelheadAnchored Validator BlockId Payload w).decisionRound j ≤ N) →
      ∃ v, Decided w U V (x 0) v := by
  intro h
  induction h with
  | zero =>
    intro x hR _ hlead hN
    obtain ⟨A, -, -, hA⟩ :=
      commitsOfSynchrony hw hT hcard hs hpop (by rw [hid]; exact hR) hN hV hlead
    exact ⟨some A, hA⟩
  | succ h ih =>
    intro x hR hhop hlead hN
    have hhop0 : FloorHop w U V (x 0) (x 1) := hhop 0 (by omega)
    have hR1 : R ≤ x 1 := le_trans hR (by have := hhop0.1; have := hw (x 0); omega)
    obtain ⟨v, hv⟩ := ih (fun i => x (i + 1)) hR1 (fun i hi => hhop (i + 1) (by omega)) hlead hN
    obtain ⟨A, rfl⟩ : ∃ A, v = some A := by
      cases v with
      | none => exact absurd hv hhop0.2.2
      | some A => exact ⟨A, rfl⟩
    exact decidedOfCommitAboveFloor hw hid hhop0.1 hv hhop0.2.1

/-- **SH6i.** A reliably led landing commits (SH6a), and a view decides a slot one way, so a
skipped round is never reliably led. If none of the first `n − |T|` landings were reliably led,
neither would be any round from a landing's floor up to the next landing, those being the skips
the hop passes over, and `roundRobin_hop_bound` would contradict `ws · (n − |T|) < n`. -/
theorem floorChainReachesReliable {U : BlockUniverse Validator BlockId Payload} {w : ℕ → ℕ}
    {ws n : ℕ} (hn : 0 < n) (hwr : ∀ r, w r = ws) (hws : 3 ≤ ws) (hid : ∀ t, S.slotRound t = t)
    {T : Finset Validator} {V : View Validator BlockId Payload U} {R N : ℕ}
    (hT : T ⊆ (Correct : Finset Validator)) (hcard : quorumCard Validator ≤ T.card)
    (hs : SynchronisedOn U T R) (hpop : ∀ r, R ≤ r → r ≤ N → PopulatedOn U T r)
    (hV : V.CoversUpto N) {lead : Fin n → Validator} (hbij : Function.Bijective lead)
    (hsched : ∀ t, S.leader t = lead ⟨t % n, Nat.mod_lt t hn⟩) (hlt : ws * (n - T.card) < n)
    {x : ℕ → ℕ} (hR : R ≤ x 0) (hhop : ∀ i, i < n - T.card → FloorHop w U V (x i) (x (i + 1)))
    (hN : ∀ j, j ≤ x (n - T.card) →
      (steelheadAnchored Validator BlockId Payload w).decisionRound j ≤ N) :
    ∃ i, i ≤ n - T.card ∧ S.leader (x i) ∈ T := by
  classical
  have hw3 : ∀ r, 3 ≤ w r := fun r => by rw [hwr r]; exact hws
  by_contra hcon
  have hno : ∀ i, i ≤ n - T.card → S.leader (x i) ∉ T := fun i hi hmem => hcon ⟨i, hi, hmem⟩
  have hstep : ∀ i, i < n - T.card → x i + ws ≤ x (i + 1) := by
    intro i hi
    have := (hhop i hi).1
    rwa [hwr] at this
  -- the chain climbs, so every round it visits lies between its first and last landing
  have hgrow : ∀ d i, i + d ≤ n - T.card → x i ≤ x (i + d) := by
    intro d
    induction d with
    | zero => intro i _; simp
    | succ d ih =>
      intro i hi
      have h1 := ih i (by omega)
      have h2 := hstep (i + d) (by omega)
      rw [show i + (d + 1) = i + d + 1 by omega]
      omega
  have hmono : ∀ a b, a ≤ b → b ≤ n - T.card → x a ≤ x b := by
    intro a b hab hb
    have := hgrow (b - a) a (by omega)
    rwa [show a + (b - a) = b by omega] at this
  -- a skipped round is not reliably led: SH6a would commit it, and a view decides one way
  have hnotT : ∀ t, x 0 ≤ t → t ≤ x (n - T.card) → Decided w U V t none → S.leader t ∉ T := by
    intro t ht0 htm hskip hmem
    obtain ⟨L, -, -, hcommit⟩ := commitsOfSynchrony hw3 hT hcard hs hpop
      (by rw [hid]; omega) (fun j hj => hN j (by omega)) hV hmem
    have hagree := AnchoredRule.decided_agree
      (steelheadLaws (fun r => by have := hw3 r; omega)) trivial hcommit hskip
    simp at hagree
  exact roundRobin_hop_bound hn (by omega) hbij hsched rfl hlt hstep hno
    fun i hi t ht1 ht2 =>
      hnotT t (le_trans (hmono 0 i (by omega) (by omega)) (by omega))
        (le_trans (le_of_lt ht2) (hmono (i + 1) (n - T.card) (by omega) le_rfl))
        ((hhop i hi).2.1 t (by rw [hwr]; omega) ht2)

/-! ## SH6c, SH6e -/

/-- **SH6c.** Every reliable block at the vote round blames a slot whose leader has no block at
the slot's round, since no candidate lies in any cone, and a view holding that round holds a
quorum of them. -/
theorem skipsCrashed {U : BlockUniverse Validator BlockId Payload} {w : ℕ → ℕ}
    {T : Finset Validator} {V : View Validator BlockId Payload U} {k : ℕ}
    (hcard : quorumCard Validator ≤ T.card)
    (hcrash : ∀ L ∈ U.ids, (U.block L).round = S.slotRound k → (U.block L).creator ≠ S.leader k)
    (hpop : PopulatedOn U T (MahiMahi.votingRound (w (S.slotRound k)) (S.slotRound k)))
    (hV : V.CoversUpto (MahiMahi.votingRound (w (S.slotRound k)) (S.slotRound k))) :
    Decided w U V k none := by
  refine Decided.directSkip ?_
  change MahiMahi.DirectSkipIn U V (w (S.slotRound k)) (S.leader k) (S.slotRound k)
  unfold MahiMahi.DirectSkipIn HoldsAtLeast
  refine le_trans hcard (Finset.card_le_card fun v hv => ?_)
  obtain ⟨q, hq, hqc, hqr⟩ := hpop v hv
  refine mem_heldAuthors.mpr ⟨q, Finset.mem_filter.mpr ⟨mem_blocksAt.mpr ⟨hq, hqr⟩, ?_⟩,
    hV q hq (le_of_eq hqr), hqc⟩
  unfold MahiMahi.Blames
  refine Finset.eq_empty_of_forall_notMem fun L hL => ?_
  obtain ⟨hLids, hLr, hLc, -⟩ := MahiMahi.mem_candidatesAt.mp hL
  exact hcrash L hLids hLr hLc

/-- **SH6l.** A landing the view does not skip is not led by a crashed validator, since a crashed
leader's slot is directly skipped once the reliable set populates its vote round (SH6c); so a
landing led from outside `T` is Byzantine-led, the skips between landings are not reliably led
(SH6a and one verdict per slot, as in SH6i), and `roundRobin_byzantine_hop_bound` bounds the
chain by the Byzantine validators. -/
theorem floorChainReachesReliableWithinByzantine {U : BlockUniverse Validator BlockId Payload}
    {w : ℕ → ℕ} {ws n : ℕ} (hn : 0 < n) (hwr : ∀ r, w r = ws) (hws : 3 ≤ ws)
    (hid : ∀ t, S.slotRound t = t) {T : Finset Validator} {V : View Validator BlockId Payload U}
    {R N : ℕ} (hT : T ⊆ (Correct : Finset Validator)) (hcard : quorumCard Validator ≤ T.card)
    (hs : SynchronisedOn U T R) (hpop : ∀ r, R ≤ r → r ≤ N → PopulatedOn U T r)
    (hV : V.CoversUpto N)
    (hcrash : ∀ v, v ∉ T → v ∉ F.byzantine →
      ∀ L ∈ U.ids, R ≤ (U.block L).round → (U.block L).creator ≠ v)
    {lead : Fin n → Validator} (hbij : Function.Bijective lead)
    (hsched : ∀ t, S.leader t = lead ⟨t % n, Nat.mod_lt t hn⟩) (hlt : ws * (n - T.card) < n)
    {x : ℕ → ℕ} (hR : R ≤ x 0) (hstart : ¬ Decided w U V (x 0) none)
    (hhop : ∀ i, i < F.byzantine.card → FloorHop w U V (x i) (x (i + 1)))
    (hN : ∀ j, j ≤ x F.byzantine.card →
      (steelheadAnchored Validator BlockId Payload w).decisionRound j ≤ N) :
    ∃ i, i ≤ F.byzantine.card ∧ S.leader (x i) ∈ T := by
  classical
  have hw3 : ∀ r, 3 ≤ w r := fun r => by rw [hwr r]; exact hws
  by_contra hcon
  have hno : ∀ i, i ≤ F.byzantine.card → S.leader (x i) ∉ T :=
    fun i hi hmem => hcon ⟨i, hi, hmem⟩
  have hstep : ∀ i, i < F.byzantine.card → x i + ws ≤ x (i + 1) := by
    intro i hi
    have := (hhop i hi).1
    rwa [hwr] at this
  -- the chain climbs, so every round it visits lies between its first and last landing
  have hgrow : ∀ d i, i + d ≤ F.byzantine.card → x i ≤ x (i + d) := by
    intro d
    induction d with
    | zero => intro i _; simp
    | succ d ih =>
      intro i hi
      have h1 := ih i (by omega)
      have h2 := hstep (i + d) (by omega)
      rw [show i + (d + 1) = i + d + 1 by omega]
      omega
  have hmono : ∀ a b, a ≤ b → b ≤ F.byzantine.card → x a ≤ x b := by
    intro a b hab hb
    have := hgrow (b - a) a (by omega)
    rwa [show a + (b - a) = b by omega] at this
  -- no landing is skipped: the first by hypothesis, the others by the hop that reaches them
  have hunskipped : ∀ i, i ≤ F.byzantine.card → ¬ Decided w U V (x i) none := by
    intro i hi
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · exact hstart
    · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
      exact (hhop i' (by omega)).2.2
  -- so no landing is led by a crashed validator: its slot would be directly skipped (SH6c)
  have hbyz : ∀ i, i ≤ F.byzantine.card → S.leader (x i) ∈ F.byzantine := by
    intro i hi
    by_contra hnb
    have hRi : R ≤ x i := le_trans hR (hmono 0 i (by omega) hi)
    have hdec := hN (x i) (hmono i _ hi le_rfl)
    simp only [AnchoredRule.decisionRound, steelheadAnchored_waveAt, hid, hwr] at hdec
    have hvote : R ≤ MahiMahi.votingRound (w (S.slotRound (x i))) (S.slotRound (x i)) ∧
        MahiMahi.votingRound (w (S.slotRound (x i))) (S.slotRound (x i)) ≤ N := by
      unfold MahiMahi.votingRound
      rw [hid, hwr]
      omega
    refine hunskipped i hi (skipsCrashed hcard (fun L hL hLr => ?_) (hpop _ hvote.1 hvote.2)
      (hV.mono hvote.2))
    rw [hid] at hLr
    exact hcrash _ (hno i hi) hnb L hL (by rw [hLr]; exact hRi)
  -- a skipped round is not reliably led: SH6a would commit it, and a view decides one way
  have hnotT : ∀ t, x 0 ≤ t → t ≤ x F.byzantine.card → Decided w U V t none →
      S.leader t ∉ T := by
    intro t ht0 htm hskip hmem
    obtain ⟨L, -, -, hcommit⟩ := commitsOfSynchrony hw3 hT hcard hs hpop
      (by rw [hid]; omega) (fun j hj => hN j (by omega)) hV hmem
    have hagree := AnchoredRule.decided_agree
      (steelheadLaws (fun r => by have := hw3 r; omega)) trivial hcommit hskip
    simp at hagree
  exact roundRobin_byzantine_hop_bound hn (by omega) hT hbij hsched hlt hstep hbyz
    fun i hi t ht1 ht2 =>
      hnotT t (le_trans (hmono 0 i (by omega) (by omega)) (by omega))
        (le_trans (le_of_lt ht2) (hmono (i + 1) F.byzantine.card (by omega) le_rfl))
        ((hhop i hi).2.1 t (by rw [hwr]; omega) ht2)

omit S in
/-- A block reaching the only block of its author at a round votes for it: `Votes` asks for the
least candidate of that author and round in the cone, and there is one. -/
theorem votes_of_reaches_of_unique {U : BlockUniverse Validator BlockId Payload} {q L : BlockId}
    (hq : q ∈ U.ids) (hL : L ∈ U.ids)
    (huniq : ∀ L' ∈ U.ids, (U.block L').round = (U.block L).round →
      (U.block L').creator = (U.block L).creator → L' = L)
    (h : Reaches U q L) : MahiMahi.Votes U q L := by
  refine ⟨MahiMahi.mem_candidatesAt.mpr ⟨hL, rfl, rfl, (mem_history_iff hq).mpr h⟩, ?_⟩
  intro L' hL' hlt
  obtain ⟨hL'ids, hL'r, hL'c, -⟩ := MahiMahi.mem_candidatesAt.mp hL'
  rw [huniq L' hL'ids hL'r hL'c] at hlt
  exact lt_irrefl _ hlt

omit S [LinearOrder BlockId] in
/-- Under synchrony from `R`, a block one reliable round-`R` block references lies in the cone of
every reliable block at the rounds past `R` the reliable set populates: each reliable block
references every reliable block one round down, one of which reaches it. -/
theorem reaches_of_synchronised_of_ref {U : BlockUniverse Validator BlockId Payload}
    {T : Finset Validator} {R N : ℕ} {L q : BlockId} (hcard : quorumCard Validator ≤ T.card)
    (hs : SynchronisedOn U T R) (hpop : ∀ r, R ≤ r → r ≤ N → PopulatedOn U T r)
    (hq : q ∈ U.ids) (hqr : (U.block q).round = R) (hqT : (U.block q).creator ∈ T)
    (hqL : L ∈ (U.block q).refs) :
    ∀ c ∈ U.ids, R + 1 ≤ (U.block c).round → (U.block c).round ≤ N →
      (U.block c).creator ∈ T → Reaches U c L := by
  suffices H : ∀ m, R + 1 ≤ m → m ≤ N → ∀ c ∈ U.ids, (U.block c).round = m →
      (U.block c).creator ∈ T → Reaches U c L by
    intro c hc h1 h2 hcT
    exact H _ h1 h2 c hc rfl hcT
  intro m hm
  induction m, hm using Nat.le_induction with
  | base =>
    intro _ c hc hcr hcT
    exact Reaches.trans (Reaches.single (hs R le_rfl c hc hcr hcT q hq hqr hqT))
      (Reaches.single hqL)
  | succ m hRm ih =>
    intro hmN c hc hcr hcT
    obtain ⟨v, hv⟩ := MahiMahi.nonempty_of_quorum hcard
    obtain ⟨b, hb, hbc, hbr⟩ := hpop m (by omega) (by omega) v hv
    exact Reaches.trans (Reaches.single (hs m (by omega) c hc hcr hcT b hb hbr (hbc ▸ hv)))
      (ih (by omega) b hb hbr (hbc ▸ hv))

/-- **SH6e.** Synchrony carries the candidate into every reliable cone from two rounds up; the
reliable voters vote for it, the leader's only block at its round; every reliable block at the
decision round references all of them and so certifies; and a view holding the decision round
holds those certificates. -/
theorem commitsOfDissemination {U : BlockUniverse Validator BlockId Payload} {w : ℕ → ℕ}
    {T : Finset Validator} {V : View Validator BlockId Payload U} {k : ℕ} {L q : BlockId}
    (hw : 4 ≤ w (S.slotRound k)) (hcard : quorumCard Validator ≤ T.card)
    (hL : IsLeaderBlock U k L)
    (huniq : ∀ L' ∈ U.ids, (U.block L').round = S.slotRound k →
      (U.block L').creator = S.leader k → L' = L)
    (hq : q ∈ U.ids) (hqr : (U.block q).round = S.slotRound k + 1) (hqT : (U.block q).creator ∈ T)
    (hqL : L ∈ (U.block q).refs) (hs : SynchronisedOn U T (S.slotRound k + 1))
    (hpop : ∀ r, S.slotRound k + 1 ≤ r →
      r ≤ MahiMahi.decisionRoundAt (w (S.slotRound k)) (S.slotRound k) → PopulatedOn U T r)
    (hV : V.CoversUpto (MahiMahi.decisionRoundAt (w (S.slotRound k)) (S.slotRound k))) :
    Decided w U V k (some L) := by
  have hreach := reaches_of_synchronised_of_ref hcard hs hpop hq hqr hqT hqL
  have huniq' : ∀ L' ∈ U.ids, (U.block L').round = (U.block L).round →
      (U.block L').creator = (U.block L).creator → L' = L :=
    fun L' h1 h2 h3 => huniq L' h1 (h2.trans hL.2.1) (h3.trans hL.2.2)
  -- every reliable block at the decision round certifies L
  have hcert : ∀ C ∈ U.ids,
      (U.block C).round = MahiMahi.decisionRoundAt (w (S.slotRound k)) (S.slotRound k) →
      (U.block C).creator ∈ T →
      C ∈ MahiMahi.certificates U (w (S.slotRound k)) L (S.slotRound k) := by
    intro C hC hCr hCT
    refine mem_certificatesAt.mpr ⟨hC, hCr, ?_⟩
    unfold CarriesVotes
    refine le_trans hcard (Finset.card_le_card fun v hv => ?_)
    obtain ⟨b, hb, hbc, hbr⟩ := hpop (MahiMahi.votingRound (w (S.slotRound k)) (S.slotRound k))
      (by unfold MahiMahi.votingRound; omega)
      (by unfold MahiMahi.votingRound MahiMahi.decisionRoundAt; omega) v hv
    refine mem_creatorsOf.mpr ⟨b, mem_carriedVotes.mpr ⟨?_, ?_⟩, hbc⟩
    · refine hs (MahiMahi.votingRound (w (S.slotRound k)) (S.slotRound k))
        (by unfold MahiMahi.votingRound; omega) C hC ?_ hCT b hb hbr (hbc ▸ hv)
      rw [hCr]
      unfold MahiMahi.votingRound MahiMahi.decisionRoundAt
      omega
    · refine votes_of_reaches_of_unique hb hL.1 huniq' (hreach b hb ?_ ?_ (hbc ▸ hv))
      · rw [hbr]; unfold MahiMahi.votingRound; omega
      · rw [hbr]; unfold MahiMahi.votingRound MahiMahi.decisionRoundAt; omega
  -- so L is directly committed, and the view holds the certificates
  have hdc : MahiMahi.DirectCommit U (w (S.slotRound k)) L (S.slotRound k) := by
    unfold MahiMahi.DirectCommit
    refine le_trans hcard (Finset.card_le_card fun v hv => ?_)
    obtain ⟨C, hC, hCc, hCr⟩ := hpop _ (by unfold MahiMahi.decisionRoundAt; omega) le_rfl v hv
    exact mem_creatorsOf.mpr ⟨C, hcert C hC hCr (hCc ▸ hv), hCc⟩
  exact Decided.directCommit hL (MahiMahiProperties.directCommitIn_of_coversUpto hdc hV)

end Slots

/-! ## SH7 — the chain -/

/-- At the identity schedule a run of `wa` slots spans, at wave `wa`. -/
theorem chainSpansEligible {wa : ℕ} (hwa : 1 ≤ wa) (coin : ℕ → Validator) :
    (MahiMahi.mahiMahiAnchored Validator BlockId Payload wa).SpansEligible
      (S := chainSlots coin) wa := by
  have := (MahiMahi.mahiMahiAnchored Validator BlockId Payload wa).spansEligible_of_identity
    (S := chainSlots coin) (fun _ => rfl) (w := wa - 1) (fun _ => le_rfl)
  rwa [Nat.sub_add_cancel hwa] at this

/-- **SH7c.** The core's descent below a run of direct commits, at the chain schedule: the run's
commits are direct, and a view holding their decision rounds holds their certificates. -/
theorem chainAllDecidedBelowOfRun {U : BlockUniverse Validator BlockId Payload} {wa : ℕ}
    (hwa : 1 ≤ wa) {coin : ℕ → Validator} {V : View Validator BlockId Payload U} {b : ℕ}
    (hgood : ∀ i, i < wa → coin (b + i) ∈ MahiMahi.goodAt U wa (b + i))
    (hV : V.CoversUpto (MahiMahi.decisionRoundAt wa (b + wa - 1))) :
    ∀ i, i < b → ∃ v, ChainDecided wa coin U V i v := by
  refine AnchoredRule.decided_below_of_run (S := chainSlots coin)
    (fun hi h => MahiMahi.exists_least (S := chainSlots coin) hi h) hwa
    (chainSpansEligible hwa coin) (Led := fun j => coin j ∈ MahiMahi.goodAt U wa j) hgood
    fun j _ hj2 hj => ?_
  obtain ⟨L, hL, hLr, hLc, hdc⟩ := MahiMahi.mem_goodAt.mp hj
  refine ⟨L, MahiMahi.Decided.directCommit (S := chainSlots coin) ⟨hL, hLr, hLc⟩
    (MahiMahiProperties.directCommitIn_of_coversUpto hdc (hV.mono ?_))⟩
  change MahiMahi.decisionRoundAt wa j ≤ MahiMahi.decisionRoundAt wa (b + wa - 1)
  unfold MahiMahi.decisionRoundAt
  omega

/-- **SH7a.** MM3c at the chain schedule, in any view caught up to the horizon: the clause names
a run past `r`, and SH7c settles everything below it. -/
theorem chainAllDecidedBelow {U : BlockUniverse Validator BlockId Payload} {wa : ℕ}
    (hwa : 1 ≤ wa) {coin : ℕ → Validator} {V : View Validator BlockId Payload U} {c N : ℕ}
    (hrun : MahiMahi.UnpredictableRunWithin (S := chainSlots coin) U wa c wa N)
    (hV : V.CoversUpto N) (r : ℕ) (hr : MahiMahi.decisionRoundAt wa (r + c + wa - 1) ≤ N) :
    ∃ b, r ≤ b ∧ ∀ i, i < b → ∃ v, ChainDecided wa coin U V i v := by
  obtain ⟨k', hk1, hk2, hgood⟩ := hrun r (by
    rw [MahiMahi.mahiMahiAnchored_decisionRound (S := chainSlots coin) hwa]; exact hr)
  refine ⟨k', hk1, chainAllDecidedBelowOfRun hwa hgood (hV.mono ?_)⟩
  unfold MahiMahi.decisionRoundAt at hr ⊢
  omega

/-- **SH7b.** The timed descent at Mahi-Mahi's support, at the chain schedule. -/
theorem chainAllDecidedBelowOfSynchrony {wa : ℕ} (hwa : 4 ≤ wa) (coin : ℕ → Validator)
    {T : Finset Validator} (hT : T ⊆ (Correct : Finset Validator))
    (hcard : quorumCard Validator ≤ T.card) (fair : FairRunOn (S := chainSlots coin) T wa)
    (R k : ℕ) :
    ∃ b, k ≤ b ∧ R ≤ b ∧
      ∀ (U : BlockUniverse Validator BlockId Payload) (V : View Validator BlockId Payload U)
        (N : ℕ),
        SynchronisedOn U T R → (∀ r, R ≤ r → r ≤ N → PopulatedOn U T r) →
        V.CoversUpto N → MahiMahi.decisionRoundAt wa (b + wa - 1) ≤ N →
        ∀ i, i < b → ∃ v, ChainDecided wa coin U V i v := by
  have hd : Descends (MahiMahiProperties.mahiMahiRule (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload) wa) (chainSlots coin) wa :=
    Descends.of_indirect (MahiMahiProperties.indirect (by omega)) (by omega)
      (fun b i hi => by change i + wa ≤ b + wa - 1; omega)
  obtain ⟨b, hb, hRb, h⟩ := Timed.decidedBelow_of_fairRun (MahiMahiProperties.mmSupport wa)
    (MahiMahiProperties.mmSupport_ofCoverage hwa) (MahiMahiProperties.mmSupport_commits (by omega))
    hd (isQuorum_core hT hcard) fair R k
  refine ⟨b, hb, hRb, fun U V N hs hpop hV hN i hi => ?_⟩
  obtain ⟨v, hv⟩ := h V N hs hpop hV (fun j hj => by
    change j + (wa - 1) ≤ N
    unfold MahiMahi.decisionRoundAt at hN
    omega) i hi
  exact ⟨v, hv.2.1⟩

/-! ## SH8 — the stall -/

section Stall

variable [S : Slots Validator] {U : BlockUniverse Validator BlockId Payload}
  {V : View Validator BlockId Payload U} {ws wa k : ℕ}

/-- The wavelength at a synchronous round is `ws`. -/
theorem periodic_of_not_isAsync {r : ℕ} (h : ¬ IsAsync k r) : periodic ws wa k r = ws := by
  unfold IsAsync at h
  simp [periodic, h]

/-- The residue class `k − 1` is synchronous, at `2 ≤ k`. -/
theorem not_isAsync_of_mod {i : ℕ} (hk : 2 ≤ k) (hi : i % k = k - 1) : ¬ IsAsync k i := by
  unfold IsAsync; omega

/-- **A synchronous slot never commits** when no synchronous candidate of the slots `Q` names is
certified: the direct commit and the link both need a certificate. -/
theorem not_commit_sync_of_pred (hid : ∀ s, S.slotRound s = s) {Q : ℕ → Prop}
    (hcert : ∀ (j : ℕ) (L : BlockId), Q j → ¬ IsAsync k j → IsLeaderBlock U j L →
      MahiMahi.certificates U ws L j = ∅)
    {j : ℕ} {A : BlockId} (hQ : Q j) (hj : ¬ IsAsync k j)
    (h : Decided (periodic ws wa k) U V j (some A)) : False := by
  have hne : (MahiMahi.certificates U ws A j).Nonempty := by
    cases h with
    | directCommit hL hc =>
      change MahiMahi.DirectCommitIn U V (periodic ws wa k (S.slotRound j)) A (S.slotRound j) at hc
      rw [hid, periodic_of_not_isAsync hj] at hc
      exact MahiMahi.certificates_nonempty_of_directCommit
        (MahiMahi.directCommit_of_directCommitIn hc)
    | indirectCommit _ _ _ _ _ _ _ hlink _ =>
      change MahiMahi.CertifiedIn U (periodic ws wa k (S.slotRound j)) _ A (S.slotRound j) at hlink
      rw [hid, periodic_of_not_isAsync hj] at hlink
      exact MahiMahi.certificates_nonempty_of_certifiedIn hlink
  rw [hcert j A hQ hj (AnchoredRule.isLeaderBlock_of_decided h)] at hne
  exact Finset.not_nonempty_empty hne

/-- **A synchronous slot never commits** when no synchronous candidate is
certified: the direct commit and the link both need a certificate. -/
theorem not_commit_sync (hid : ∀ s, S.slotRound s = s)
    (hcert : ∀ (j : ℕ) (L : BlockId), ¬ IsAsync k j → IsLeaderBlock U j L →
      MahiMahi.certificates U ws L j = ∅)
    {j : ℕ} {A : BlockId} (hj : ¬ IsAsync k j)
    (h : Decided (periodic ws wa k) U V j (some A)) : False :=
  not_commit_sync_of_pred hid (Q := fun _ => True) (fun j L _ => hcert j L) trivial hj h

/-- An asynchronous round above `i + 1`, where `i ≡ k − 1`, lies a full
period above `i`: the arithmetic `omega` cannot do at a variable modulus. -/
theorem add_period_le_of_isAsync {i j : ℕ} (hk : 2 ≤ k) (hi : i % k = k - 1) (hj : IsAsync k j)
    (hij : i + 2 ≤ j) : i + k + 1 ≤ j := by
  unfold IsAsync at hj
  have hi' := Nat.div_add_mod i k
  have hj' := Nat.div_add_mod j k
  rw [hi] at hi'
  rw [hj] at hj'
  have hlt : k * (i / k + 1) < k * (j / k) := by
    have e : k * (i / k + 1) = k * (i / k) + k := by rw [Nat.mul_add, Nat.mul_one]
    omega
  have hq : i / k + 1 < j / k := Nat.lt_of_mul_lt_mul_left hlt
  have : k * (i / k + 2) ≤ k * (j / k) := Nat.mul_le_mul_left k hq
  rw [Nat.mul_add] at this
  omega

/-- **SH8, at the slots a view can decide.** Induction on the derivation: a class-`(k − 1)`
slot's direct verdicts are excluded outright, a synchronous anchor never commits, and an
asynchronous anchor leaves the class-`(k − 1)` slot one period up as an eligible slot between,
which must be skipped, which is the claim one period up. The certificate and skip hypotheses are
asked at the slots `Q` names, which every slot a derivation in `V` mentions satisfies; on a view
that reaches no further than some round, that is the slots below it. -/
theorem stall_of_pred (hws : 2 ≤ ws) (hk : ws ≤ k) (hid : ∀ s, S.slotRound s = s) {Q : ℕ → Prop}
    (hQ : ∀ (j : ℕ) (v : Option BlockId), Decided (periodic ws wa k) U V j v → Q j)
    (hcert : ∀ (j : ℕ) (L : BlockId), Q j → ¬ IsAsync k j → IsLeaderBlock U j L →
      MahiMahi.certificates U ws L j = ∅)
    (hskip : ∀ j, Q j → ¬ IsAsync k j → ¬ MahiMahi.DirectSkipIn U V ws (S.leader j) j)
    {i : ℕ} (hi : i % k = k - 1) {v : Option BlockId}
    (h : Decided (periodic ws wa k) U V i v) : False := by
  have hk2 : 2 ≤ k := le_trans hws hk
  -- the middle slot of an asynchronous anchor's search is one period up
  have hmid_of_async : ∀ {i j : ℕ}, i % k = k - 1 → IsAsync k j →
      (steelheadAnchored Validator BlockId Payload (periodic ws wa k)).Eligible i j →
      i < i + k ∧ i + k < j ∧
        (steelheadAnchored Validator BlockId Payload (periodic ws wa k)).Eligible i (i + k) := by
    intro i j hi hj helig
    have hsync := not_isAsync_of_mod hk2 hi
    rw [AnchoredRule.eligible_iff] at helig ⊢
    simp only [steelheadAnchored_waveAt, hid, periodic_of_not_isAsync hsync] at helig ⊢
    have := add_period_le_of_isAsync hk2 hi hj (by omega)
    omega
  revert hi
  induction h with
  | @directCommit j L hL hc =>
    intro hi
    exact not_commit_sync_of_pred hid hcert (hQ j _ (Decided.directCommit hL hc))
      (not_isAsync_of_mod hk2 hi) (Decided.directCommit hL hc)
  | @directSkip j hs =>
    intro hi
    have hj := not_isAsync_of_mod hk2 hi
    have hQj := hQ j none (Decided.directSkip hs)
    change MahiMahi.DirectSkipIn U V (periodic ws wa k (S.slotRound j)) (S.leader j)
      (S.slotRound j) at hs
    rw [hid, periodic_of_not_isAsync hj] at hs
    exact hskip j hQj hj hs
  | @indirectCommit i j A L _ hkj helig hj hmid _ _ _ _ _ _ ihmid =>
    intro hi
    by_cases hasync : IsAsync k j
    · obtain ⟨h1, h2, h3⟩ := hmid_of_async hi hasync helig
      exact ihmid (i + k) h1 h2 h3 (by rw [Nat.add_mod_right]; exact hi)
    · exact not_commit_sync_of_pred hid hcert (hQ j _ hj) hasync hj
  | @indirectSkip i j A hkj helig hj hmid _ _ ihmid =>
    intro hi
    by_cases hasync : IsAsync k j
    · obtain ⟨h1, h2, h3⟩ := hmid_of_async hi hasync helig
      exact ihmid (i + k) h1 h2 h3 (by rw [Nat.add_mod_right]; exact hi)
    · exact not_commit_sync_of_pred hid hcert (hQ j _ hj) hasync hj

/-- **SH8.** `stall_of_pred` with nothing asked of the slots. -/
theorem stall (hws : 2 ≤ ws) (hk : ws ≤ k) (hid : ∀ s, S.slotRound s = s)
    (hcert : ∀ (j : ℕ) (L : BlockId), ¬ IsAsync k j → IsLeaderBlock U j L →
      MahiMahi.certificates U ws L j = ∅)
    (hskip : ∀ j, ¬ IsAsync k j → ¬ MahiMahi.DirectSkipIn U V ws (S.leader j) j)
    {i : ℕ} (hi : i % k = k - 1) {v : Option BlockId}
    (h : Decided (periodic ws wa k) U V i v) : False :=
  stall_of_pred hws hk hid (Q := fun _ => True) (fun _ _ _ => trivial) (fun j L _ => hcert j L)
    (fun j _ => hskip j) hi h

end Stall

/-! ## SH9 — the drain -/

section Drain

variable [S : Slots Validator] {U : BlockUniverse Validator BlockId Payload}

/-- At one slot per round, `wa` consecutive slots span eligibility at every wavelength function
bounded by `wa`. -/
theorem spansEligible_of_le {w : ℕ → ℕ} {wa : ℕ} (hwa : 1 ≤ wa) (hle : ∀ r, w r ≤ wa)
    (hid : ∀ s, S.slotRound s = s) :
    (steelheadAnchored Validator BlockId Payload w).SpansEligible (S := S) wa := by
  have := (steelheadAnchored Validator BlockId Payload w).spansEligible_of_identity (S := S) hid
    (w := wa - 1) (fun r => by simp only [steelheadAnchored_waveAt]; have := hle r; omega)
  rwa [Nat.sub_add_cancel hwa] at this

/-- **SH9.** The relation's descent below a committed run, at each slot's own wave. -/
theorem allDecidedBelowOfRun {w : ℕ → ℕ} {wa : ℕ} {V : View Validator BlockId Payload U} {b : ℕ}
    (hw : ∀ r, 1 ≤ w r) (hle : ∀ r, w r ≤ wa) (hid : ∀ s, S.slotRound s = s)
    (hrun : ∀ i, i < wa → ∃ L, Decided w U V (b + i) (some L)) :
    ∀ i, i < b → ∃ v, Decided w U V i v := by
  have hwa : 1 ≤ wa := le_trans (hw 0) (hle 0)
  exact AnchoredRule.decided_below_of_run (fun hi h => exists_least hi h) hwa
    (spansEligible_of_le hwa hle hid) (Led := fun j => ∃ L, Decided w U V j (some L)) hrun
    fun j _ _ hj => hj

/-- The period-one wavelength is `wa` at every round. -/
theorem periodic_one {ws wa : ℕ} (r : ℕ) : periodic ws wa 1 r = wa := by
  simp [periodic, Nat.mod_one]

/-- **SH9b.** SH7a's argument at the output schedule: the clause names a run of `wa` committed
leaders past `r`, each committed directly in a view holding its decision round, and the run
decides everything below it (SH9). -/
theorem allDecidedBelowAtPeriodOne {ws wa : ℕ} (hwa : 1 ≤ wa) {V : View Validator BlockId Payload U}
    (hid : ∀ s, S.slotRound s = s) {c N : ℕ}
    (hrun : MahiMahi.UnpredictableRunWithin (S := S) U wa c wa N) (hV : V.CoversUpto N) (r : ℕ)
    (hr : MahiMahi.decisionRoundAt wa (r + c + wa - 1) ≤ N) :
    ∃ b, r ≤ b ∧ ∀ i, i < b → ∃ v, Decided (periodic ws wa 1) U V i v := by
  obtain ⟨k', hk1, hk2, hgood⟩ := hrun r (by
    rw [MahiMahi.mahiMahiAnchored_decisionRound (S := S) hwa, hid]; exact hr)
  refine ⟨k', hk1, allDecidedBelowOfRun (fun r => by rw [periodic_one]; exact hwa)
    (fun r => le_of_eq (periodic_one r)) hid fun i hi => ?_⟩
  obtain ⟨L, hL, hLr, hLc, hdc⟩ := MahiMahi.mem_goodAt.mp (hgood i hi)
  refine ⟨L, Decided.directCommit ⟨hL, hLr, hLc⟩ ?_⟩
  change MahiMahi.DirectCommitIn U V (periodic ws wa 1 (S.slotRound (k' + i))) L
    (S.slotRound (k' + i))
  rw [periodic_one]
  refine MahiMahiProperties.directCommitIn_of_coversUpto hdc (hV.mono ?_)
  rw [hid]
  unfold MahiMahi.decisionRoundAt at hr ⊢
  omega

/-- **SH9c.** Decision rounds at the periodic wavelength: `r + wa − 1` at an asynchronous round,
`r + ws − 1` at a synchronous one; the rest is arithmetic. -/
theorem asyncSlotCost {ws wa k : ℕ} (hid : ∀ s, S.slotRound s = s) (hws : 1 ≤ ws) (hwa : ws ≤ wa)
    {r : ℕ} (hr : IsAsync k r) :
    (steelheadAnchored Validator BlockId Payload (periodic ws wa k)).decisionRound (S := S) r =
      (steelheadAnchored Validator BlockId Payload (fun _ => ws)).decisionRound (S := S) r +
        (wa - ws) ∧
    ∀ i, 1 ≤ i → i < k →
      (steelheadAnchored Validator BlockId Payload (periodic ws wa k)).decisionRound (S := S) r ≤
        (steelheadAnchored Validator BlockId Payload (periodic ws wa k)).decisionRound (S := S)
          (r + i) + (wa - ws - i) := by
  have hasync : periodic ws wa k r = wa := by unfold IsAsync at hr; simp [periodic, hr]
  refine ⟨?_, fun i hi hik => ?_⟩
  · unfold AnchoredRule.decisionRound
    simp only [steelheadAnchored_waveAt, hid, hasync]
    omega
  · have hsync : periodic ws wa k (r + i) = ws := by
      refine periodic_of_not_isAsync ?_
      unfold IsAsync at hr ⊢
      rw [Nat.add_mod, hr, zero_add, Nat.mod_mod, Nat.mod_eq_of_lt hik]
      omega
    unfold AnchoredRule.decisionRound
    simp only [steelheadAnchored_waveAt, hid, hasync, hsync]
    omega

end Drain

end Steelhead

end LeanDag
