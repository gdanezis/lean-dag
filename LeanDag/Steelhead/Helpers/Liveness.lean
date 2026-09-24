import LeanDag.Steelhead.Liveness.Statement
import LeanDag.Steelhead.Helpers.Decision
import LeanDag.Steelhead.Helpers.Safety
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Group.Action.Defs
/-!
# Helpers — the liveness layer

Generated lemma infrastructure for `Liveness/Statement.lean`; not part of
the audit surface. The round-robin arithmetic reads the schedule alone.
Every other lemma reads its rule through the clauses: a reliably led slot
commits by `CommitsUnderSync`, a slot is decided below a commit by the
relation's own anchor step (`AnchoredRule.exists_decided_of_anchor`) at
the rule's `LeastLinked`, and a skipped slot is not reliably led because
a lawful rule decides a slot one way. The Mahi-Mahi pair's instances are
in `Helpers/MahiMahiPair/Liveness.lean`.
-/

namespace LeanDag

namespace Steelhead

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type} [LinearOrder BlockId] {Payload : Type}

/-! ## SH6g — the round-robin schedule -/

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

/-- **SH6g.** A validator outside `T` leads one residue, which spoils the `c` windows ending at
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

/-- **SH6g, the near half.** A window of `n − |T| + 1` consecutive rounds leads that many
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

/-! ## SH6h — the hop count -/

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

/-- **A span of `q` cycles holds at most `q · ⌈n / p⌉` multiples of `p`.** Two multiples of `p`
lie `p` apart, so the map carrying a multiple to its distance above the span's foot, divided by
`p`, is injective into a range of that size. -/
theorem card_multiples_le {n p : ℕ} (hp : 0 < p) (a q : ℕ) :
    ((Finset.Ico a (a + n * q)).filter fun t => t % p = 0).card ≤ q * ((n + p - 1) / p) := by
  set c := (n + p - 1) / p with hc
  -- `p · ⌈n / p⌉` is at least `n`, so the span fits in `q · c` blocks of `p`
  have hpc : n ≤ p * c := by
    have h1 : p * c + (n + p - 1) % p = n + p - 1 := by rw [hc]; exact Nat.div_add_mod _ _
    have h2 : (n + p - 1) % p < p := Nat.mod_lt _ hp
    omega
  have hspan : n * q ≤ q * c * p := by
    calc n * q ≤ (p * c) * q := Nat.mul_le_mul_right q hpc
      _ = q * c * p := by
        rw [Nat.mul_comm (p * c) q, Nat.mul_comm p c, ← Nat.mul_assoc]
  -- two distinct multiples of `p` sit at least `p` apart, so their quotients differ
  have hsep : ∀ u v : ℕ, u % p = 0 → v % p = 0 → u < v → a ≤ u →
      (u - a) / p < (v - a) / p := by
    intro u v hu hv huv hau
    have hdiff : p ≤ v - u := Nat.le_of_dvd (by omega)
      (Nat.dvd_sub (Nat.dvd_of_mod_eq_zero hv) (Nat.dvd_of_mod_eq_zero hu))
    calc (u - a) / p < (u - a) / p + 1 := Nat.lt_succ_self _
      _ = (u - a + p) / p := (Nat.add_div_right _ hp).symm
      _ ≤ (v - a) / p := Nat.div_le_div_right (by omega)
  have hle : ((Finset.Ico a (a + n * q)).filter fun t => t % p = 0).card ≤
      (Finset.range (q * c)).card := by
    refine Finset.card_le_card_of_injOn (fun t => (t - a) / p) (fun t ht => ?_)
      (fun t ht t' ht' heq => ?_)
    · obtain ⟨hmem, -⟩ := Finset.mem_filter.mp ht
      obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hmem
      exact Finset.mem_range.mpr ((Nat.div_lt_iff_lt_mul hp).mpr (by omega))
    · obtain ⟨hmem, hdvd⟩ := Finset.mem_filter.mp ht
      obtain ⟨hmem', hdvd'⟩ := Finset.mem_filter.mp ht'
      have hlo := (Finset.mem_Ico.mp hmem).1
      have hlo' := (Finset.mem_Ico.mp hmem').1
      rcases Nat.lt_trichotomy t t' with h | h | h
      · exact absurd heq (Nat.ne_of_lt (hsep t t' hdvd hdvd' h hlo))
      · exact h
      · exact absurd heq.symm (Nat.ne_of_lt (hsep t' t hdvd' hdvd h hlo'))
  rwa [Finset.card_range] at hle

omit [DecidableEq Validator] F in
/-- The committee a bijection from `Fin n` names has `n` members. -/
theorem card_eq_of_bijective {n : ℕ} {lead : Fin n → Validator}
    (hbij : Function.Bijective lead) : Fintype.card Validator = n := by
  have := Fintype.card_of_bijective hbij
  simpa using this.symm

omit [Fintype Validator] [DecidableEq Validator] F in
/-- **Two landings of the floor chain never share a residue**, with the rounds an exempt
predicate covers left out of the count. A chain that advances by at least `ws` rounds a hop,
whose landings are led from outside `T` and whose rounds from a landing's floor up to the next
landing are too or exempt, cannot have two landings at one residue: between two such landings
lies a whole number of cycles, each holding `T.card` reliably led rounds, and every one of them
must fall in the `ws − 1` rounds a hop leaves free or among the `c` exempt rounds a cycle holds,
which forces `n ≤ ws · (n − T.card) + ws · c`. The exemption is what a period costs: a round the
coin leads is led by nobody the schedule names, so the count cannot claim it. -/
theorem roundRobin_residues_distinct_exempt {n ws m c : ℕ} (hn : 0 < n) (hws : 1 ≤ ws)
    {T : Finset Validator} {lead : Fin n → Validator} (hbij : Function.Bijective lead)
    {sched : ℕ → Validator} (hsched : ∀ t, sched t = lead ⟨t % n, Nat.mod_lt t hn⟩)
    {Ex : ℕ → Prop} [DecidablePred Ex]
    (hex : ∀ a q, ((Finset.Ico a (a + n * q)).filter Ex).card ≤ q * c)
    (hTcard : T.card ≤ n) (hlt : ws * (n - T.card) + ws * c < n)
    {x : ℕ → ℕ} (hstep : ∀ i, i < m → x i + ws ≤ x (i + 1))
    (hbad : ∀ i, i ≤ m → sched (x i) ∉ T)
    (hmid : ∀ i, i < m → ∀ t, x i + ws ≤ t → t < x (i + 1) → Ex t ∨ sched t ∉ T) :
    ∀ i j, i < j → j ≤ m → x i % n ≠ x j % n := by
  classical
  set e : Fin n ≃ Validator := Equiv.ofBijective lead hbij with he
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
  -- and each of those rounds falls in the rounds one hop leaves free, or is exempt
  set Exm : Finset ℕ := (Finset.Ico (x i) (x j)).filter Ex with hExm
  have hup : Led.card ≤ (j - i) * (ws - 1) + Exm.card := by
    have hfree : (Led.filter fun t => ¬ Ex t).card ≤ (j - i) * (ws - 1) := by
      have hsub : (Led.filter fun t => ¬ Ex t) ⊆
          (Finset.Ico i j).biUnion fun k => Finset.Ioo (x k) (x k + ws) := by
        intro t ht
        obtain ⟨htLed, htEx⟩ := Finset.mem_filter.mp ht
        obtain ⟨htIco, htT⟩ := Finset.mem_filter.mp htLed
        obtain ⟨ht1, ht2⟩ := Finset.mem_Ico.mp htIco
        obtain ⟨k, hk1, hk2, hk3, hk4⟩ := exists_hop_index hij ht1 ht2
        refine Finset.mem_biUnion.mpr ⟨k, Finset.mem_Ico.mpr ⟨hk1, hk2⟩,
          Finset.mem_Ioo.mpr ⟨?_, ?_⟩⟩
        · rcases Nat.eq_or_lt_of_le hk3 with heq | hlt'
          · exact absurd (heq ▸ htT) (hbad k (by omega))
          · exact hlt'
        · by_contra hge
          rcases hmid k (by omega) t (by omega) hk4 with hEx | hnT
          · exact htEx hEx
          · exact hnT htT
      refine le_trans (Finset.card_le_card hsub) (le_trans Finset.card_biUnion_le ?_)
      calc ∑ k ∈ Finset.Ico i j, (Finset.Ioo (x k) (x k + ws)).card
          ≤ ∑ _k ∈ Finset.Ico i j, (ws - 1) :=
            Finset.sum_le_sum fun k _ => by rw [Nat.card_Ioo]; omega
        _ = (j - i) * (ws - 1) := by rw [Finset.sum_const, Nat.card_Ico, smul_eq_mul]
    have hexm : (Led.filter Ex).card ≤ Exm.card :=
      Finset.card_le_card fun t ht => by
        obtain ⟨htLed, htEx⟩ := Finset.mem_filter.mp ht
        exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp htLed).1, htEx⟩
    have hsplit := Finset.card_filter_add_card_filter_not (s := Led) (p := Ex)
    omega
  -- the exempt rounds of the span number at most `q · c`
  have hexq : Exm.card ≤ q * c := by
    have := hex (x i) q
    rwa [show x i + n * q = x j by omega] at this
  -- the two counts meet only at `n ≤ ws · (n − T.card) + ws · c`
  have hdn : (j - i) * ws ≤ n * q := by omega
  have h1 : ws * (T.card * q) ≤ ws * ((j - i) * (ws - 1) + q * c) :=
    Nat.mul_le_mul_left ws (le_trans hlow (by omega))
  have h2 : ws * ((j - i) * (ws - 1) + q * c) = ((j - i) * ws) * (ws - 1) + q * (ws * c) := by
    rw [Nat.mul_add]
    congr 1
    · rw [Nat.mul_comm ws ((j - i) * (ws - 1)), Nat.mul_assoc, Nat.mul_comm (ws - 1) ws,
        ← Nat.mul_assoc]
    · rw [← Nat.mul_assoc, Nat.mul_comm ws q, Nat.mul_assoc]
  have h3 : ((j - i) * ws) * (ws - 1) ≤ (n * q) * (ws - 1) :=
    Nat.mul_le_mul_right (ws - 1) hdn
  have h4 : q * (ws * T.card) ≤ q * (n * (ws - 1) + ws * c) := by
    have hleft : ws * (T.card * q) = q * (ws * T.card) := by
      rw [Nat.mul_comm T.card q, ← Nat.mul_assoc, Nat.mul_comm ws q, Nat.mul_assoc]
    have hright : (n * q) * (ws - 1) + q * (ws * c) = q * (n * (ws - 1) + ws * c) := by
      rw [Nat.mul_add, Nat.mul_comm n q, Nat.mul_assoc]
    rw [← hleft, ← hright]
    exact le_trans h1 (le_trans (le_of_eq h2) (by omega))
  have h5 : ws * T.card ≤ n * (ws - 1) + ws * c := Nat.le_of_mul_le_mul_left h4 (by omega)
  have h6 : n * (ws - 1) = n * ws - n := by
    rw [Nat.mul_sub, Nat.mul_one]
  have h7 : ws * (n - T.card) = ws * n - ws * T.card := Nat.mul_sub ws n T.card
  have h8 : ws * n = n * ws := Nat.mul_comm ws n
  have h9 : ws * T.card ≤ ws * n := Nat.mul_le_mul_left ws hTcard
  have h10 : n ≤ n * ws := Nat.le_mul_of_pos_right n (by omega)
  omega

omit [DecidableEq Validator] F in
/-- **Two landings of the floor chain never share a residue.** The constant-wave case, where no
round is exempt and the count keeps every cycle's `T.card` reliably led rounds. -/
theorem roundRobin_residues_distinct {n ws m : ℕ} (hn : 0 < n) (hws : 1 ≤ ws) {T : Finset Validator}
    {lead : Fin n → Validator} (hbij : Function.Bijective lead) {sched : ℕ → Validator}
    (hsched : ∀ t, sched t = lead ⟨t % n, Nat.mod_lt t hn⟩) (hlt : ws * (n - T.card) < n)
    {x : ℕ → ℕ} (hstep : ∀ i, i < m → x i + ws ≤ x (i + 1))
    (hbad : ∀ i, i ≤ m → sched (x i) ∉ T)
    (hmid : ∀ i, i < m → ∀ t, x i + ws ≤ t → t < x (i + 1) → sched t ∉ T) :
    ∀ i j, i < j → j ≤ m → x i % n ≠ x j % n :=
  roundRobin_residues_distinct_exempt (c := 0) hn hws hbij hsched (Ex := fun _ => False)
    (fun _ _ => by simp) (by rw [← card_eq_of_bijective hbij]; exact Finset.card_le_univ T)
    (by simpa using hlt) hstep hbad fun i hi t ht1 ht2 => Or.inr (hmid i hi t ht1 ht2)

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

omit [Fintype Validator] [DecidableEq Validator] F in
/-- **The count that bounds the floor chain (SH6h, SH6o).** The landings' residues are distinct
(`roundRobin_residues_distinct_exempt`), and only the `n − T.card` residues outside `T` are open
to them, so a chain of that many hops led from outside `T` throughout cannot exist. The exempt
predicate is empty at a constant wave and the coin's rounds at a period. -/
theorem roundRobin_hop_bound_exempt {n ws m c : ℕ} (hn : 0 < n) (hws : 1 ≤ ws)
    {T : Finset Validator} {lead : Fin n → Validator} (hbij : Function.Bijective lead)
    {sched : ℕ → Validator} (hsched : ∀ t, sched t = lead ⟨t % n, Nat.mod_lt t hn⟩)
    {Ex : ℕ → Prop} [DecidablePred Ex]
    (hex : ∀ a q, ((Finset.Ico a (a + n * q)).filter Ex).card ≤ q * c)
    (hm : m = n - T.card) (hlt : ws * (n - T.card) + ws * c < n)
    {x : ℕ → ℕ} (hstep : ∀ i, i < m → x i + ws ≤ x (i + 1))
    (hbad : ∀ i, i ≤ m → sched (x i) ∉ T)
    (hmid : ∀ i, i < m → ∀ t, x i + ws ≤ t → t < x (i + 1) → Ex t ∨ sched t ∉ T) : False := by
  classical
  letI : Fintype Validator := Fintype.ofBijective lead hbij
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
  have key := roundRobin_residues_distinct_exempt hn hws hbij hsched hex
    (by rw [← hcard]; exact Finset.card_le_univ T) hlt hstep hbad hmid
  rcases Nat.lt_or_ge i j with h | h
  · exact key i j h (by omega) hres
  · exact key j i (by omega) (by omega) hres.symm

omit [Fintype Validator] [DecidableEq Validator] F in
/-- **The count that bounds the floor chain (SH6h).** The constant-wave case of
`roundRobin_hop_bound_exempt`, where no round is exempt. -/
theorem roundRobin_hop_bound {n ws m : ℕ} (hn : 0 < n) (hws : 1 ≤ ws) {T : Finset Validator}
    {lead : Fin n → Validator} (hbij : Function.Bijective lead) {sched : ℕ → Validator}
    (hsched : ∀ t, sched t = lead ⟨t % n, Nat.mod_lt t hn⟩) (hm : m = n - T.card)
    (hlt : ws * m < n) {x : ℕ → ℕ} (hstep : ∀ i, i < m → x i + ws ≤ x (i + 1))
    (hbad : ∀ i, i ≤ m → sched (x i) ∉ T)
    (hmid : ∀ i, i < m → ∀ t, x i + ws ≤ t → t < x (i + 1) → sched t ∉ T) : False :=
  roundRobin_hop_bound_exempt (c := 0) hn hws hbij hsched (Ex := fun _ => False)
    (fun _ _ => by simp) hm (by simpa using hm ▸ hlt) hstep hbad
    fun i hi t ht1 ht2 => Or.inr (hmid i hi t ht1 ht2)

/-- **The count that bounds the floor chain by the Byzantine validators (SH6h′, SH6p).** Landings
led by Byzantine validators occupy at most `|byzantine|` residues, and the landings' residues are
distinct (`roundRobin_residues_distinct_exempt`), so a chain of that many hops whose landings are
all Byzantine-led cannot exist. The exempt predicate is empty at a constant wave and the coin's
rounds at a period. -/
theorem roundRobin_byzantine_hop_bound_exempt {n ws c : ℕ} (hn : 0 < n) (hws : 1 ≤ ws)
    {T : Finset Validator} (hT : T ⊆ (Correct : Finset Validator)) {lead : Fin n → Validator}
    (hbij : Function.Bijective lead) {sched : ℕ → Validator}
    (hsched : ∀ t, sched t = lead ⟨t % n, Nat.mod_lt t hn⟩)
    {Ex : ℕ → Prop} [DecidablePred Ex]
    (hex : ∀ a q, ((Finset.Ico a (a + n * q)).filter Ex).card ≤ q * c)
    (hlt : ws * (n - T.card) + ws * c < n)
    {x : ℕ → ℕ} (hstep : ∀ i, i < F.byzantine.card → x i + ws ≤ x (i + 1))
    (hbyz : ∀ i, i ≤ F.byzantine.card → sched (x i) ∈ F.byzantine)
    (hmid : ∀ i, i < F.byzantine.card → ∀ t, x i + ws ≤ t → t < x (i + 1) →
      Ex t ∨ sched t ∉ T) :
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
  have key := roundRobin_residues_distinct_exempt hn hws hbij hsched hex
    (by rw [← card_eq_of_bijective hbij]; exact Finset.card_le_univ T) hlt hstep hbad hmid
  rcases Nat.lt_or_ge i j with h | h
  · exact key i j h (by omega) hres
  · exact key j i (by omega) (by omega) hres.symm

/-- **The count that bounds the floor chain by the Byzantine validators (SH6h′).** The
constant-wave case of `roundRobin_byzantine_hop_bound_exempt`, where no round is exempt. -/
theorem roundRobin_byzantine_hop_bound {n ws : ℕ} (hn : 0 < n) (hws : 1 ≤ ws)
    {T : Finset Validator} (hT : T ⊆ (Correct : Finset Validator)) {lead : Fin n → Validator}
    (hbij : Function.Bijective lead) {sched : ℕ → Validator}
    (hsched : ∀ t, sched t = lead ⟨t % n, Nat.mod_lt t hn⟩) (hlt : ws * (n - T.card) < n)
    {x : ℕ → ℕ} (hstep : ∀ i, i < F.byzantine.card → x i + ws ≤ x (i + 1))
    (hbyz : ∀ i, i ≤ F.byzantine.card → sched (x i) ∈ F.byzantine)
    (hmid : ∀ i, i < F.byzantine.card → ∀ t, x i + ws ≤ t → t < x (i + 1) → sched t ∉ T) :
    False :=
  roundRobin_byzantine_hop_bound_exempt (c := 0) hn hws hT hbij hsched (Ex := fun _ => False)
    (fun _ _ => by simp) (by simpa using hlt) hstep hbyz
    fun i hi t ht1 ht2 => Or.inr (hmid i hi t ht1 ht2)

omit F in
/-- **SH6n.** Every window of `n` rounds holds one round of each residue, so `T.card` of them are
reliably led; at most `⌈n / p⌉` carry a coin instead (`card_multiples_le`), so one reliably led
round of the window is synchronous. -/
theorem periodicRoundRobinReliableSync {n p : ℕ} (hn : 0 < n) (hp : 0 < p) {T : Finset (Fin n)}
    (hlt : (n + p - 1) / p < T.card) (r : ℕ) :
    ∃ a, r ≤ a ∧ a ≤ r + (n - 1) ∧ periodicKind p a ≠ 1 ∧
      (⟨a % n, Nat.mod_lt a hn⟩ : Fin n) ∈ T := by
  classical
  by_contra hcon
  -- every reliably led round of the window carries a coin
  have hall : ∀ a, r ≤ a → a ≤ r + (n - 1) → (⟨a % n, Nat.mod_lt a hn⟩ : Fin n) ∈ T →
      a % p = 0 := by
    intro a h1 h2 hmem
    by_contra hzero
    refine hcon ⟨a, h1, h2, ?_, hmem⟩
    unfold periodicKind
    rw [if_neg hzero]
    decide
  -- but the window holds one round of each residue, and too few coins to cover them all
  have hinj : T.card ≤ ((Finset.Ico r (r + n)).filter fun t => t % p = 0).card := by
    refine Finset.card_le_card_of_injOn (fun v : Fin n => r + ((v : ℕ) + n - r % n) % n)
      (fun v hv => ?_) (fun v _ v' _ heq => ?_)
    · obtain ⟨off, hoffeq, hoff⟩ : ∃ off, ((v : ℕ) + n - r % n) % n = off ∧ off < n :=
        ⟨_, rfl, Nat.mod_lt _ hn⟩
      have hres : (r + off) % n = (v : ℕ) := by
        rw [← hoffeq]; exact mod_add_offset hn r v v.isLt
      change r + ((v : ℕ) + n - r % n) % n ∈ _
      rw [hoffeq]
      refine Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by omega, by omega⟩, ?_⟩
      refine hall _ (by omega) (by omega) ?_
      have hfin : (⟨(r + off) % n, Nat.mod_lt _ hn⟩ : Fin n) = v := Fin.ext hres
      rw [hfin]
      exact hv
    · have h1 : (r + ((v : ℕ) + n - r % n) % n) % n = (v : ℕ) := mod_add_offset hn r v v.isLt
      have h2 : (r + ((v' : ℕ) + n - r % n) % n) % n = (v' : ℕ) := mod_add_offset hn r v' v'.isLt
      exact Fin.ext (by rw [← h1, ← h2]; exact congrArg (· % n) heq)
  have hmul := card_multiples_le (n := n) (p := p) hp r 1
  rw [Nat.mul_one, Nat.one_mul] at hmul
  exact absurd (le_trans hinj hmul) (Nat.not_le.mpr hlt)

/-- A chain whose hops each advance at least one round climbs: every landing up to `m` lies at or
above every earlier one. -/
theorem chain_mono {x : ℕ → ℕ} {m : ℕ} (hstep : ∀ i, i < m → x i + 1 ≤ x (i + 1)) :
    ∀ a b, a ≤ b → b ≤ m → x a ≤ x b := by
  intro a b hab hb
  have hgrow : ∀ d i, i + d ≤ m → x i ≤ x (i + d) := by
    intro d
    induction d with
    | zero => intro i _; simp
    | succ d ih =>
      intro i hi
      have h1 := ih i (by omega)
      have h2 := hstep (i + d) (by omega)
      rw [show i + (d + 1) = i + d + 1 by omega]
      omega
  have := hgrow (b - a) a (by omega)
  rwa [show a + (b - a) = b by omega] at this

section Slots

variable [S : Slots Validator] {R : AnchoredRule Validator BlockId Payload ValidWrt Correct}

/-! ## SH6a, SH6c — the clauses compose -/

omit [LinearOrder BlockId] in
/-- **SH6a.** The composite's decision round and direct commit at a slot are the slot's rule's,
so the clause at that rule is the clause at the composite. -/
theorem commitsUnderSync_compose {U : BlockUniverse Validator BlockId Payload}
    {rules : ℕ → AnchoredRule Validator BlockId Payload ValidWrt Correct}
    (h : ∀ κ, CommitsUnderSync (rules κ) U) : CommitsUnderSync (compose rules) U :=
  fun T V R₀ N k hT hcard hs hpop hR hN hV hlead =>
    h (S.kind k) T V R₀ N k hT hcard hs hpop hR hN hV hlead

omit [LinearOrder BlockId] in
/-- **SH6c.** The composite's direct skip and decision round at a slot are the slot's rule's. -/
theorem skipsSilent_compose {U : BlockUniverse Validator BlockId Payload}
    {rules : ℕ → AnchoredRule Validator BlockId Payload ValidWrt Correct}
    (h : ∀ κ, SkipsSilent (rules κ) U) : SkipsSilent (compose rules) U :=
  fun T V k hcard hcrash hpop hV => h (S.kind k) T V k hcard hcrash hpop hV

omit S [LinearOrder BlockId] in
/-- **The composite's tie-break has a choice** at every nonempty rung once every rule's does and
the family agrees on its rung count and tie-break: a rung of the composite at a slot is the rung
of the slot's rule. -/
theorem leastLinked_compose {rules : ℕ → AnchoredRule Validator BlockId Payload ValidWrt Correct}
    (h : ∀ κ, LeastLinked (rules κ)) (hr : ∀ κ, (rules κ).rungs = (rules 0).rungs)
    (ht : ∀ κ, (rules κ).tie = (rules 0).tie) : LeastLinked (compose rules) := by
  intro S U A i k hi hex
  obtain ⟨L, hL, hlink, hleast⟩ := h (S.kind k) (by rw [hr]; exact hi) hex
  refine ⟨L, hL, hlink, fun L' hL' hlink' => ?_⟩
  change ¬ (rules 0).tie i L' L
  rw [← ht (S.kind k)]
  exact hleast L' hL' hlink'

/-! ## SH6b — everything below a fair run -/

omit [LinearOrder BlockId] in
/-- A run of `c` slots spans only if `c` is positive: its last slot must clear a slot below its
first. -/
theorem pos_of_spansEligible {c : ℕ} (hspan : R.SpansEligible c) : 0 < c := by
  have := R.lt_of_eligible (hspan 1 0 (by omega))
  omega

/-- **SH6b.** The fair run lies past both the slot and the synchrony round; each of its slots
commits by the clause, and the descent below a committed run decides everything under it. -/
theorem allDecidedBelowOfSynchrony (hleast : LeastLinked R)
    (hcu : ∀ U, CommitsUnderSync R U) {T : Finset Validator} {c : ℕ}
    (hT : T ⊆ (Correct : Finset Validator)) (hcard : quorumCard Validator ≤ T.card)
    (hspan : R.SpansEligible c) (fair : FairRunOn T c) (R₀ k : ℕ) :
    ∃ b, k ≤ b ∧ R₀ ≤ S.slotRound b ∧
      ∀ (U : BlockUniverse Validator BlockId Payload) (V : View Validator BlockId Payload U)
        (N : ℕ),
        SynchronisedOn U T R₀ → (∀ r, R₀ ≤ r → r ≤ N → PopulatedOn U T r) →
        V.CoversUpto N → (∀ j, j < b + c → R.decisionRound j ≤ N) →
        ∀ i, i < b → ∃ v, R.Decided U V i v := by
  obtain ⟨k₀, hk₀⟩ := S.unbounded R₀
  obtain ⟨b, hb, hrun⟩ := fair (max k k₀)
  have hRb : R₀ ≤ S.slotRound b := le_trans hk₀ (S.mono (le_trans (le_max_right k k₀) hb))
  have hc := pos_of_spansEligible hspan
  refine ⟨b, le_trans (le_max_left _ _) hb, hRb, fun U V N hs hpop hV hN => ?_⟩
  refine AnchoredRule.decided_below_of_run (fun hi h => hleast hi h) hc hspan
    (Led := fun j => S.leader j ∈ T) hrun fun j hj1 hj2 hj => ?_
  obtain ⟨L, hL, hcom⟩ := hcu U T V R₀ N j hT hcard hs hpop (le_trans hRb (S.mono hj1))
    (hN j (by omega)) hV hj
  exact ⟨L, AnchoredRule.Decided.directCommit hL hcom⟩

/-! ## SH6e, SH6f, SH6m — the anchor below a commit -/

omit [LinearOrder BlockId] in
/-- At one slot per round a slot is eligible for another exactly when it lies past the other's
decision round. -/
theorem eligible_iff_of_identity (hid : ∀ t, S.slotRound t = t) {k j : ℕ} :
    R.Eligible k j ↔ k + R.waveAt (S.kind k) + 1 ≤ j := by
  rw [R.eligible_iff, hid, hid]

/-- A commit past a slot's decision round, with every slot between skipped, decides the slot: the
anchor search reads the commit as the anchor and passes over the skips. -/
theorem decidedOfCommitAboveFloor {U : BlockUniverse Validator BlockId Payload}
    (hleast : LeastLinked R) (hid : ∀ t, S.slotRound t = t)
    {V : View Validator BlockId Payload U} {k a : ℕ} {A : BlockId}
    (hka : k + R.waveAt (S.kind k) + 1 ≤ a) (hA : R.Decided U V a (some A))
    (hmid : ∀ j, k + R.waveAt (S.kind k) + 1 ≤ j → j < a → R.Decided U V j none) :
    ∃ v, R.Decided U V k v :=
  AnchoredRule.exists_decided_of_anchor (fun hi h => hleast hi h)
    ((eligible_iff_of_identity hid).mpr hka) hA
    fun m _ hm he => hmid m ((eligible_iff_of_identity hid).mp he) hm

/-- **SH6e.** The reliably led slot commits by the clause, so the least commit past the floor is
an anchor, and every slot between, decided but not committed, is a skip. -/
theorem decidedOfReliableAboveFloor {U : BlockUniverse Validator BlockId Payload}
    (hleast : LeastLinked R) (hcu : CommitsUnderSync R U) (hid : ∀ t, S.slotRound t = t)
    {T : Finset Validator} {V : View Validator BlockId Payload U} {R₀ N k a : ℕ}
    (hT : T ⊆ (Correct : Finset Validator)) (hcard : quorumCard Validator ≤ T.card)
    (hs : SynchronisedOn U T R₀) (hpop : ∀ r, R₀ ≤ r → r ≤ N → PopulatedOn U T r) (hR : R₀ ≤ k)
    (hka : k + R.waveAt (S.kind k) + 1 ≤ a) (hlead : S.leader a ∈ T)
    (hdec : ∀ j, k + R.waveAt (S.kind k) + 1 ≤ j → j < a → ∃ v, R.Decided U V j v)
    (hN : R.decisionRound a ≤ N) (hV : V.CoversUpto N) : ∃ v, R.Decided U V k v := by
  classical
  obtain ⟨A, hAL, hAc⟩ := hcu T V R₀ N a hT hcard hs hpop (by rw [hid]; omega) hN hV hlead
  have hA : R.Decided U V a (some A) := AnchoredRule.Decided.directCommit hAL hAc
  -- the least committed slot past the floor
  have hex : ∃ j, k + R.waveAt (S.kind k) + 1 ≤ j ∧ ∃ A, R.Decided U V j (some A) :=
    ⟨a, hka, A, hA⟩
  obtain ⟨hkj, A', hA'⟩ := Nat.find_spec hex
  have hja : Nat.find hex ≤ a := Nat.find_le ⟨hka, A, hA⟩
  -- every slot between the floor and it is decided but not committed, so skipped
  refine decidedOfCommitAboveFloor hleast hid hkj hA' fun j hj1 hj2 => ?_
  have hnc : ¬ ∃ C, R.Decided U V j (some C) := fun hc => Nat.find_min hex hj2 ⟨hj1, hc⟩
  obtain ⟨v, hv⟩ := hdec j hj1 (by omega)
  cases v with
  | none => exact hv
  | some C => exact absurd ⟨C, hv⟩ hnc

/-- **SH6f.** Downward induction on the chain: the last landing commits by the clause, and a
landing whose successor commits is decided, the slots between them being the skips the search
passes over; the hop leaves it unskipped, so it commits in turn and anchors the landing below. -/
theorem floorChainDecides {U : BlockUniverse Validator BlockId Payload}
    (hleast : LeastLinked R) (hcu : CommitsUnderSync R U) (hid : ∀ t, S.slotRound t = t)
    {T : Finset Validator} {V : View Validator BlockId Payload U} {R₀ N : ℕ}
    (hT : T ⊆ (Correct : Finset Validator)) (hcard : quorumCard Validator ≤ T.card)
    (hs : SynchronisedOn U T R₀) (hpop : ∀ r, R₀ ≤ r → r ≤ N → PopulatedOn U T r)
    (hV : V.CoversUpto N) :
    ∀ (h : ℕ) (x : ℕ → ℕ), R₀ ≤ x 0 → (∀ i, i < h → FloorHopOf R U V (x i) (x (i + 1))) →
      S.leader (x h) ∈ T → R.decisionRound (x h) ≤ N → ∃ v, R.Decided U V (x 0) v := by
  intro h
  induction h with
  | zero =>
    intro x hR _ hlead hN
    obtain ⟨A, hAL, hAc⟩ :=
      hcu T V R₀ N (x 0) hT hcard hs hpop (by rw [hid]; exact hR) hN hV hlead
    exact ⟨some A, AnchoredRule.Decided.directCommit hAL hAc⟩
  | succ h ih =>
    intro x hR hhop hlead hN
    have hhop0 : FloorHopOf R U V (x 0) (x 1) := hhop 0 (by omega)
    have hR1 : R₀ ≤ x 1 := le_trans hR (by have := hhop0.1; omega)
    obtain ⟨v, hv⟩ := ih (fun i => x (i + 1)) hR1 (fun i hi => hhop (i + 1) (by omega)) hlead hN
    obtain ⟨A, rfl⟩ : ∃ A, v = some A := by
      cases v with
      | none => exact absurd hv hhop0.2.2
      | some A => exact ⟨A, rfl⟩
    exact decidedOfCommitAboveFloor hleast hid hhop0.1 hv hhop0.2.1

/-- **SH6m.** The descent alone: the last landing commits, and a landing whose successor commits
is decided and left unskipped by its own hop, so it commits in turn and anchors the landing below
it. No quorum, no synchrony and no horizon: those were only ever how SH6f came by the top
commit. -/
theorem floorChainDecidesFromCommit {U : BlockUniverse Validator BlockId Payload}
    (hleast : LeastLinked R) (hid : ∀ t, S.slotRound t = t)
    {V : View Validator BlockId Payload U} :
    ∀ (h : ℕ) (x : ℕ → ℕ), (∀ i, i < h → FloorHopOf R U V (x i) (x (i + 1))) →
      (∃ A, R.Decided U V (x h) (some A)) → ∃ v, R.Decided U V (x 0) v := by
  intro h
  induction h with
  | zero =>
    intro x _ hcom
    obtain ⟨A, hA⟩ := hcom
    exact ⟨some A, hA⟩
  | succ h ih =>
    intro x hhop hcom
    have hhop0 : FloorHopOf R U V (x 0) (x 1) := hhop 0 (by omega)
    obtain ⟨v, hv⟩ := ih (fun i => x (i + 1)) (fun i hi => hhop (i + 1) (by omega)) hcom
    obtain ⟨A, rfl⟩ : ∃ A, v = some A := by
      cases v with
      | none => exact absurd hv hhop0.2.2
      | some A => exact ⟨A, rfl⟩
    exact decidedOfCommitAboveFloor hleast hid hhop0.1 hv hhop0.2.1

/-! ## SH6h, SH6i, SH6j — the hop count at one wave -/

omit [LinearOrder BlockId] in
/-- **A skipped slot is not reliably led**, under synchrony: the clause would commit it, and a
lawful rule decides a slot one way. -/
theorem leader_not_mem_of_skip {U : BlockUniverse Validator BlockId Payload} (hl : R.Laws)
    (hcu : CommitsUnderSync R U) {T : Finset Validator} {V : View Validator BlockId Payload U}
    {R₀ N t : ℕ} (hT : T ⊆ (Correct : Finset Validator)) (hcard : quorumCard Validator ≤ T.card)
    (hs : SynchronisedOn U T R₀) (hpop : ∀ r, R₀ ≤ r → r ≤ N → PopulatedOn U T r)
    (hV : V.CoversUpto N) (hR : R₀ ≤ S.slotRound t) (hN : R.decisionRound t ≤ N)
    (hskip : R.Decided U V t none) : S.leader t ∉ T := fun hmem => by
  obtain ⟨L, hL, hc⟩ := hcu T V R₀ N t hT hcard hs hpop hR hN hV hmem
  have := AnchoredRule.decided_agree hl trivial (AnchoredRule.Decided.directCommit hL hc) hskip
  simp at this

omit [LinearOrder BlockId] in
/-- No landing of a chain is skipped: the first by hypothesis, the others by the hop that reaches
them. -/
theorem unskipped_of_hops {U : BlockUniverse Validator BlockId Payload}
    {V : View Validator BlockId Payload U} {x : ℕ → ℕ} {m : ℕ}
    (hstart : ¬ R.Decided U V (x 0) none)
    (hhop : ∀ i, i < m → FloorHopOf R U V (x i) (x (i + 1))) :
    ∀ i, i ≤ m → ¬ R.Decided U V (x i) none := by
  intro i hi
  rcases Nat.eq_zero_or_pos i with rfl | hpos
  · exact hstart
  · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    exact (hhop i' (by omega)).2.2

omit [LinearOrder BlockId] in
/-- **A landing is not led by a crashed validator**: its slot would be directly skipped
(`SkipsSilent`) once the reliable set populates the rounds above it, and a landing is a slot the
view does not skip. -/
theorem byzantine_of_unskipped {U : BlockUniverse Validator BlockId Payload}
    (hsk : SkipsSilent R U) {T : Finset Validator} {V : View Validator BlockId Payload U}
    {R₀ N t : ℕ} (hcard : quorumCard Validator ≤ T.card)
    (hpop : ∀ r, R₀ ≤ r → r ≤ N → PopulatedOn U T r) (hV : V.CoversUpto N)
    (hcrash : ∀ v, v ∉ T → v ∉ F.byzantine →
      ∀ L ∈ U.ids, R₀ ≤ (U.block L).round → (U.block L).creator ≠ v)
    (hR : R₀ ≤ S.slotRound t) (hN : R.decisionRound t ≤ N) (hunskip : ¬ R.Decided U V t none)
    (hno : S.leader t ∉ T) : S.leader t ∈ F.byzantine := by
  by_contra hnb
  refine hunskip (AnchoredRule.Decided.directSkip
    (hsk T V t hcard (fun L hL hLr => hcrash _ hno hnb L hL (by rw [hLr]; exact hR))
      (fun r hr1 hr2 => hpop r (by omega) (le_trans hr2 hN)) (hV.mono hN)))

omit [LinearOrder BlockId] in
/-- **SH6h.** A reliably led landing commits by the clause, and a lawful rule decides a slot one
way, so a skipped round is never reliably led. If none of the first `n − |T|` landings were
reliably led, neither would be any round the hops pass over, and `roundRobin_hop_bound` would
contradict `ws · (n − |T|) < n`. -/
theorem floorChainReachesReliable {U : BlockUniverse Validator BlockId Payload} {ws n : ℕ}
    (hn : 0 < n) (hl : R.Laws) (hcu : CommitsUnderSync R U)
    (hwr : ∀ t, R.waveAt (S.kind t) + 1 = ws) (hid : ∀ t, S.slotRound t = t)
    {T : Finset Validator} {V : View Validator BlockId Payload U} {R₀ N : ℕ}
    (hT : T ⊆ (Correct : Finset Validator)) (hcard : quorumCard Validator ≤ T.card)
    (hs : SynchronisedOn U T R₀) (hpop : ∀ r, R₀ ≤ r → r ≤ N → PopulatedOn U T r)
    (hV : V.CoversUpto N) {lead : Fin n → Validator} (hbij : Function.Bijective lead)
    (hsched : ∀ t, S.leader t = lead ⟨t % n, Nat.mod_lt t hn⟩) (hlt : ws * (n - T.card) < n)
    {x : ℕ → ℕ} (hR : R₀ ≤ x 0)
    (hhop : ∀ i, i < n - T.card → FloorHopOf R U V (x i) (x (i + 1)))
    (hN : ∀ j, j ≤ x (n - T.card) → R.decisionRound j ≤ N) :
    ∃ i, i ≤ n - T.card ∧ S.leader (x i) ∈ T := by
  classical
  have hws : 1 ≤ ws := by have := hwr 0; omega
  by_contra hcon
  have hno : ∀ i, i ≤ n - T.card → S.leader (x i) ∉ T := fun i hi hmem => hcon ⟨i, hi, hmem⟩
  have hstep : ∀ i, i < n - T.card → x i + ws ≤ x (i + 1) := by
    intro i hi
    have := (hhop i hi).1
    have := hwr (x i)
    omega
  have hmono := chain_mono (x := x) (m := n - T.card) fun i hi => by have := hstep i hi; omega
  exact roundRobin_hop_bound hn hws hbij hsched rfl hlt hstep hno fun i hi t ht1 ht2 =>
    leader_not_mem_of_skip hl hcu hT hcard hs hpop hV
      (by rw [hid]; exact le_trans hR (le_trans (hmono 0 i (by omega) (by omega)) (by omega)))
      (hN t (le_trans (le_of_lt ht2) (hmono (i + 1) (n - T.card) (by omega) le_rfl)))
      ((hhop i hi).2.1 t (by have := hwr (x i); omega) ht2)

omit [LinearOrder BlockId] in
/-- **SH6i.** A landing the view does not skip is not led by a crashed validator (`SkipsSilent`),
so a landing led from outside `T` is Byzantine-led; the skips between landings are not reliably
led, as in SH6h; and `roundRobin_byzantine_hop_bound` bounds the chain by the Byzantine
validators. -/
theorem floorChainReachesReliableWithinByzantine {U : BlockUniverse Validator BlockId Payload}
    {ws n : ℕ} (hn : 0 < n) (hl : R.Laws) (hcu : CommitsUnderSync R U) (hsk : SkipsSilent R U)
    (hwr : ∀ t, R.waveAt (S.kind t) + 1 = ws) (hid : ∀ t, S.slotRound t = t)
    {T : Finset Validator} {V : View Validator BlockId Payload U} {R₀ N : ℕ}
    (hT : T ⊆ (Correct : Finset Validator)) (hcard : quorumCard Validator ≤ T.card)
    (hs : SynchronisedOn U T R₀) (hpop : ∀ r, R₀ ≤ r → r ≤ N → PopulatedOn U T r)
    (hV : V.CoversUpto N)
    (hcrash : ∀ v, v ∉ T → v ∉ F.byzantine →
      ∀ L ∈ U.ids, R₀ ≤ (U.block L).round → (U.block L).creator ≠ v)
    {lead : Fin n → Validator} (hbij : Function.Bijective lead)
    (hsched : ∀ t, S.leader t = lead ⟨t % n, Nat.mod_lt t hn⟩) (hlt : ws * (n - T.card) < n)
    {x : ℕ → ℕ} (hR : R₀ ≤ x 0) (hstart : ¬ R.Decided U V (x 0) none)
    (hhop : ∀ i, i < F.byzantine.card → FloorHopOf R U V (x i) (x (i + 1)))
    (hN : ∀ j, j ≤ x F.byzantine.card → R.decisionRound j ≤ N) :
    ∃ i, i ≤ F.byzantine.card ∧ S.leader (x i) ∈ T := by
  classical
  have hws : 1 ≤ ws := by have := hwr 0; omega
  by_contra hcon
  have hno : ∀ i, i ≤ F.byzantine.card → S.leader (x i) ∉ T :=
    fun i hi hmem => hcon ⟨i, hi, hmem⟩
  have hstep : ∀ i, i < F.byzantine.card → x i + ws ≤ x (i + 1) := by
    intro i hi
    have := (hhop i hi).1
    have := hwr (x i)
    omega
  have hmono := chain_mono (x := x) (m := F.byzantine.card) fun i hi => by have := hstep i hi; omega
  have hunskipped := unskipped_of_hops hstart hhop
  have hbyz : ∀ i, i ≤ F.byzantine.card → S.leader (x i) ∈ F.byzantine := fun i hi =>
    byzantine_of_unskipped hsk hcard hpop hV hcrash
      (by rw [hid]; exact le_trans hR (hmono 0 i (by omega) hi))
      (hN (x i) (hmono i _ hi le_rfl)) (hunskipped i hi) (hno i hi)
  exact roundRobin_byzantine_hop_bound hn hws hT hbij hsched hlt hstep hbyz
    fun i hi t ht1 ht2 =>
      leader_not_mem_of_skip hl hcu hT hcard hs hpop hV
        (by rw [hid]; exact le_trans hR (le_trans (hmono 0 i (by omega) (by omega)) (by omega)))
        (hN t (le_trans (le_of_lt ht2) (hmono (i + 1) F.byzantine.card (by omega) le_rfl)))
        ((hhop i hi).2.1 t (by have := hwr (x i); omega) ht2)

/-- **The landing of a hop at a rule**: the least slot past `k`'s decision round that the view
does not skip, which is where the anchor search stops; the floor itself where no such slot
exists, a case the claims that read the chain never see, since they carry the landing's own
`¬ Decided`. -/
noncomputable def floorLandingOf (R : AnchoredRule Validator BlockId Payload ValidWrt Correct)
    (U : BlockUniverse Validator BlockId Payload) (V : View Validator BlockId Payload U)
    (k : ℕ) : ℕ :=
  open Classical in
  if h : ∃ y, k + R.waveAt (S.kind k) + 1 ≤ y ∧ ¬ R.Decided U V y none then Nat.find h
  else k + R.waveAt (S.kind k) + 1

/-- **The floor chain at a rule**: hop to the landing, and again from there. -/
noncomputable def floorChainOf (R : AnchoredRule Validator BlockId Payload ValidWrt Correct)
    (U : BlockUniverse Validator BlockId Payload) (V : View Validator BlockId Payload U)
    (k : ℕ) : ℕ → ℕ
  | 0 => k
  | i + 1 => floorLandingOf R U V (floorChainOf R U V k i)

omit [LinearOrder BlockId] in
/-- Where some slot past a slot's floor is not skipped, the landing is a hop of the chain, at or
below every such slot. -/
theorem floorHopOf_floorLandingOf {U : BlockUniverse Validator BlockId Payload}
    {V : View Validator BlockId Payload U} {y z : ℕ} (hz : y + R.waveAt (S.kind y) + 1 ≤ z)
    (hnz : ¬ R.Decided U V z none) :
    FloorHopOf R U V y (floorLandingOf R U V y) ∧ floorLandingOf R U V y ≤ z := by
  classical
  have h : ∃ z, y + R.waveAt (S.kind y) + 1 ≤ z ∧ ¬ R.Decided U V z none := ⟨z, hz, hnz⟩
  have hl : floorLandingOf R U V y = Nat.find h := by
    unfold floorLandingOf
    rw [dif_pos h]
  rw [hl]
  refine ⟨⟨(Nat.find_spec h).1, fun j hj1 hj2 => ?_, (Nat.find_spec h).2⟩,
    Nat.find_min' h ⟨hz, hnz⟩⟩
  by_contra hns
  exact Nat.find_min h hj2 ⟨hj1, hns⟩

/-- **SH6j.** At the round-robin schedule a reliably led round lies within `n − |T|` rounds above
any floor (SH6g); under synchrony it commits and so is not skipped, so the chain's landing lies at
or below it and each hop climbs by at most `ws + (n − |T|)` rounds. One of the first `b + 1`
landings is reliably led (SH6i), and its commit decides the chain's start (SH6f). -/
theorem floorChainDecidesWithinRounds {U : BlockUniverse Validator BlockId Payload}
    {ws n : ℕ} (hn : 0 < n) (hl : R.Laws) (hleast : LeastLinked R) (hcu : CommitsUnderSync R U)
    (hsk : SkipsSilent R U) (hwr : ∀ t, R.waveAt (S.kind t) + 1 = ws)
    (hid : ∀ t, S.slotRound t = t) {T : Finset Validator} {V : View Validator BlockId Payload U}
    {R₀ N : ℕ} (hT : T ⊆ (Correct : Finset Validator)) (hcard : quorumCard Validator ≤ T.card)
    (hs : SynchronisedOn U T R₀) (hpop : ∀ r, R₀ ≤ r → r ≤ N → PopulatedOn U T r)
    (hV : V.CoversUpto N)
    (hcrash : ∀ v, v ∉ T → v ∉ F.byzantine →
      ∀ L ∈ U.ids, R₀ ≤ (U.block L).round → (U.block L).creator ≠ v)
    {lead : Fin n → Validator} (hbij : Function.Bijective lead)
    (hsched : ∀ t, S.leader t = lead ⟨t % n, Nat.mod_lt t hn⟩) (hlt : ws * (n - T.card) < n)
    {k : ℕ} (hR : R₀ ≤ k) (hstart : ¬ R.Decided U V k none)
    (hN : k + (F.byzantine.card + 1) * (ws + (n - T.card)) ≤ N) :
    ∃ v, R.Decided U V k v := by
  classical
  -- the residues T leads, as many as T
  set T' : Finset (Fin n) := Finset.univ.filter fun r => lead r ∈ T with hT'
  have hT'card : T'.card = T.card := card_residues_of_bijective hbij T
  have hT'ne : T'.Nonempty := by
    obtain ⟨v, hv⟩ : T.Nonempty := by
      rw [← Finset.card_pos]
      have := F.card_validators
      omega
    obtain ⟨r, rfl⟩ := hbij.2 v
    exact ⟨r, by rw [hT', Finset.mem_filter]; exact ⟨Finset.mem_univ _, hv⟩⟩
  set m := n - T.card with hm
  set b := F.byzantine.card with hb
  -- a hop from a slot lands within ws + (n − |T|) rounds of it, once the view holds that far
  have hop : ∀ y, R₀ ≤ y → y + ws + m + ws ≤ N →
      FloorHopOf R U V y (floorLandingOf R U V y) ∧ floorLandingOf R U V y ≤ y + ws + m := by
    intro y hy hyN
    obtain ⟨a, ha1, ha2, haT'⟩ := roundRobin_near hn hT'ne (y + ws)
    rw [hT'card] at ha2
    have haT : S.leader a ∈ T := by
      rw [hsched]
      rw [hT', Finset.mem_filter] at haT'
      exact haT'.2
    have hna : ¬ R.Decided U V a none := fun hskip =>
      leader_not_mem_of_skip hl hcu hT hcard hs hpop hV (by rw [hid]; omega)
        (by unfold AnchoredRule.decisionRound; rw [hid]; have := hwr a; omega) hskip haT
    obtain ⟨hhop, hle⟩ := floorHopOf_floorLandingOf (V := V) (y := y) (z := a)
      (by have := hwr y; omega) hna
    exact ⟨hhop, by omega⟩
  -- the chain of floors climbs by at most that a hop, and stays past R₀
  set x := floorChainOf R U V k with hx
  have hx0 : x 0 = k := rfl
  have hxs : ∀ i, x (i + 1) = floorLandingOf R U V (x i) := fun i => rfl
  have hbound : ∀ i, i ≤ b → R₀ ≤ x i ∧ x i ≤ k + i * (ws + m) := by
    intro i
    induction i with
    | zero => intro _; rw [hx0]; exact ⟨hR, by omega⟩
    | succ i ih =>
      intro hi
      obtain ⟨hRi, hxi⟩ := ih (by omega)
      have h1 : (i + 1) * (ws + m) ≤ b * (ws + m) := Nat.mul_le_mul_right _ hi
      have h2 : (i + 1) * (ws + m) = i * (ws + m) + (ws + m) := by rw [Nat.add_mul, Nat.one_mul]
      have h3 : (b + 1) * (ws + m) = b * (ws + m) + (ws + m) := by rw [Nat.add_mul, Nat.one_mul]
      obtain ⟨hhop, hle⟩ := hop (x i) hRi (by omega)
      rw [← hxs] at hhop hle
      refine ⟨le_trans hRi (by have := hhop.1; omega), by omega⟩
  have hhop : ∀ i, i < b → FloorHopOf R U V (x i) (x (i + 1)) := by
    intro i hi
    obtain ⟨hRi, hxi⟩ := hbound i (le_of_lt hi)
    have h1 : (i + 1) * (ws + m) ≤ b * (ws + m) := Nat.mul_le_mul_right _ hi
    have h2 : (i + 1) * (ws + m) = i * (ws + m) + (ws + m) := by rw [Nat.add_mul, Nat.one_mul]
    have h3 : (b + 1) * (ws + m) = b * (ws + m) + (ws + m) := by rw [Nat.add_mul, Nat.one_mul]
    have := (hop (x i) hRi (by omega)).1
    rwa [← hxs] at this
  have hdec : ∀ i, i ≤ b → ∀ j, j ≤ x i → R.decisionRound j ≤ N := by
    intro i hi j hj
    have := (hbound i hi).2
    have h1 : i * (ws + m) ≤ b * (ws + m) := Nat.mul_le_mul_right _ hi
    have h3 : (b + 1) * (ws + m) = b * (ws + m) + (ws + m) := by rw [Nat.add_mul, Nat.one_mul]
    unfold AnchoredRule.decisionRound
    rw [hid]
    have := hwr j
    omega
  -- one of the first b + 1 landings is reliably led, and its commit decides the start
  obtain ⟨i, hi, hlead⟩ := floorChainReachesReliableWithinByzantine hn hl hcu hsk hwr hid hT
    hcard hs hpop hV hcrash hbij hsched hlt (x := x) (by rw [hx0]; exact hR)
    (by rw [hx0]; exact hstart) hhop (hdec b le_rfl)
  have := floorChainDecides hleast hcu hid hT hcard hs hpop hV i x (by rw [hx0]; exact hR)
    (fun i' hi' => hhop i' (by omega)) hlead (hdec i hi (x i) le_rfl)
  rwa [hx0] at this

/-! ## SH6o, SH6p — the chain at a period

At the paper's dial a landing may be a slot no schedule names, so two things change. The descent
takes a commit in place of a reliable leader (SH6m), which lets the chain stop wherever the coin
decided something; and the count that bounds the chain loses the coin's rounds (SH6o), since a
round the coin leads is led by nobody the round robin knows. -/

omit [Fintype Validator] [DecidableEq Validator] F in
/-- A periodic schedule's asynchronous rounds: a slot whose round is not a multiple of the period
is synchronous. -/
theorem kind_eq_zero_of_mod_ne {p : ℕ} (hkind : ∀ t, S.kind t = periodicKind p t) {t : ℕ}
    (h : t % p ≠ 0) : S.kind t = 0 := by
  rw [hkind]
  unfold periodicKind
  rw [if_neg h]

omit [LinearOrder BlockId] in
/-- **SH6o.** A landing of an asynchronous slot is decided by hypothesis and unskipped by its
hop, so it is committed and the second disjunct holds; otherwise every landing is synchronous and
led by the round robin, the skips between landings are exempt or not reliably led, and
`roundRobin_hop_bound_exempt` contradicts the count. -/
theorem floorChainReachesAtPeriod {U : BlockUniverse Validator BlockId Payload}
    {ws p n : ℕ} (hn : 0 < n) (hp : 0 < p) (hl : R.Laws) (hcu : CommitsUnderSync R U)
    (hw0 : R.waveAt 0 + 1 = ws) (hid : ∀ t, S.slotRound t = t)
    (hkind : ∀ t, S.kind t = periodicKind p t) {lead : Fin n → Validator}
    (hsched : ∀ t, S.kind t = 0 → S.leader t = lead ⟨t % n, Nat.mod_lt t hn⟩)
    {T : Finset Validator} {V : View Validator BlockId Payload U} {R₀ N : ℕ}
    (hT : T ⊆ (Correct : Finset Validator)) (hcard : quorumCard Validator ≤ T.card)
    (hs : SynchronisedOn U T R₀) (hpop : ∀ r, R₀ ≤ r → r ≤ N → PopulatedOn U T r)
    (hV : V.CoversUpto N) (hbij : Function.Bijective lead)
    (hlt : ws * (n - T.card) + ws * ((n + p - 1) / p) < n) {x : ℕ → ℕ}
    (hasync : ∀ t, x 0 ≤ t → S.kind t = 1 → ∃ v, R.Decided U V t v)
    (hR : R₀ ≤ x 0) (hstart : ¬ R.Decided U V (x 0) none)
    (hhop : ∀ i, i < n - T.card → FloorHopOf R U V (x i) (x (i + 1)))
    (hN : ∀ j, j ≤ x (n - T.card) → R.decisionRound j ≤ N) :
    ∃ i, i ≤ n - T.card ∧ (S.leader (x i) ∈ T ∨ ∃ A, R.Decided U V (x i) (some A)) := by
  classical
  set m := n - T.card with hm
  by_contra hcon
  have hno : ∀ i, i ≤ m → S.leader (x i) ∉ T ∧ ¬ ∃ A, R.Decided U V (x i) (some A) := by
    intro i hi
    exact ⟨fun hmem => hcon ⟨i, hi, Or.inl hmem⟩, fun hex => hcon ⟨i, hi, Or.inr hex⟩⟩
  -- the chain climbs, so every landing lies at or above its start
  have hmono := chain_mono (x := x) (m := m) fun i hi => by have := (hhop i hi).1; omega
  have hunskipped := unskipped_of_hops hstart hhop
  -- so every landing is synchronous: an asynchronous one is decided, hence committed
  have hsync : ∀ i, i ≤ m → S.kind (x i) = 0 := by
    intro i hi
    by_contra hk
    have hk1 : S.kind (x i) = 1 := by
      rw [hkind] at hk ⊢
      by_contra hk1
      exact hk (periodicKind_eq_zero_of_ne_one hk1)
    obtain ⟨v, hv⟩ := hasync (x i) (hmono 0 i (by omega) hi) hk1
    cases v with
    | none => exact hunskipped i hi hv
    | some A => exact (hno i hi).2 ⟨A, hv⟩
  -- the chain advances by the synchronous wave a hop
  have hstep : ∀ i, i < m → x i + ws ≤ x (i + 1) := by
    intro i hi
    have h := (hhop i hi).1
    rw [hsync i (by omega)] at h
    omega
  -- the landings are led from outside T by the round robin
  have hbad : ∀ i, i ≤ m → lead ⟨x i % n, Nat.mod_lt _ hn⟩ ∉ T := by
    intro i hi
    have := (hno i hi).1
    rwa [hsched (x i) (hsync i hi)] at this
  -- and the skips between them carry a coin or are led from outside T
  have hmid : ∀ i, i < m → ∀ t, x i + ws ≤ t → t < x (i + 1) →
      t % p = 0 ∨ lead ⟨t % n, Nat.mod_lt _ hn⟩ ∉ T := by
    intro i hi t ht1 ht2
    by_cases hasyncr : t % p = 0
    · exact Or.inl hasyncr
    refine Or.inr fun hmem => ?_
    have hk0 : S.kind t = 0 := kind_eq_zero_of_mod_ne hkind hasyncr
    have hleadT : S.leader t ∈ T := by rwa [hsched t hk0]
    have hskip : R.Decided U V t none :=
      (hhop i hi).2.1 t (by rw [hsync i (by omega)]; omega) ht2
    exact leader_not_mem_of_skip hl hcu hT hcard hs hpop hV
      (by rw [hid]; have := hmono 0 i (by omega) (by omega); omega)
      (hN t (le_trans (le_of_lt ht2) (hmono (i + 1) m (by omega) le_rfl))) hskip hleadT
  exact roundRobin_hop_bound_exempt (c := (n + p - 1) / p) hn (by omega) hbij
    (sched := fun t => lead ⟨t % n, Nat.mod_lt t hn⟩) (fun _ => rfl)
    (Ex := fun t => t % p = 0) (fun a q => card_multiples_le hp a q) hm hlt hstep hbad hmid

omit [LinearOrder BlockId] in
/-- **SH6o at the Byzantine count**, the step SH6p takes: with every landing already known
synchronous, a landing led by a crashed validator would be directly skipped (`SkipsSilent`), so a
landing led from outside `T` is Byzantine-led, and `roundRobin_byzantine_hop_bound_exempt` bounds
the chain by the Byzantine validators with the coin's rounds exempt. -/
theorem floorChainReachesAtPeriodWithinByzantine {U : BlockUniverse Validator BlockId Payload}
    {ws p n : ℕ} (hn : 0 < n) (hp : 0 < p) (hl : R.Laws) (hcu : CommitsUnderSync R U)
    (hsk : SkipsSilent R U) (hw0 : R.waveAt 0 + 1 = ws) (hid : ∀ t, S.slotRound t = t)
    (hkind : ∀ t, S.kind t = periodicKind p t) {lead : Fin n → Validator}
    (hsched : ∀ t, S.kind t = 0 → S.leader t = lead ⟨t % n, Nat.mod_lt t hn⟩)
    {T : Finset Validator} {V : View Validator BlockId Payload U} {R₀ N : ℕ}
    (hT : T ⊆ (Correct : Finset Validator)) (hcard : quorumCard Validator ≤ T.card)
    (hs : SynchronisedOn U T R₀) (hpop : ∀ r, R₀ ≤ r → r ≤ N → PopulatedOn U T r)
    (hV : V.CoversUpto N)
    (hcrash : ∀ v, v ∉ T → v ∉ F.byzantine →
      ∀ L ∈ U.ids, R₀ ≤ (U.block L).round → (U.block L).creator ≠ v)
    (hbij : Function.Bijective lead)
    (hlt : ws * (n - T.card) + ws * ((n + p - 1) / p) < n) {x : ℕ → ℕ}
    (hR : R₀ ≤ x 0) (hstart : ¬ R.Decided U V (x 0) none)
    (hsyncs : ∀ i, i ≤ F.byzantine.card → S.kind (x i) = 0)
    (hhop : ∀ i, i < F.byzantine.card → FloorHopOf R U V (x i) (x (i + 1)))
    (hN : ∀ j, j ≤ x F.byzantine.card → R.decisionRound j ≤ N) :
    ∃ i, i ≤ F.byzantine.card ∧ S.leader (x i) ∈ T := by
  classical
  by_contra hcon
  have hno : ∀ i, i ≤ F.byzantine.card → S.leader (x i) ∉ T :=
    fun i hi hmem => hcon ⟨i, hi, hmem⟩
  have hstep : ∀ i, i < F.byzantine.card → x i + ws ≤ x (i + 1) := by
    intro i hi
    have h := (hhop i hi).1
    rw [hsyncs i (by omega)] at h
    omega
  have hmono := chain_mono (x := x) (m := F.byzantine.card) fun i hi => by have := hstep i hi; omega
  have hunskipped := unskipped_of_hops hstart hhop
  -- no landing is led by a crashed validator: its slot would be directly skipped
  have hbyz : ∀ i, i ≤ F.byzantine.card → S.leader (x i) ∈ F.byzantine := fun i hi =>
    byzantine_of_unskipped hsk hcard hpop hV hcrash
      (by rw [hid]; exact le_trans hR (hmono 0 i (by omega) hi))
      (hN (x i) (hmono i _ hi le_rfl)) (hunskipped i hi) (hno i hi)
  -- and the skips between landings carry a coin or are led from outside T
  have hmid : ∀ i, i < F.byzantine.card → ∀ t, x i + ws ≤ t → t < x (i + 1) →
      t % p = 0 ∨ lead ⟨t % n, Nat.mod_lt _ hn⟩ ∉ T := by
    intro i hi t ht1 ht2
    by_cases hasyncr : t % p = 0
    · exact Or.inl hasyncr
    refine Or.inr fun hmem => ?_
    have hk0 : S.kind t = 0 := kind_eq_zero_of_mod_ne hkind hasyncr
    have hleadT : S.leader t ∈ T := by rwa [hsched t hk0]
    have hskip : R.Decided U V t none :=
      (hhop i hi).2.1 t (by rw [hsyncs i (by omega)]; omega) ht2
    exact leader_not_mem_of_skip hl hcu hT hcard hs hpop hV
      (by rw [hid]; have := hmono 0 i (by omega) (by omega); omega)
      (hN t (le_trans (le_of_lt ht2) (hmono (i + 1) F.byzantine.card (by omega) le_rfl)))
      hskip hleadT
  exact roundRobin_byzantine_hop_bound_exempt (c := (n + p - 1) / p) hn (by omega) hT hbij
    (sched := fun t => lead ⟨t % n, Nat.mod_lt t hn⟩) (fun _ => rfl)
    (Ex := fun t => t % p = 0) (fun a q => card_multiples_le hp a q) hlt hstep
    (fun i hi => by rw [← hsched (x i) (hsyncs i hi)]; exact hbyz i hi) hmid

/-- **SH6p.** At the periodic round robin a reliably led synchronous round lies within `W` rounds
above any floor; under synchrony it commits and so is not skipped, so the chain's landing lies at
or below it and each hop from a synchronous slot climbs by at most `ws + W` rounds. The chain
stops at the first asynchronous landing, which is decided by hypothesis and unskipped by its hop,
hence committed, and SH6m descends from it; otherwise every landing is synchronous, one of the
first `b + 1` is reliably led, and SH6f descends from its commit. -/
theorem floorChainDecidesWithinRoundsAtPeriod {U : BlockUniverse Validator BlockId Payload}
    {ws wa p n W : ℕ} (hn : 0 < n) (hp : 0 < p) (hl : R.Laws) (hleast : LeastLinked R)
    (hcu : CommitsUnderSync R U) (hsk : SkipsSilent R U) (hw0 : R.waveAt 0 + 1 = ws)
    (hw1 : R.waveAt 1 + 1 = wa) (hid : ∀ t, S.slotRound t = t)
    (hkind : ∀ t, S.kind t = periodicKind p t) {lead : Fin n → Validator}
    (hsched : ∀ t, S.kind t = 0 → S.leader t = lead ⟨t % n, Nat.mod_lt t hn⟩)
    {T : Finset Validator} {V : View Validator BlockId Payload U} {R₀ N : ℕ}
    (hT : T ⊆ (Correct : Finset Validator)) (hcard : quorumCard Validator ≤ T.card)
    (hs : SynchronisedOn U T R₀) (hpop : ∀ r, R₀ ≤ r → r ≤ N → PopulatedOn U T r)
    (hV : V.CoversUpto N)
    (hcrash : ∀ v, v ∉ T → v ∉ F.byzantine →
      ∀ L ∈ U.ids, R₀ ≤ (U.block L).round → (U.block L).creator ≠ v)
    (hbij : Function.Bijective lead)
    (hlt : ws * (n - T.card) + ws * ((n + p - 1) / p) < n)
    (hwait : ∀ r, ∃ a, r ≤ a ∧ a ≤ r + W ∧ S.kind a = 0 ∧ S.leader a ∈ T) {k : ℕ}
    (hasync : ∀ t, k ≤ t → S.kind t = 1 → ∃ v, R.Decided U V t v)
    (hR : R₀ ≤ k) (hstart : ¬ R.Decided U V k none)
    (hN : k + (F.byzantine.card + 1) * (ws + W) + wa ≤ N) :
    ∃ v, R.Decided U V k v := by
  classical
  have hwk : ∀ t, R.waveAt (S.kind t) + 1 ≤ ws + wa := by
    intro t
    rw [hkind]
    unfold periodicKind
    split <;> omega
  set b := F.byzantine.card with hb
  -- every decision round below the budget lies under the horizon
  have hdecN : ∀ j, j ≤ k + b * (ws + W) → R.decisionRound j ≤ N := by
    intro j hj
    have h1 : (b + 1) * (ws + W) = b * (ws + W) + (ws + W) := by rw [Nat.add_mul, Nat.one_mul]
    have h3 := hwk j
    unfold AnchoredRule.decisionRound
    rw [hid]
    omega
  -- a hop from a synchronous slot lands within ws + W rounds of it
  have hop : ∀ y, R₀ ≤ y → S.kind y = 0 → y + ws + W ≤ k + b * (ws + W) →
      FloorHopOf R U V y (floorLandingOf R U V y) ∧ floorLandingOf R U V y ≤ y + ws + W := by
    intro y hy hky hyN
    obtain ⟨a, ha1, ha2, hka, haT⟩ := hwait (y + ws)
    have hna : ¬ R.Decided U V a none := fun hskip =>
      leader_not_mem_of_skip hl hcu hT hcard hs hpop hV (by rw [hid]; omega)
        (hdecN a (by omega)) hskip haT
    obtain ⟨hhop, hle⟩ := floorHopOf_floorLandingOf (V := V) (y := y) (z := a)
      (by rw [hky]; omega) hna
    exact ⟨hhop, by omega⟩
  -- the chain of floors, bounded while its landings stay synchronous
  set x := floorChainOf R U V k with hx
  have hx0 : x 0 = k := rfl
  have hxs : ∀ i, x (i + 1) = floorLandingOf R U V (x i) := fun i => rfl
  have hmain : ∀ i, i ≤ b → (∃ v, R.Decided U V k v) ∨
      (R₀ ≤ x i ∧ k ≤ x i ∧ (∀ j, j ≤ i → x j ≤ k + j * (ws + W)) ∧
        (∀ j, j ≤ i → S.kind (x j) = 0) ∧
        ∀ j, j < i → FloorHopOf R U V (x j) (x (j + 1))) := by
    intro i
    induction i with
    | zero =>
      intro _
      by_cases hk1 : S.kind k = 1
      · exact Or.inl (hasync k le_rfl hk1)
      · refine Or.inr ⟨by rw [hx0]; exact hR, by rw [hx0], fun j hj => ?_, fun j hj => ?_,
          fun j hj => ?_⟩
        · rw [show j = 0 by omega, hx0]; omega
        · rw [show j = 0 by omega, hx0]
          rw [hkind] at hk1 ⊢
          exact periodicKind_eq_zero_of_ne_one hk1
        · omega
    | succ i ih =>
      intro hi
      rcases ih (by omega) with hdone | ⟨hRi, hki, hxj, hkinds, hhops⟩
      · exact Or.inl hdone
      have hxi := hxj i le_rfl
      have h1 : (i + 1) * (ws + W) ≤ b * (ws + W) := Nat.mul_le_mul_right _ hi
      have h2 : (i + 1) * (ws + W) = i * (ws + W) + (ws + W) := by rw [Nat.add_mul, Nat.one_mul]
      obtain ⟨hhop, hle⟩ := hop (x i) hRi (hkinds i le_rfl) (by omega)
      rw [← hxs] at hhop hle
      have hlow : x i ≤ x (i + 1) := by have := hhop.1; omega
      by_cases hk1 : S.kind (x (i + 1)) = 1
      · -- an asynchronous landing is decided and unskipped, hence committed
        obtain ⟨v, hv⟩ := hasync (x (i + 1)) (le_trans hki hlow) hk1
        obtain ⟨A, rfl⟩ : ∃ A, v = some A := by
          cases v with
          | none => exact absurd hv hhop.2.2
          | some A => exact ⟨A, rfl⟩
        refine Or.inl ?_
        have := floorChainDecidesFromCommit hleast hid (i + 1) x
          (fun j hj => by
            rcases Nat.lt_or_ge j i with h | h
            · exact hhops j h
            · rw [show j = i by omega]; exact hhop) ⟨A, hv⟩
        rwa [hx0] at this
      · refine Or.inr ⟨le_trans hRi hlow, le_trans hki hlow, fun j hj => ?_, fun j hj => ?_,
          fun j hj => ?_⟩
        · rcases Nat.lt_or_ge j (i + 1) with h | h
          · exact hxj j (by omega)
          · rw [show j = i + 1 by omega]; omega
        · rcases Nat.lt_or_ge j (i + 1) with h | h
          · exact hkinds j (by omega)
          · rw [show j = i + 1 by omega]
            rw [hkind] at hk1 ⊢
            exact periodicKind_eq_zero_of_ne_one hk1
        · rcases Nat.lt_or_ge j i with h | h
          · exact hhops j h
          · rw [show j = i by omega]; exact hhop
  rcases hmain b le_rfl with hdone | ⟨hRb, hkb, hxj, hkinds, hhops⟩
  · exact hdone
  -- every landing is synchronous, so one of the first b + 1 is reliably led
  have hbudget : ∀ j, j ≤ b → x j ≤ k + b * (ws + W) := by
    intro j hj
    have h1 : j * (ws + W) ≤ b * (ws + W) := Nat.mul_le_mul_right _ hj
    have := hxj j hj
    omega
  obtain ⟨i, hi, hlead⟩ := floorChainReachesAtPeriodWithinByzantine hn hp hl hcu hsk hw0 hid
    hkind hsched hT hcard hs hpop hV hcrash hbij hlt (x := x) (by rw [hx0]; exact hR)
    (by rw [hx0]; exact hstart) hkinds hhops
    (fun j hj => hdecN j (le_trans hj (hbudget b le_rfl)))
  have := floorChainDecides hleast hcu hid hT hcard hs hpop hV i x (by rw [hx0]; exact hR)
    (fun i' hi' => hhops i' (by omega)) hlead (hdecN (x i) (hbudget i hi))
  rwa [hx0] at this

/-! ## SH6l — the timed discipline -/

omit [LinearOrder BlockId] in
/-- **SH6l.** A `ViewPace` whose timeout clears the delay at a rate synchronises the reliable set
from `max (2Δ + proc, gst)` (`synchronisedOn_of_rate`), and the clause commits from there. -/
theorem commitsOfViewPace {U : BlockUniverse Validator BlockId Payload}
    (hcu : CommitsUnderSync R U) {T : Finset Validator} {V : View Validator BlockId Payload U}
    {N N' k : ℕ} (vp : ViewPace U T N) (hT : T ⊆ (Correct : Finset Validator))
    (hcard : quorumCard Validator ≤ T.card) (hrate : Rated vp.timeout)
    (hR : max (2 * vp.delay + vp.proc) vp.gst ≤ S.slotRound k)
    (hpop : ∀ r, max (2 * vp.delay + vp.proc) vp.gst ≤ r → r ≤ N' → PopulatedOn U T r)
    (hN : R.decisionRound k ≤ N') (hV : V.CoversUpto N') (hlead : S.leader k ∈ T) :
    ∃ L, IsLeaderBlock U k L ∧ R.Decided U V k (some L) := by
  obtain ⟨L, hL, hc⟩ :=
    hcu T V _ N' k hT hcard (vp.synchronisedOn_of_rate hcard hrate) hpop hR hN hV hlead
  exact ⟨L, hL, AnchoredRule.Decided.directCommit hL hc⟩

/-! ## SH9a, SH9c — the drain and the cost of an asynchronous slot -/

omit [LinearOrder BlockId] in
/-- At one slot per round, `wa` consecutive slots span once no slot's wave exceeds `wa`. -/
theorem spansEligible_of_le {wa : ℕ} (hw : ∀ s, R.waveAt (S.kind s) + 1 ≤ wa)
    (hid : ∀ s, S.slotRound s = s) : R.SpansEligible wa := by
  intro b i hi
  have := hw i
  rw [R.eligible_iff, hid, hid]
  omega

/-- **SH9a.** The relation's descent below a committed run, at each slot's own wave. -/
theorem allDecidedBelowOfRun {U : BlockUniverse Validator BlockId Payload} {wa : ℕ}
    (hleast : LeastLinked R) (hw : ∀ s, R.waveAt (S.kind s) + 1 ≤ wa)
    (hid : ∀ s, S.slotRound s = s) {V : View Validator BlockId Payload U} {b : ℕ}
    (hrun : ∀ i, i < wa → ∃ L, R.Decided U V (b + i) (some L)) :
    ∀ i, i < b → ∃ v, R.Decided U V i v := by
  have hwa : 1 ≤ wa := by have := hw 0; omega
  exact AnchoredRule.decided_below_of_run (fun hi h => hleast hi h) hwa (spansEligible_of_le hw hid)
    (Led := fun j => ∃ L, R.Decided U V j (some L)) hrun fun j _ _ hj => hj

omit [LinearOrder BlockId] in
/-- **SH9c.** Decision rounds at the periodic kinds: `r + wa − 1` at an asynchronous slot,
`r + ws − 1` at a synchronous one; the rest is arithmetic. -/
theorem asyncSlotCost {ws wa k : ℕ} (hid : ∀ s, S.slotRound s = s)
    (hkind : ∀ s, S.kind s = periodicKind k s) (hw0 : R.waveAt 0 + 1 = ws)
    (hw1 : R.waveAt 1 + 1 = wa) (hwa : ws ≤ wa) {r : ℕ} (hr : S.kind r = 1) :
    R.decisionRound r = r + (ws - 1) + (wa - ws) ∧
    ∀ i, 1 ≤ i → i < k → R.decisionRound r ≤ R.decisionRound (r + i) + (wa - ws - i) := by
  refine ⟨?_, fun i hi hik => ?_⟩
  · unfold AnchoredRule.decisionRound
    rw [hid, hr]
    omega
  · have hasync : IsAsync k r := periodicKind_eq_one_iff.mp (hkind r ▸ hr)
    have hsync : S.kind (r + i) = 0 := by
      refine kind_eq_zero_of_mod_ne hkind ?_
      unfold IsAsync at hasync
      rw [Nat.add_mod, hasync, zero_add, Nat.mod_mod, Nat.mod_eq_of_lt hik]
      omega
    unfold AnchoredRule.decisionRound
    rw [hid, hid, hr, hsync]
    omega

end Slots


/-! ## SH7 — the chain

Stated at any schedule whose rounds strictly increase: the coin schedule and every control
schedule. Consecutive slots of such a schedule lie at least one round apart, so `wa` of them span
the wave, which is all the descent asks. -/

section Chain

variable {R : AnchoredRule Validator BlockId Payload ValidWrt Correct}
  {good : BlockUniverse Validator BlockId Payload → ℕ → Finset Validator}

omit [Fintype Validator] [DecidableEq Validator] F [LinearOrder BlockId] in
/-- A strictly increasing schedule puts slot `m` at least `m − i` rounds above slot `i`. -/
theorem slotRound_add_le_of_strictMono {S' : Slots Validator} (hmono : StrictMono S'.slotRound)
    {i m : ℕ} (h : i ≤ m) : S'.slotRound i + (m - i) ≤ S'.slotRound m := by
  have := hmono.add_le_nat (m - i) i
  rw [Nat.sub_add_cancel h] at this
  omega

omit [LinearOrder BlockId] in
/-- At a strictly increasing schedule a run of `wa` slots spans, once no slot's wave reaches
`wa`. -/
theorem spansEligible_of_strictMono {wa : ℕ} {S' : Slots Validator}
    (hw : ∀ i, R.waveAt (S'.kind i) + 1 ≤ wa) (hmono : StrictMono S'.slotRound) :
    R.SpansEligible (S := S') wa := by
  intro b i hi
  rw [AnchoredRule.eligible_iff]
  have := hw i
  have := slotRound_add_le_of_strictMono hmono (show i ≤ b + wa - 1 by omega)
  omega

/-- **SH7c, at any strictly increasing schedule.** The relation's descent below a run of good
slots: each commits directly by `GoodCommits`, in a view holding the run's decision rounds. -/
theorem decidedBelowOfGoodRun (hleast : LeastLinked R) (hgc : GoodCommits R good) {wa : ℕ}
    {S' : Slots Validator} (hw : ∀ i, R.waveAt (S'.kind i) + 1 ≤ wa)
    (hmono : StrictMono S'.slotRound) {U : BlockUniverse Validator BlockId Payload}
    {V : View Validator BlockId Payload U} {b : ℕ}
    (hgood : ∀ i, i < wa → S'.leader (b + i) ∈ good U (S'.slotRound (b + i)))
    (hV : V.CoversUpto (S'.slotRound (b + wa - 1) + (wa - 1))) :
    ∀ i, i < b → ∃ v, R.Decided (S := S') U V i v := by
  have hwa : 0 < wa := by have := hw 0; omega
  refine AnchoredRule.decided_below_of_run (S := S') (fun hi h => hleast hi h) hwa
    (spansEligible_of_strictMono hw hmono)
    (Led := fun j => S'.leader j ∈ good U (S'.slotRound j)) hgood fun j _ hj2 hj => ?_
  obtain ⟨L, hL, hLr, hLc, hc⟩ := hgc U _ _ hj
  refine ⟨L, AnchoredRule.Decided.directCommit (S := S') ⟨hL, hLr, hLc⟩ (hc _ V (hV.mono ?_))⟩
  have := S'.mono hj2
  have := hw j
  omega

/-- **SH7c.** The descent at the coin schedule, the run named by rounds. -/
theorem chainAllDecidedBelowOfRun (hleast : LeastLinked R) (hgc : GoodCommits R good) {wa : ℕ}
    (hw : ∀ κ, R.waveAt κ + 1 ≤ wa) {coin : ℕ → Validator}
    {U : BlockUniverse Validator BlockId Payload} {V : View Validator BlockId Payload U} {b : ℕ}
    (hgood : ∀ i, i < wa → coin (b + i) ∈ good U (b + i))
    (hV : V.CoversUpto (b + wa - 1 + (wa - 1))) :
    ∀ i, i < b → ∃ v, ChainDecided R coin U V i v :=
  decidedBelowOfGoodRun (S' := chainSlots coin) hleast hgc (fun _ => hw _) strictMono_id hgood hV

/-- **SH7a.** The clause names a run past `k` within the window, and SH7c settles everything
below it. -/
theorem chainAllDecidedBelow (hleast : LeastLinked R) (hgc : GoodCommits R good) {wa : ℕ}
    {S' : Slots Validator} (hw : ∀ i, R.waveAt (S'.kind i) + 1 ≤ wa)
    (hmono : StrictMono S'.slotRound) {U : BlockUniverse Validator BlockId Payload}
    {V : View Validator BlockId Payload U} {c N : ℕ} (hrun : RunWithin (S := S') R good U c wa N)
    (hV : V.CoversUpto N) (k : ℕ) (hk : S'.slotRound (k + c + wa - 1) + (wa - 1) ≤ N) :
    ∃ b, k ≤ b ∧ ∀ i, i < b → ∃ v, R.Decided (S := S') U V i v := by
  obtain ⟨k', hk1, hk2, hgood⟩ := hrun k (by
    unfold AnchoredRule.decisionRound
    have := hw (k + c + wa - 1)
    omega)
  refine ⟨k', hk1, decidedBelowOfGoodRun hleast hgc hw hmono hgood (hV.mono ?_)⟩
  have := S'.mono (show k' + wa - 1 ≤ k + c + wa - 1 by omega)
  omega

/-- **SH7b.** SH6b at the schedule, whose strictly increasing rounds span the run. -/
theorem chainAllDecidedBelowOfSynchrony (hleast : LeastLinked R) {S' : Slots Validator}
    (hcu : ∀ U, CommitsUnderSync (S := S') R U) {wa : ℕ} (hw : ∀ i, R.waveAt (S'.kind i) + 1 ≤ wa)
    {T : Finset Validator} (hT : T ⊆ (Correct : Finset Validator))
    (hcard : quorumCard Validator ≤ T.card) (hmono : StrictMono S'.slotRound)
    (fair : FairRunOn (S := S') T wa) (R₀ k : ℕ) :
    ∃ b, k ≤ b ∧ R₀ ≤ S'.slotRound b ∧
      ∀ (U : BlockUniverse Validator BlockId Payload) (V : View Validator BlockId Payload U)
        (N : ℕ),
        SynchronisedOn U T R₀ → (∀ r, R₀ ≤ r → r ≤ N → PopulatedOn U T r) →
        V.CoversUpto N → S'.slotRound (b + wa - 1) + (wa - 1) ≤ N →
        ∀ i, i < b → ∃ v, R.Decided (S := S') U V i v := by
  obtain ⟨b, hb, hRb, h⟩ := allDecidedBelowOfSynchrony (S := S') hleast hcu hT hcard
    (spansEligible_of_strictMono hw hmono) fair R₀ k
  refine ⟨b, hb, hRb, fun U V N hs hpop hV hN => h U V N hs hpop hV fun j hj => ?_⟩
  unfold AnchoredRule.decisionRound
  have := S'.mono (show j ≤ b + wa - 1 by omega)
  have := hw j
  omega

end Chain

/-! ## SH8, SH9b — the stall and period one -/

/-- The rules of a pair agree on the rung count. -/
theorem RulePair.rules_rungs (p : RulePair Validator BlockId Payload) (κ : ℕ) :
    (p.rules κ).rungs = (p.rules 0).rungs := by
  unfold RulePair.rules
  split
  · rfl
  · exact p.rungs_eq

/-- The rules of a pair agree on the tie-break. -/
theorem RulePair.rules_tie (p : RulePair Validator BlockId Payload) (κ : ℕ) :
    (p.rules κ).tie = (p.rules 0).tie := by
  unfold RulePair.rules
  split
  · rfl
  · exact p.tie_eq

/-- The rules of a pair agree on the anchor. -/
theorem RulePair.rules_anchor (p : RulePair Validator BlockId Payload) (κ : ℕ) :
    (p.rules κ).Anchor = (p.rules 0).Anchor := by
  unfold RulePair.rules
  split
  · rfl
  · exact p.anchor_eq

section Pair

variable [S : Slots Validator] {U : BlockUniverse Validator BlockId Payload}
  {V : View Validator BlockId Payload U} {p : RulePair Validator BlockId Payload}

omit [Fintype Validator] [DecidableEq Validator] F [LinearOrder BlockId] S in
/-- An asynchronous round above `i + 1`, where `i ≡ k − 1`, lies a full period above `i`: the
arithmetic `omega` cannot do at a variable modulus. -/
theorem add_period_le_of_isAsync {k i j : ℕ} (hk : 2 ≤ k) (hi : i % k = k - 1)
    (hj : IsAsync k j) (hij : i + 2 ≤ j) : i + k + 1 ≤ j := by
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

/-- **SH8, at the slots a view can decide.** Induction on the derivation: a class-`(k − 1)` slot
is synchronous, so its direct verdicts are excluded outright and a synchronous anchor never commits
it, since it is neither committed nor linked; an asynchronous anchor leaves the class-`(k − 1)`
slot one period up as an eligible slot between, which must be skipped, which is the claim one
period up. The hypotheses are asked at the slots `Q` names, which every slot a derivation in `V`
mentions satisfies. -/
theorem stall_of_pred {ws k : ℕ} (hw0 : p.sync.waveAt 0 + 1 = ws) (hws : 2 ≤ ws) (hk : ws ≤ k)
    (hid : ∀ s, S.slotRound s = s) {Q : ℕ → Prop} (hkind : ∀ s, Q s → S.kind s = periodicKind k s)
    (hQ : ∀ (j : ℕ) (v : Option BlockId), (steelheadAt p).Decided U V j v → Q j)
    (hcl : ∀ (j : ℕ) (L : BlockId), Q j → S.kind j = 0 → IsLeaderBlock U j L →
      (∀ V' : View Validator BlockId Payload U, ¬ p.sync.Commit U V' L j 0) ∧
        ∀ (i : ℕ) (A : BlockId), ¬ p.sync.Link i U A L S j)
    (hskip : ∀ j, Q j → S.kind j = 0 → ¬ p.sync.Skip U V S j) {i : ℕ} (hi : i % k = k - 1)
    {v : Option BlockId} (h : (steelheadAt p).Decided U V i v) : False := by
  have hk2 : 2 ≤ k := le_trans hws hk
  have hsync_of_mod : ∀ {i : ℕ}, Q i → i % k = k - 1 → S.kind i = 0 := by
    intro i hQi hi
    rw [hkind i hQi]
    unfold periodicKind
    rw [if_neg]
    omega
  -- a synchronous slot is never committed: neither its direct commit nor a link holds
  have hnocommit : ∀ {j : ℕ} {A : BlockId}, S.kind j = 0 →
      (steelheadAt p).Decided U V j (some A) → False := by
    intro j A hj hd
    obtain ⟨hnc, hnl⟩ := hcl j A (hQ j _ hd) hj (AnchoredRule.isLeaderBlock_of_decided hd)
    cases hd with
    | directCommit _ hc =>
      change (p.rules (S.kind j)).Commit U V A (S.slotRound j) (S.kind j) at hc
      rw [hj, hid] at hc
      exact hnc V hc
    | indirectCommit _ _ _ _ _ _ _ hlink _ =>
      change (p.rules (S.kind j)).Link _ U _ A S j at hlink
      rw [hj] at hlink
      exact hnl _ _ hlink
  -- the middle slot of an asynchronous anchor's search is one period up
  have hmid_of_async : ∀ {i j : ℕ}, Q i → Q j → i % k = k - 1 → S.kind j = 1 →
      (steelheadAt p).Eligible i j →
      i < i + k ∧ i + k < j ∧ (steelheadAt p).Eligible i (i + k) := by
    intro i j hQi hQj hi hj helig
    have hsync := hsync_of_mod hQi hi
    have hasync : IsAsync k j := periodicKind_eq_one_iff.mp (hkind j hQj ▸ hj)
    have hw : (steelheadAt p).waveAt (S.kind i) = p.sync.waveAt 0 := by
      rw [hsync]
      rfl
    rw [AnchoredRule.eligible_iff, hid, hid, hw] at helig
    have := add_period_le_of_isAsync hk2 hi hasync (by omega)
    refine ⟨by omega, by omega, ?_⟩
    rw [AnchoredRule.eligible_iff, hid, hid, hw]
    omega
  -- a synchronous anchor is committed, which `hnocommit` excludes
  have hsync_anchor : ∀ {j : ℕ} {A : BlockId}, Q j → ¬ S.kind j = 1 →
      (steelheadAt p).Decided U V j (some A) → False := fun hQj hasync hj =>
    hnocommit (by rw [hkind _ hQj] at hasync ⊢; exact periodicKind_eq_zero_of_ne_one hasync) hj
  revert hi
  induction h with
  | @directCommit j L hL hc =>
    intro hi
    have hd := AnchoredRule.Decided.directCommit hL hc
    exact hnocommit (hsync_of_mod (hQ j _ hd) hi) hd
  | @directSkip j hs =>
    intro hi
    have hQj := hQ j none (AnchoredRule.Decided.directSkip hs)
    have hj := hsync_of_mod hQj hi
    change (p.rules (S.kind j)).Skip U V S j at hs
    rw [hj] at hs
    exact hskip j hQj hj hs
  | @indirectCommit i j A L _ hkj helig hj hmid hi' hemp hL hlink hleast _ ihmid =>
    intro hi
    have hQi := hQ i _
      (AnchoredRule.Decided.indirectCommit hkj helig hj hmid hi' hemp hL hlink hleast)
    by_cases hasync : S.kind j = 1
    · obtain ⟨h1, h2, h3⟩ := hmid_of_async hQi (hQ j _ hj) hi hasync helig
      exact ihmid (i + k) h1 h2 h3 (by rw [Nat.add_mod_right]; exact hi)
    · exact hsync_anchor (hQ j _ hj) hasync hj
  | @indirectSkip i j A hkj helig hj hmid hnone _ ihmid =>
    intro hi
    have hQi := hQ i _ (AnchoredRule.Decided.indirectSkip hkj helig hj hmid hnone)
    by_cases hasync : S.kind j = 1
    · obtain ⟨h1, h2, h3⟩ := hmid_of_async hQi (hQ j _ hj) hi hasync helig
      exact ihmid (i + k) h1 h2 h3 (by rw [Nat.add_mod_right]; exact hi)
    · exact hsync_anchor (hQ j _ hj) hasync hj

/-- **SH8.** `stall_of_pred` with nothing asked of the slots. -/
theorem stall {ws k : ℕ} (hw0 : p.sync.waveAt 0 + 1 = ws) (hws : 2 ≤ ws) (hk : ws ≤ k)
    (hid : ∀ s, S.slotRound s = s) (hkind : ∀ s, S.kind s = periodicKind k s)
    (hcl : ∀ (j : ℕ) (L : BlockId), S.kind j = 0 → IsLeaderBlock U j L →
      (∀ V' : View Validator BlockId Payload U, ¬ p.sync.Commit U V' L j 0) ∧
        ∀ (i : ℕ) (A : BlockId), ¬ p.sync.Link i U A L S j)
    (hskip : ∀ j, S.kind j = 0 → ¬ p.sync.Skip U V S j) {i : ℕ} (hi : i % k = k - 1)
    {v : Option BlockId} (h : (steelheadAt p).Decided U V i v) : False :=
  stall_of_pred hw0 hws hk hid (Q := fun _ => True) (fun s _ => hkind s) (fun _ _ _ => trivial)
    (fun j L _ => hcl j L) (fun j _ => hskip j) hi h

/-- **SH9b.** SH7a's argument at the output schedule, whose every slot is asynchronous: the
clause names a run past `r`, the asynchronous rule decides every slot below it, and at one kind
the pair's composite decides as that rule (SH4). -/
theorem allDecidedBelowAtPeriodOne {good : BlockUniverse Validator BlockId Payload → ℕ →
    Finset Validator} (hleast : LeastLinked p.async) (hgc : GoodCommits p.async good) {wa : ℕ}
    (hwa : p.async.waveAt 1 + 1 = wa) (hid : ∀ s, S.slotRound s = s) (hone : ∀ s, S.kind s = 1)
    {c N : ℕ} (hrun : RunWithin p.async good U c wa N) (hV : V.CoversUpto N) (r : ℕ)
    (hr : r + c + wa - 1 + (wa - 1) ≤ N) :
    ∃ b, r ≤ b ∧ ∀ i, i < b → ∃ v, (steelheadAt p).Decided U V i v := by
  have hmono : StrictMono S.slotRound := fun a b h => by rw [hid, hid]; exact h
  obtain ⟨b, hb, h⟩ := chainAllDecidedBelow (S' := S) hleast hgc
    (fun i => by rw [hone i, hwa]) hmono hrun hV r (by rw [hid]; exact hr)
  refine ⟨b, hb, fun i hi => ?_⟩
  obtain ⟨v, hv⟩ := h i hi
  exact ⟨v, (compose_decided_iff (rules := p.rules) (κ := 1) (RulePair.rules_rungs p)
    (RulePair.rules_tie p) hone).mpr hv⟩

end Pair

end Steelhead

end LeanDag
