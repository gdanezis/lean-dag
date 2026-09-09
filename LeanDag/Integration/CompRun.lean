import LeanDag.Integration.BarnacleFrame
import LeanDag.Integration.AdaptiveFrame
/-!
# A run of both mechanisms

`CompRun` carries Barnacle's configuration data and a frame, with one
slot numbering throughout: anchors are global slot indices and `cnt_eq`
is the bridge, a round of configuration `k` being `count k` slots wide.

`anchor_below` is `Params.gap`'s purpose, read at the run's own frame:
the anchor that sets a count lies two epochs below every round that count
governs. `cnt_det` and `anchor_det` are the two determinisms the
composition's safety argument needs — the widths from the configurations,
and the anchor from the verdicts.

What is not here is their assembly into
`Integration.frameRun_agree`'s `hwd`; `docs/adaptive-rounds.md` §6.2
records what that still asks for.

**Trusted core: `CompRun` is a definition.**
-/

namespace LeanDag
namespace Integration
open Barnacle Properties

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {R : Properties.DagRule Validator BlockId Payload} {P : Params}

/-- **A run of both mechanisms.** Barnacle's configuration data, and the
frame and verdicts of `FrameRun`. `cnt` is the frame's widths and
`cnt_eq` is the bridge: a round of configuration `k` is `count k` slots
wide. Anchors are global slot indices, so there is one numbering
throughout. -/
structure CompRun (W : ℕ) (P : Params)
    (upd : ℕ → ℕ → (U : R.Universe) → R.View U → BlockId → ℕ × ℕ)
    (U : R.Universe) (V : R.View U) (K : ℕ) where
  /-- The round after which configuration `k` is in force. -/
  start : ℕ → ℕ
  /-- Its leader count, back-off, and the global slot of its anchor. -/
  count : ℕ → ℕ
  backoff : ℕ → ℕ
  anchor : ℕ → ℕ
  /-- The schedule's round widths. -/
  F : Frame
  /-- The global verdicts. -/
  vdct : ℕ → Option BlockId
  init : start 0 = 0 ∧ count 0 = 1 ∧ backoff 0 = 0
  count_pos : ∀ k, 0 < count k
  /-- **A round of a configuration is that configuration's count wide.**
  Round `0` precedes every range and is genesis, at one leader. -/
  cnt_zero : F.width 0 = 1
  cnt_eq : ∀ k, k < K → ∀ r, start k < r → r ≤ start (k + 1) → F.width r = count k
  /-- **The anchor is committed past the threshold, and least such.**
  The threshold is `Frame.cum` of the first round past it, which is the
  same slot as Barnacle's round condition by
  `Frame.cum_le_iff_le_roundOf` — and unlike the round condition it is
  fixed by the widths *below* the threshold, so two runs agree about it
  long before they agree about where their configurations end. -/
  anchor_commits : ∀ k, k < K → (∃ A, vdct (anchor k) = some A) ∧
    F.cum (start k + P.interval + 1) ≤ anchor k
  anchor_least : ∀ k, k < K → ∀ g, F.cum (start k + P.interval + 1) ≤ g →
    g < anchor k → vdct g = none
  /-- The next configuration begins `P.gap` rounds after the anchor's. -/
  start_succ : ∀ k, k < K → start (k + 1) = F.roundOf (anchor k) + P.gap
  /-- The next configuration is the rule's, at the anchor's block. -/
  update : ∀ k, k < K → ∀ A, vdct (anchor k) = some A →
    (count (k + 1), backoff (k + 1)) = upd (count k) (backoff k) U V A

namespace CompRun

variable {W : ℕ} {upd : ℕ → ℕ → (U : R.Universe) → R.View U → BlockId → ℕ × ℕ}
variable {U : R.Universe} {V : R.View U} {K : ℕ}

theorem start_lt (Rn : CompRun (R := R) W P upd U V K) (k : ℕ) (hk : k < K) :
    Rn.start k < Rn.start (k + 1) := by
  obtain ⟨-, hthr⟩ := Rn.anchor_commits k hk
  have hr : Rn.start k + P.interval + 1 ≤ Rn.F.roundOf (Rn.anchor k) :=
    Rn.F.cum_le_iff_le_roundOf.mp hthr
  rw [Rn.start_succ k hk]
  have := P.interval_pos
  omega

theorem start_mono (Rn : CompRun (R := R) W P upd U V K) {a b : ℕ} (hab : a ≤ b)
    (hb : b ≤ K) : Rn.start a ≤ Rn.start b := by
  induction b with
  | zero => have : a = 0 := by omega
            subst this; exact le_refl _
  | succ j ih =>
      rcases Nat.eq_or_lt_of_le hab with h | h
      · subst h; exact le_refl _
      · exact le_trans (ih (by omega) (by omega)) (le_of_lt (Rn.start_lt j (by omega)))

/-- **The anchor of an earlier configuration is two epochs below.** The
run's own frame, read through `anchor_two_epochs_below`'s counting. -/
theorem anchor_below (Rn : CompRun (R := R) W P upd U V K) (hW : 0 < W)
    (hgap : P.gap = 2 * W) {k : ℕ} (hk : k < K) {r : ℕ} (hr : Rn.start (k + 1) < r) :
    epochOf W (Rn.anchor k) + 2 ≤ epochOf W (Rn.F.cum r) := by
  have hstart : Rn.start (k + 1) = Rn.F.roundOf (Rn.anchor k) + P.gap :=
    Rn.start_succ k hk
  have hglt : Rn.anchor k < Rn.F.cum (Rn.F.roundOf (Rn.anchor k) + 1) :=
    Rn.F.lt_cum_roundOf_succ _
  have hgapr : Rn.F.cum (Rn.F.roundOf (Rn.anchor k) + 1) + P.gap
      ≤ Rn.F.cum (Rn.start (k + 1) + 1) := Rn.F.cum_gap (by omega)
  have hmono : Rn.F.cum (Rn.start (k + 1) + 1) ≤ Rn.F.cum r :=
    Rn.F.cum_mono (by omega)
  exact epochOf_add_two hW (by omega)


/-- Every round a run covers lies in one configuration's range. -/
theorem exists_cfg (Rn : CompRun (R := R) W P upd U V K) {k r : ℕ} (hk : k < K)
    (hr : 0 < r) (hrk : r ≤ Rn.start (k + 1)) :
    ∃ j, j ≤ k ∧ Rn.start j < r ∧ r ≤ Rn.start (j + 1) := by
  induction k with
  | zero => exact ⟨0, le_refl _, by rw [Rn.init.1]; omega, hrk⟩
  | succ i ih =>
      by_cases h : r ≤ Rn.start (i + 1)
      · obtain ⟨j, hj, h1, h2⟩ := ih (by omega) h
        exact ⟨j, by omega, h1, h2⟩
      · exact ⟨i + 1, le_refl _, by omega, hrk⟩

/-- **Agreeing configurations give agreeing widths**, at every round the
runs cover. -/
theorem cnt_det {Rn Rn' : CompRun (R := R) W P upd U V K} {k : ℕ} (hk : k < K)
    (h : ∀ j, j ≤ k + 1 → Rn.start j = Rn'.start j ∧ Rn.count j = Rn'.count j)
    {r : ℕ} (hrk : r ≤ Rn.start (k + 1)) : Rn.F.width r = Rn'.F.width r := by
  rcases Nat.eq_zero_or_pos r with h0 | h0
  · subst h0; rw [Rn.cnt_zero, Rn'.cnt_zero]
  · obtain ⟨j, hj, h1, h2⟩ := Rn.exists_cfg hk h0 hrk
    obtain ⟨hs, hc⟩ := h j (by omega)
    have hs1 : Rn.start (j + 1) = Rn'.start (j + 1) := (h (j + 1) (by omega)).1
    rw [Rn.cnt_eq j (by omega) r h1 h2, Rn'.cnt_eq j (by omega) r (by omega) (by omega), hc]


/-- **The anchor is a function of the verdicts.** Both runs' anchors are
the least committed slot at or past the same threshold, and a set has one
least element. The widths need only agree below the threshold's round,
which is `P.interval` above the configuration's start and so well inside
both runs' ranges — no round above an anchor is read, which is what lets
this be proved before the configurations' extents are known. -/
theorem anchor_det {Rn Rn' : CompRun (R := R) W P upd U V K} {k : ℕ} (hk : k < K)
    (hs : Rn.start k = Rn'.start k)
    (hcnt : ∀ r, r < Rn.start k + P.interval + 1 → Rn'.F.width r = Rn.F.width r)
    (hv : ∀ g, g ≤ Rn.anchor k → g ≤ Rn'.anchor k → Rn.vdct g = Rn'.vdct g) :
    Rn.anchor k = Rn'.anchor k := by
  obtain ⟨⟨A, hA⟩, hthr⟩ := Rn.anchor_commits k hk
  obtain ⟨⟨A', hA'⟩, hthr'⟩ := Rn'.anchor_commits k hk
  have hcum : Rn'.F.cum (Rn.start k + P.interval + 1)
      = Rn.F.cum (Rn.start k + P.interval + 1) := Frame.cum_congr hcnt (le_refl _)
  rw [← hs] at hthr'
  rw [hcum] at hthr'
  rcases Nat.lt_trichotomy (Rn.anchor k) (Rn'.anchor k) with hlt | heq | hgt
  · exfalso
    have hno := Rn'.anchor_least k hk (Rn.anchor k) (by rw [← hs, hcum]; exact hthr) hlt
    rw [← hv (Rn.anchor k) (le_refl _) (le_of_lt hlt)] at hno
    exact absurd (hno ▸ hA) (by simp)
  · exact heq
  · exfalso
    have hno := Rn.anchor_least k hk (Rn'.anchor k) hthr' hgt
    rw [hv (Rn'.anchor k) (le_of_lt hgt) (le_refl _)] at hno
    exact absurd (hno ▸ hA') (by simp)


/-- **Widths agree as far as both configurations reach.** Below the
configuration's start by hypothesis, and inside it because both give the
round the same count. -/
theorem cnt_agree_upto {Rn Rn' : CompRun (R := R) W P upd U V K} {k : ℕ} (hk : k < K)
    (hs : Rn.start k = Rn'.start k) (hc : Rn.count k = Rn'.count k)
    (hlow : ∀ r, r ≤ Rn.start k → Rn'.F.width r = Rn.F.width r)
    {b : ℕ} (hb : b ≤ Rn.start (k + 1)) (hb' : b ≤ Rn'.start (k + 1)) :
    ∀ r, r ≤ b → Rn'.F.width r = Rn.F.width r := by
  intro r hr
  rcases Nat.lt_or_ge (Rn.start k) r with h | h
  · rw [Rn.cnt_eq k hk r h (by omega), Rn'.cnt_eq k hk r (by omega) (by omega), hc]
  · exact hlow r h

/-- The threshold's round is inside the configuration. -/
theorem thr_lt_start_succ (Rn : CompRun (R := R) W P upd U V K) (k : ℕ) (hk : k < K) :
    Rn.start k + P.interval + 1 ≤ Rn.start (k + 1) := by
  obtain ⟨-, hthr⟩ := Rn.anchor_commits k hk
  have hr : Rn.start k + P.interval + 1 ≤ Rn.F.roundOf (Rn.anchor k) :=
    Rn.F.cum_le_iff_le_roundOf.mp hthr
  rw [Rn.start_succ k hk]; omega

/-- **And so the next configuration starts at the same round.** With the
anchors equal as slots, the two runs disagree about the round only if
they disagree about the widths below it — and where they would have to
disagree is inside the shorter of the two ranges, where they cannot. -/
theorem start_succ_det {Rn Rn' : CompRun (R := R) W P upd U V K} {k : ℕ} (hk : k < K)
    (hs : Rn.start k = Rn'.start k) (hc : Rn.count k = Rn'.count k)
    (hlow : ∀ r, r ≤ Rn.start k → Rn'.F.width r = Rn.F.width r)
    (ha : Rn.anchor k = Rn'.anchor k) :
    Rn.start (k + 1) = Rn'.start (k + 1) := by
  have e := Rn.start_succ k hk
  have e' := Rn'.start_succ k hk
  rcases Nat.lt_trichotomy (Rn.F.roundOf (Rn.anchor k)) (Rn'.F.roundOf (Rn'.anchor k))
    with hlt | heq | hgt
  · exfalso
    have hw := cnt_agree_upto hk hs hc hlow (b := Rn.start (k + 1)) (le_refl _) (by omega)
    have hcg : Rn'.F.roundOf (Rn.anchor k) = Rn.F.roundOf (Rn.anchor k) :=
      Frame.roundOf_congr (F := Rn.F) (F' := Rn'.F) (B := Rn.start (k + 1) + 1)
        (fun r hr => hw r (by omega)) (by omega)
    rw [ha] at hcg hlt; omega
  · omega
  · exfalso
    have hw := cnt_agree_upto hk hs hc hlow (b := Rn'.start (k + 1)) (by omega) (le_refl _)
    have hcg : Rn.F.roundOf (Rn'.anchor k) = Rn'.F.roundOf (Rn'.anchor k) :=
      Frame.roundOf_congr (F := Rn'.F) (F' := Rn.F) (B := Rn'.start (k + 1) + 1)
        (fun r hr => (hw r (by omega)).symm) (by omega)
    rw [← ha] at hcg hgt; omega

/-- **The configuration data is a function of the verdicts.** -/
theorem config_det {Rn Rn' : CompRun (R := R) W P upd U V K} {kb : ℕ} (hkb : kb ≤ K)
    (hv : ∀ j, j < kb → ∀ g, g ≤ Rn.anchor j → Rn.vdct g = Rn'.vdct g) :
    ∀ k, k ≤ kb →
      (Rn.start k = Rn'.start k ∧ Rn.count k = Rn'.count k ∧
        Rn.backoff k = Rn'.backoff k) ∧
      (∀ r, r ≤ Rn.start k → Rn'.F.width r = Rn.F.width r) := by
  intro k
  induction k with
  | zero =>
      intro _
      obtain ⟨s, c, b⟩ := Rn.init
      obtain ⟨s', c', b'⟩ := Rn'.init
      refine ⟨⟨by rw [s, s'], by rw [c, c'], by rw [b, b']⟩, fun r hr => ?_⟩
      have : r = 0 := by rw [s] at hr; omega
      subst this
      rw [Rn.cnt_zero, Rn'.cnt_zero]
  | succ k ih =>
      intro hk1
      obtain ⟨⟨hs, hc, hb⟩, hlow⟩ := ih (by omega)
      have hkb' : k < kb := by omega
      have hk : k < K := by omega
      have hthr := Rn.thr_lt_start_succ k hk
      have hthr' := Rn'.thr_lt_start_succ k hk
      have hwthr := cnt_agree_upto hk hs hc hlow
        (b := Rn.start k + P.interval + 1) (by omega) (by omega)
      have ha : Rn.anchor k = Rn'.anchor k :=
        anchor_det hk hs (fun r hr => hwthr r (by omega))
          (fun g hg _ => hv k hkb' g hg)
      have hs1 : Rn.start (k + 1) = Rn'.start (k + 1) := start_succ_det hk hs hc hlow ha
      obtain ⟨⟨A, hA⟩, -⟩ := Rn.anchor_commits k hk
      have hA' : Rn'.vdct (Rn'.anchor k) = some A := by
        rw [← ha, ← hv k hkb' (Rn.anchor k) (le_refl _)]; exact hA
      have u := Rn.update k hk A hA
      have u' := Rn'.update k hk A hA'
      rw [hc, hb] at u
      have hu := u.trans u'.symm
      refine ⟨⟨hs1, congrArg Prod.fst hu, congrArg Prod.snd hu⟩, ?_⟩
      exact cnt_agree_upto hk hs hc hlow (b := Rn.start (k + 1)) (le_refl _) (by omega)


/-- **The widths are a function of the verdicts two epochs below.** This
is `Integration.frameRun_agree`'s `hwd`, at a run of both mechanisms.

The width of a round of configuration `k` is `count k`, which the anchor
of configuration `k - 1` sets, and that anchor lies two epochs below by
`anchor_below` — so the count follows from `config_det`. What needs more
is the other run's *extent*: reading its width at `r` through `cnt_eq`
asks `r ≤ Rn'.start (k + 1)`, which configuration `k`'s own anchor
settles, and that anchor is not two epochs below `r`. It is refuted
instead: were the other run's configuration to end before `r`, its anchor
would lie two epochs below after all, so the two anchors would agree and
the two configurations would end together. -/
theorem width_det {Rn Rn' : CompRun (R := R) W P upd U V K} (hW : 0 < W)
    (hgap : P.gap = 2 * W) {k : ℕ} (hk : k < K) {r : ℕ}
    (hlo : Rn.start k < r) (hhi : r ≤ Rn.start (k + 1))
    (hv : ∀ g, epochOf W g + 2 ≤ epochOf W (Rn.F.cum r) → Rn.vdct g = Rn'.vdct g) :
    Rn'.F.width r = Rn.F.width r := by
  -- the configurations below `k` agree, since their anchors are two epochs down
  obtain ⟨⟨hs, hc, -⟩, hlow⟩ :=
    config_det (Rn := Rn) (Rn' := Rn') (kb := k) (by omega)
      (fun j hj g hg => hv g (le_trans (Nat.add_le_add_right (epochOf_mono W hg) 2)
        (Rn.anchor_below hW hgap (by omega)
          (lt_of_le_of_lt (Rn.start_mono (by omega) (by omega)) hlo)))) k (le_refl _)
  -- and so does the extent of configuration `k` itself
  have hext : r ≤ Rn'.start (k + 1) := by
    by_contra hc'
    push_neg at hc'
    have hw2 := cnt_agree_upto hk hs hc hlow (b := Rn'.start (k + 1)) (by omega) (le_refl _)
    have hcum : ∀ x, x ≤ Rn'.start (k + 1) + 1 → Rn'.F.cum x = Rn.F.cum x :=
      fun x hx => Frame.cum_congr (fun s hs' => hw2 s (by omega)) hx
    have e' := Rn'.start_succ k hk
    obtain ⟨-, hthr'⟩ := Rn'.anchor_commits k hk
    have hgapp : P.gap ≤ Rn'.start (k + 1) := by omega
    -- the other run's anchor is two epochs below `r`
    have h1 : Rn'.anchor k < Rn'.F.cum (Rn'.F.roundOf (Rn'.anchor k) + 1) :=
      Rn'.F.lt_cum_roundOf_succ _
    have h2 : Rn'.F.cum (Rn'.F.roundOf (Rn'.anchor k) + 1)
        = Rn.F.cum (Rn'.F.roundOf (Rn'.anchor k) + 1) := hcum _ (by omega)
    have h3 : Rn.F.cum (Rn'.F.roundOf (Rn'.anchor k) + 1) + P.gap
        ≤ Rn.F.cum (Rn'.start (k + 1) + 1) := Rn.F.cum_gap (by omega)
    have h4 : Rn.F.cum (Rn'.start (k + 1) + 1) ≤ Rn.F.cum r := Rn.F.cum_mono (by omega)
    have hbelow : epochOf W (Rn'.anchor k) + 2 ≤ epochOf W (Rn.F.cum r) :=
      epochOf_add_two hW (by omega)
    -- so the anchors agree, and the configurations end together
    have hwthr := cnt_agree_upto hk hs hc hlow
      (b := Rn.start k + P.interval + 1)
      (by have := Rn.thr_lt_start_succ k hk; omega)
      (by have := Rn'.thr_lt_start_succ k hk; omega)
    have ha : Rn.anchor k = Rn'.anchor k :=
      anchor_det hk hs (fun s hs' => hwthr s (by omega))
        (fun g _ hg2 => hv g (le_trans (Nat.add_le_add_right (epochOf_mono W hg2) 2) hbelow))
    have hs1 := start_succ_det hk hs hc hlow ha
    omega
  rw [Rn.cnt_eq k hk r hlo hhi, Rn'.cnt_eq k hk r (by omega) hext, hc]

end CompRun


end Integration
end LeanDag
