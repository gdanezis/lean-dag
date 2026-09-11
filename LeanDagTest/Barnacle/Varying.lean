import LeanDagTest.Barnacle.Agreement
/-!
# Barnacle witnesses — a reconfiguration that changes all three

Every witness so far reconfigures the way the paper's rule does: a new
count, the same leaders, the same interval. The run structure asks for
none of that. `varC` is a configuration that differs from the genesis one
in **all three** — round `4` is two slots wide where every other round is
one, the leaders are the rotation shifted by a round, and the interval is
two rather than one — and `varRun` is a height-`2` run that installs it,
decides its range against its schedule, and finds its anchor under it.

The rule is `varUpd`, which reads the anchor's round and is not the AIMD
rule: BN3 and BN5 hold for every update rule, and this is the witness
that the generality is not idle. What the file exhibits:

* the three differences, each on data;
* `varC`'s slot numbering: round `4` holds slots `4` and `5`, so slot `6`
  is round `5` where under one leader a round it would be round `6`;
* every clause of `PartialRun` at height `2`, with range `1` decided
  against `varC.sched`;
* BN3 on two views, which identifies the installed configuration itself —
  not a count — and BN5 on the ledger the two ranges produce.
-/

namespace LeanDagTest

namespace Barnacle

set_option maxRecDepth 4096

open LeanDag LeanDag.Barnacle

/-! ## The configuration the run installs -/

/-- Round `4` is two slots wide; every other round one. -/
def varSlots : ℕ → ℕ := fun r => if r = 4 then 2 else 1

/-- The rotation shifted by a round: slot `i` of round `r` is led by
`(r + i + 1) % 4`, where the genesis configuration's leader is
`(r + i) % 4`. -/
def varLead : ℕ → ℕ → Fin 4 := fun r i => ⟨(r + i + 1) % 4, Nat.mod_lt _ (by omega)⟩

/-- A configuration of varying width, on shifted leaders, at interval
two. -/
def varC : Config (Fin 4) where
  slotsAt := varSlots
  slotsAt_pos := by intro r; unfold varSlots; split <;> omega
  lead := varLead
  keyed := by
    intro r i j hi hj h
    have hi' : i < 2 := by unfold varSlots at hi; split at hi <;> omega
    have hj' : j < 2 := by unfold varSlots at hj; split at hj <;> omega
    have := congrArg Fin.val h
    simp only [varLead] at this
    omega
  interval := 2

/-! ### The three differences, on data -/

-- A round's width: round `4` holds two slots, where the genesis
-- configuration holds one at every round.
example : varC.slotsAt 4 = 2 ∧ bnC1I1.slotsAt 4 = 1 := by decide
-- A leader: round `3`'s first slot is led by validator `0` here and by
-- validator `3` there.
example : varC.head 3 = 0 ∧ bnC1I1.head 3 = 3 := by decide
-- The interval.
example : varC.interval = 2 ∧ bnC1I1.interval = 1 := by decide

/-! ### What the widths do to the slot numbering -/

-- Rounds `0` to `3` hold one slot each, round `4` holds `4` and `5`, and
-- round `5` holds slot `6` — which under one leader a round would be
-- round `6`.
example : varC.cum 4 = 4 ∧ varC.cum 5 = 6 ∧ varC.cum 6 = 7 := by decide
example : varC.roundOf 4 = 4 ∧ varC.roundOf 5 = 4 ∧ varC.roundOf 6 = 5 := by decide
example : bnC1I1.roundOf 6 = 6 := by decide
-- The two slots of round `4` have different leaders, which is `keyed`.
example : varC.sched.leader 4 = 1 ∧ varC.sched.leader 5 = 2 := by decide

/-! ## The run

At most four leaders a round and at most two rounds between
reconfigurations. -/

def varP : Params := ⟨4, 2, 96, 100, by decide⟩

/-- The rule: on an anchor at round `2` install `varC` and step the
back-off; otherwise fall back to the genesis configuration. It reads the
universe and the anchor and not the view, so it is `Anchored`. -/
def varUpd : UpdateRule bnRule32 :=
  fun _ b U _V A => if (bnRule32.block U A).round = 2 then (varC, b + 1) else (bnC1I1, 0)

theorem varUpd_anchored : Anchored bnRule32 varUpd := fun _ _ _ _ _ _ => rfl

/-- The verdicts: range `0` commits slots `1` and `2` of the genesis
schedule, range `1` slots `3` to `6` of `varC`'s. -/
def vdVar : ℕ → ℕ → Option (Fin 32) := fun k κ =>
  if k = 0 then (if κ = 1 then some 5 else if κ = 2 then some 10 else none)
  else if k = 1 then
    (if κ = 3 then some 12 else if κ = 4 then some 17 else if κ = 5 then some 18
      else if κ = 6 then some 22 else none)
  else none

/-- Configuration `0` is the genesis one and closes at round `2`;
configuration `1` is `varC` and closes at round `5`, its anchor being
slot `6` — the first slot of round `5` under widths that gave round `4`
two. -/
def varRun : PartialRun bnRule32 varP varUpd bnC1I1 Usun Vsun 2 where
  start := fun k => if k = 0 then 0 else if k = 1 then 2 else 5
  cfg := fun k => if k = 1 then varC else bnC1I1
  backoff := fun k => if k = 1 then 1 else 0
  anchor := fun k => if k = 0 then 2 else 6
  vdct := vdVar
  init := ⟨rfl, rfl, rfl⟩
  bounds := by
    intro k
    by_cases h : k = 1
    · subst h
      refine ⟨fun r => ?_, (by decide : (0 : ℕ) < 2), (by decide : (2 : ℕ) ≤ 2)⟩
      change varSlots r ≤ 4
      unfold varSlots; split <;> omega
    · simp only [h, if_false]
      exact ⟨fun _ => (by decide : (1 : ℕ) ≤ 4), (by decide : (0 : ℕ) < 1),
        (by decide : (1 : ℕ) ≤ 2)⟩
  closed := by
    intro k hk κ h1 h2
    have hkk : k = 0 ∨ k = 1 := by omega
    rcases hkk with rfl | rfl
    · -- range `0`, at the genesis configuration: slot `κ` is round `κ`
      simp only [bnC1I1, bnCfg] at h1 h2 ⊢
      norm_num [Config.uniform_roundOf] at h1 h2 ⊢
      have : κ = 1 ∨ κ = 2 := by omega
      rcases this with rfl | rfl <;>
        exact Decided.directCommit (S := bnC1I1.sched) (by decide) (by decide)
    · -- range `1`, at `varC`: the round bounds are read through `cum`
      norm_num at h1 h2 ⊢
      have hlo : (3 : ℕ) ≤ κ := by
        have h3 : varC.cum 3 = 3 := by decide
        have := (Config.cum_le_iff_le_roundOf varC (r := 3) (g := κ)).2 (by omega)
        omega
      have hhi : κ < 7 := by
        by_contra hc
        have h7 : varC.cum 6 = 7 := by decide
        have := (Config.cum_le_iff_le_roundOf varC (r := 6) (g := κ)).1 (by omega)
        omega
      interval_cases κ <;>
        exact Decided.directCommit (S := varC.sched) (by decide) (by decide)
  anchor_commits := by
    intro k hk
    have hkk : k = 0 ∨ k = 1 := by omega
    rcases hkk with rfl | rfl
    · exact ⟨⟨10, rfl⟩, by decide⟩
    · exact ⟨⟨22, rfl⟩, by decide⟩
  anchor_least := by
    intro k hk κ hκ h
    have hkk : k = 0 ∨ k = 1 := by omega
    rcases hkk with rfl | rfl
    · simp only [bnC1I1, bnCfg] at h hκ
      norm_num [Config.uniform_roundOf] at h hκ ⊢
      omega
    · -- below slot `6` no round exceeds `4`, so nothing passes the threshold
      norm_num at h hκ ⊢
      have hi : varC.interval = 2 := rfl
      have h5 : varC.cum 5 = 6 := by decide
      have := (Config.cum_le_iff_le_roundOf varC (r := 5) (g := κ)).2 (by omega)
      omega
  start_succ := by
    intro k hk
    have hkk : k = 0 ∨ k = 1 := by omega
    rcases hkk with rfl | rfl
    · decide
    · decide
  update := by
    intro k hk A hA
    have hkk : k = 0 ∨ k = 1 := by omega
    rcases hkk with rfl | rfl
    · have hA' : A = 10 := by simp [vdVar] at hA; exact hA.symm
      subst hA'; rfl
    · have hA' : A = 22 := by simp [vdVar] at hA; exact hA.symm
      subst hA'; rfl

def varRun' : PartialRun bnRule32 varP varUpd bnC1I1 Usun Vsun' 2 where
  start := fun k => if k = 0 then 0 else if k = 1 then 2 else 5
  cfg := fun k => if k = 1 then varC else bnC1I1
  backoff := fun k => if k = 1 then 1 else 0
  anchor := fun k => if k = 0 then 2 else 6
  vdct := vdVar
  init := ⟨rfl, rfl, rfl⟩
  bounds := by
    intro k
    by_cases h : k = 1
    · subst h
      refine ⟨fun r => ?_, (by decide : (0 : ℕ) < 2), (by decide : (2 : ℕ) ≤ 2)⟩
      change varSlots r ≤ 4
      unfold varSlots; split <;> omega
    · simp only [h, if_false]
      exact ⟨fun _ => (by decide : (1 : ℕ) ≤ 4), (by decide : (0 : ℕ) < 1),
        (by decide : (1 : ℕ) ≤ 2)⟩
  closed := by
    intro k hk κ h1 h2
    have hkk : k = 0 ∨ k = 1 := by omega
    rcases hkk with rfl | rfl
    · -- range `0`, at the genesis configuration: slot `κ` is round `κ`
      simp only [bnC1I1, bnCfg] at h1 h2 ⊢
      norm_num [Config.uniform_roundOf] at h1 h2 ⊢
      have : κ = 1 ∨ κ = 2 := by omega
      rcases this with rfl | rfl <;>
        exact Decided.directCommit (S := bnC1I1.sched) (by decide) (by decide)
    · -- range `1`, at `varC`: the round bounds are read through `cum`
      norm_num at h1 h2 ⊢
      have hlo : (3 : ℕ) ≤ κ := by
        have h3 : varC.cum 3 = 3 := by decide
        have := (Config.cum_le_iff_le_roundOf varC (r := 3) (g := κ)).2 (by omega)
        omega
      have hhi : κ < 7 := by
        by_contra hc
        have h7 : varC.cum 6 = 7 := by decide
        have := (Config.cum_le_iff_le_roundOf varC (r := 6) (g := κ)).1 (by omega)
        omega
      interval_cases κ <;>
        exact Decided.directCommit (S := varC.sched) (by decide) (by decide)
  anchor_commits := by
    intro k hk
    have hkk : k = 0 ∨ k = 1 := by omega
    rcases hkk with rfl | rfl
    · exact ⟨⟨10, rfl⟩, by decide⟩
    · exact ⟨⟨22, rfl⟩, by decide⟩
  anchor_least := by
    intro k hk κ hκ h
    have hkk : k = 0 ∨ k = 1 := by omega
    rcases hkk with rfl | rfl
    · simp only [bnC1I1, bnCfg] at h hκ
      norm_num [Config.uniform_roundOf] at h hκ ⊢
      omega
    · -- below slot `6` no round exceeds `4`, so nothing passes the threshold
      norm_num at h hκ ⊢
      have hi : varC.interval = 2 := rfl
      have h5 : varC.cum 5 = 6 := by decide
      have := (Config.cum_le_iff_le_roundOf varC (r := 5) (g := κ)).2 (by omega)
      omega
  start_succ := by
    intro k hk
    have hkk : k = 0 ∨ k = 1 := by omega
    rcases hkk with rfl | rfl
    · decide
    · decide
  update := by
    intro k hk A hA
    have hkk : k = 0 ∨ k = 1 := by omega
    rcases hkk with rfl | rfl
    · have hA' : A = 10 := by simp [vdVar] at hA; exact hA.symm
      subst hA'; rfl
    · have hA' : A = 22 := by simp [vdVar] at hA; exact hA.symm
      subst hA'; rfl

/-! ## What the run says -/

-- The configuration in force after round `2` is `varC`, and it is gone
-- again after round `5`.
example : varRun.cfg 1 = varC ∧ varRun.cfg 2 = bnC1I1 := ⟨rfl, rfl⟩
example : varRun.start 1 = 2 ∧ varRun.start 2 = 5 := ⟨rfl, rfl⟩
-- Range `1` runs over rounds `3` to `5`, which is four slots because
-- round `4` is two wide.
example : varRun.rangeLedger 1 = [12, 17, 18, 22] := by decide
example : varRun.ledgerUpto 2 = [5, 10, 12, 17, 18, 22] := by decide

/-! ## BN3 and BN5 on it

BN3 identifies the *configuration* the two views installed, which under
this rule is not a count: `varC` differs from the genesis configuration
in its widths, its leaders and its interval, and agreement is on the
whole of it. -/

example : varRun.start 1 = varRun'.start 1 ∧ varRun.cfg 1 = varRun'.cfg 1 ∧
    varRun.backoff 1 = varRun'.backoff 1 :=
  let h := Agreement.holds (Fin 4) (Fin 32) Unit bnRule32 agree32 varP varUpd bnC1I1
    varUpd_anchored Usun Vsun Vsun' 2 2 varRun varRun' 1 (by decide)
  ⟨h.1, h.2.1, h.2.2.1⟩

-- The anchor of the varying range, and the verdicts of its slots.
example : varRun.anchor 1 = varRun'.anchor 1 :=
  ((Agreement.holds (Fin 4) (Fin 32) Unit bnRule32 agree32 varP varUpd bnC1I1
    varUpd_anchored Usun Vsun Vsun' 2 2 varRun varRun' 1 (by decide)).2.2.2
    (by decide)).1
example : varRun.vdct 1 5 = varRun'.vdct 1 5 :=
  ((Agreement.holds (Fin 4) (Fin 32) Unit bnRule32 agree32 varP varUpd bnC1I1
    varUpd_anchored Usun Vsun Vsun' 2 2 varRun varRun' 1 (by decide)).2.2.2
    (by decide)).2 5 (by decide) (by decide)

-- BN5: one ledger, without repetition, across a reconfiguration that
-- changed the widths.
example : varRun.ledgerUpto 2 = varRun'.ledgerUpto 2 :=
  ((Ledger.holds (Fin 4) (Fin 32) Unit bnRule32 agree32 candidates32 varP varUpd bnC1I1
    varUpd_anchored).1 Usun Vsun Vsun' 2 2 varRun varRun').2 2 (by decide)
example : (varRun.ledgerUpto 2).Nodup :=
  (Ledger.holds (Fin 4) (Fin 32) Unit bnRule32 agree32 candidates32 varP varUpd bnC1I1
    varUpd_anchored).2.2 Usun Vsun 2 varRun 2 le_rfl
example : varRun.ledgerUpto 1 <+: varRun.ledgerUpto 2 :=
  (Ledger.holds (Fin 4) (Fin 32) Unit bnRule32 agree32 candidates32 varP varUpd bnC1I1
    varUpd_anchored).2.1 Usun Vsun 2 varRun 1 2 (by decide)

#print axioms varRun
#print axioms varRun'

end Barnacle

end LeanDagTest
