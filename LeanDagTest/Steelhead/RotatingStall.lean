import LeanDagTest.Mysticeti.Growth
import LeanDag.Steelhead.Helpers.Replay
import LeanDag.Steelhead.Helpers.Liveness
import LeanDag.Steelhead.Helpers.Period
import LeanDag.Common.Ledger
/-!
# Steelhead witnesses: Algorithm 2 retains a stalled period through every horizon

Finding 3 of `steelhead.md` §7 on data at every horizon. The family `rtDag N` grows the DAG of
the other witnesses to round `N`: the known leader of round `r` is validator `r mod 4`, and at
round `m` the blocks of validator `0` and of the leader of round `m − 1` reference every block
of round `m − 1` while the other two omit the leader's, so that every synchronous slot has two
votes and two blames, neither a quorum, while every asynchronous slot commits directly whatever
the coin. With the interval `8`, candidates `[1, 2, 4]`, the initial period `4`, the waves `3`
and `5`, a probe at every round and hysteresis `1/2`, the parameters the implementation accepts:

* **Algorithm 2 answers period `4` at every anchor**, at every horizon and whatever the anchor
  block: the window of an anchor spans at most nine rounds, on which periods `1` and `2` score at
  least half of what period `4` can (`anchorUpdate_half_retains`). What can leave that period is
  the scan's failover, not the replay (`PeriodAt.anchor`);
* **at period `4` slot `3` is never decided** (SH8), so the output never passes round `2`: no
  settled prefix of the adaptive output has more than three slots, and no block above round `2`
  is ever in the ledger, while validator `1`'s round-`3` block, an honest one, exists.

The period sequence is asked to be `4` on the intervals the record's rounds fall in, the
replay's answer at every anchor; the failover derives `1` from interval `2` on instead
(`Failover.lean`), so this is the schedule of the replay alone, and what it shows is that the
replay does not resolve the stall by itself. A derivation for slot `3` reads no wavelength
above the record's top round (`decided_congr`).
-/

namespace LeanDagTest

open LeanDag LeanDag.Steelhead LeanDag.Steelhead.Replay

/-- The known leader of round `r`: validator `r mod 4`. -/
def rtKnown (r : ℕ) : Fin 4 := ⟨r % 4, Nat.mod_lt _ (by decide)⟩

/-- The references of block `b`, at round `m = b / 4`: validator `0` and the leader of round
`m − 1` reference all of round `m − 1`, the other two omit the leader's block. -/
def rtRefs (b : ℕ) : Finset ℕ := (growRefs b).filter fun q =>
  b % 4 = 0 ∨ b % 4 = (b / 4 - 1) % 4 ∨ q % 4 ≠ (b / 4 - 1) % 4

/-- **`rtDag N`**: rounds `0` to `N` of the rotating stall. -/
def rtDag (N : ℕ) : BlockUniverse (Fin 4) ℕ Unit :=
  rrUniverse N rtRefs
    (fun _ _ h => Finset.mem_Ico.mp (Finset.mem_filter.mp h).1)
    (by
      intro b hb
      have hs : Finset.univ.erase (rtKnown (b / 4 - 1)) ⊆
          creators (rrBlock rtRefs) (rrBlock rtRefs b) := by
        intro v hv
        have hn : v.val ≠ (b / 4 - 1) % 4 := fun h =>
          (Finset.mem_erase.mp hv).1 (Fin.ext h)
        refine Finset.mem_image.mpr ⟨4 * (b / 4) - 4 + v.val, ?_, ?_⟩
        · change _ ∈ rtRefs b
          simp only [rtRefs, growRefs, Finset.mem_filter, Finset.mem_Ico]
          exact ⟨by omega, Or.inr (Or.inr (by omega))⟩
        · apply Fin.ext
          change (4 * (b / 4) - 4 + v.val) % 4 = v.val
          omega
      have hc : (Finset.univ.erase (rtKnown (b / 4 - 1))).card = 3 := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
      have := Finset.card_le_card hs
      omega)
    (by
      intro b hb
      simp only [rtRefs, growRefs, Finset.mem_filter, Finset.mem_Ico]
      exact ⟨by omega, by omega⟩)

/-- The waves `3` and `5`, a probe at every round, and the rotating known leader. -/
def rtConfig : Config (Fin 4) := ⟨3, 5, some 1, rtKnown⟩

/-- **Algorithm 2 at hysteresis `1/2`** on `rtDag N`, as an update rule. -/
abbrev rtUpd (N : ℕ) : UpdateRule ℕ := anchorUpdate (rtDag N) 8 rtConfig [1, 2, 4] (1 / 2)

/-! ## The synchronous slots are undecided -/

/-- A block of the round above votes for the leader's block only from validator `0` or the leader
itself. -/
theorem rt_voter_small {N r q : ℕ} (hq : q ∈ (rtDag N).ids)
    (hqr : ((rtDag N).block q).round = r + 1)
    (hv : MahiMahi.Votes (rtDag N) q (4 * r + r % 4)) : q % 4 = 0 ∨ q % 4 = r % 4 := by
  have hm := (MahiMahi.mem_candidatesAt.mp hv.1).2.2.2
  have hr : ((rtDag N).block (4 * r + r % 4)).round + 1 = ((rtDag N).block q).round := by
    change (4 * r + r % 4) / 4 + 1 = q / 4
    change q / 4 = r + 1 at hqr
    omega
  have href := mem_refs_of_mem_history_of_round_succ hq hm hr
  change 4 * r + r % 4 ∈ rtRefs q at href
  have hh := (Finset.mem_filter.mp href).2
  change q / 4 = r + 1 at hqr
  omega

/-- **No certificate for any known leader's block**: two voters never reach the quorum. -/
theorem rt_certificates_empty (N r : ℕ) :
    MahiMahi.certificates (rtDag N) 3 (4 * r + r % 4) r = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro C hc
  obtain ⟨hC, hCr, hcert⟩ := mem_certificatesAt.mp hc
  have hs : creatorsOf (rtDag N).block (MahiMahi.votesIn (rtDag N) C (4 * r + r % 4)) ⊆
      ({0, rtKnown r} : Finset (Fin 4)) := by
    intro a ha
    obtain ⟨q, hq, hqa⟩ := mem_creatorsOf.mp ha
    obtain ⟨hqC, hqv⟩ := mem_carriedVotes.mp hq
    have hqU := (rtDag N).complete C hC q hqC
    have hqr : ((rtDag N).block q).round = r + 1 := by
      have := (rtDag N).round_of_mem_refs hC hqC
      change C / 4 = r + 3 - 1 at hCr
      change q / 4 + 1 = C / 4 at this
      change q / 4 = r + 1
      omega
    have hv := rt_voter_small hqU hqr hqv
    have he : a = 0 ∨ a = rtKnown r := by
      rw [← hqa]
      exact hv.imp (fun h => Fin.ext h) (fun h => Fin.ext h)
    simpa using he
  have hb := Finset.card_le_card hs
  have hcard : ({0, rtKnown r} : Finset (Fin 4)).card ≤ 2 := by
    calc _ ≤ ({rtKnown r} : Finset (Fin 4)).card + 1 := Finset.card_insert_le _ _
         _ = 2 := by simp
  change 3 ≤ (creatorsOf (rtDag N).block (MahiMahi.votesIn (rtDag N) C (4 * r + r % 4))).card
    at hcert
  omega

/-- A block of validator `0` or of the leader at the round above holds the leader's block. -/
theorem rt_not_blames_small {N r q : ℕ} (hq : q ∈ (rtDag N).ids)
    (hqr : ((rtDag N).block q).round = r + 1) (ha : q % 4 = 0 ∨ q % 4 = r % 4) :
    ¬ MahiMahi.Blames (rtDag N) q (rtKnown r) r := by
  have href : 4 * r + r % 4 ∈ ((rtDag N).block q).refs := by
    change 4 * r + r % 4 ∈ rtRefs q
    change q / 4 = r + 1 at hqr
    simp only [rtRefs, growRefs, Finset.mem_filter, Finset.mem_Ico]
    exact ⟨by omega, by omega⟩
  have hm : 4 * r + r % 4 ∈ MahiMahi.candidatesAt (rtDag N) q (rtKnown r) r := by
    apply MahiMahi.mem_candidatesAt.mpr
    refine ⟨(rtDag N).complete q hq _ href, ?_, ?_, ?_⟩
    · change (4 * r + r % 4) / 4 = r
      omega
    · apply Fin.ext
      change (4 * r + r % 4) % 4 = r % 4
      omega
    · exact (mem_history_iff hq).mpr (Reaches.single href)
  intro hb
  exact Finset.notMem_empty _ (hb ▸ hm)

/-- **No synchronous slot is directly skipped**: two blamers never reach the quorum. -/
theorem rt_no_skip (N r : ℕ) (hr : r % 4 ≠ 0) (V : View (Fin 4) ℕ Unit (rtDag N)) :
    ¬ MahiMahi.DirectSkipIn (rtDag N) V 3 (rtKnown r) r := by
  intro hs
  unfold MahiMahi.DirectSkipIn HoldsAtLeast at hs
  have hsub : heldAuthors (rtDag N) V ((blocksAt (rtDag N) (MahiMahi.votingRound 3 r)).filter
      fun q => MahiMahi.Blames (rtDag N) q (rtKnown r) r) ⊆
      (Finset.univ.erase (0 : Fin 4)).erase (rtKnown r) := by
    intro a ha
    obtain ⟨q, hq, -, hqa⟩ := mem_heldAuthors.mp ha
    obtain ⟨hqb, hbl⟩ := Finset.mem_filter.mp hq
    obtain ⟨hqU, hqr⟩ := mem_blocksAt.mp hqb
    have hn : ¬ (q % 4 = 0 ∨ q % 4 = r % 4) := fun hsmall =>
      rt_not_blames_small hqU (by
        change q / 4 = r + 3 - 2 at hqr
        change q / 4 = r + 1
        omega) hsmall hbl
    have hav : (a : ℕ) = q % 4 := by
      rw [← hqa]
      rfl
    rw [Finset.mem_erase, Finset.mem_erase]
    refine ⟨fun h => hn (Or.inr ?_), fun h => hn (Or.inl ?_), Finset.mem_univ _⟩
    · have := congrArg Fin.val h
      change (a : ℕ) = r % 4 at this
      omega
    · have := congrArg Fin.val h
      change (a : ℕ) = 0 at this
      omega
  have hcard : ((Finset.univ.erase (0 : Fin 4)).erase (rtKnown r)).card = 2 := by
    rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr
        ⟨fun h => hr (congrArg Fin.val h), Finset.mem_univ _⟩),
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  have := Finset.card_le_card hsub
  change 3 ≤ _ at hs
  omega

/-- Every block of `rtDag N` lies at or below round `N`. -/
theorem rt_round_le {N b : ℕ} (hb : b ∈ (rtDag N).ids) : ((rtDag N).block b).round ≤ N := by
  change b ∈ Finset.range (4 * (N + 1)) at hb
  change b / 4 ≤ N
  rw [Finset.mem_range] at hb
  omega

/-- No block sits above round `N`, so no slot there is directly skipped in any view. -/
theorem rt_no_skip_above {N j : ℕ} (hj : N < j) (V : View (Fin 4) ℕ Unit (rtDag N))
    (a : Fin 4) : ¬ MahiMahi.DirectSkipIn (rtDag N) V 3 a j := by
  intro hs
  unfold MahiMahi.DirectSkipIn HoldsAtLeast at hs
  have hempty : (blocksAt (rtDag N) (MahiMahi.votingRound 3 j)).filter
      (fun q => MahiMahi.Blames (rtDag N) q a j) = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro q hq
    obtain ⟨hqU, hqr⟩ := mem_blocksAt.mp (Finset.mem_filter.mp hq).1
    have := rt_round_le hqU
    unfold MahiMahi.votingRound at hqr
    omega
  rw [hempty] at hs
  simp [heldAuthors, creatorsOf] at hs

/-- The known leader's candidate at a synchronous round is its block `4r + (r mod 4)`, on the
adaptive schedule whose period is `4` at every interval the record reaches. -/
theorem rt_known_candidate {N : ℕ} {coin : ℕ → Fin 4} {per : ℕ → ℕ}
    (hper : ∀ j, j ≤ intervalOf 8 N → per j = 4) {r L : ℕ} (hr : ¬ IsAsync 4 r)
    (hL : IsLeaderBlock (S := adaptiveSlots coin rtKnown 8 per) (rtDag N) r L) :
    L = 4 * r + r % 4 := by
  have hrN : r ≤ N := by
    have := rt_round_le hL.1
    have hround : ((rtDag N).block L).round = r := hL.2.1
    omega
  have hc := hL.2.2
  change ((rtDag N).block L).creator =
    (if IsAsync (per (intervalOf 8 r)) r then coin r else rtKnown r) at hc
  rw [hper (intervalOf 8 r) (Nat.div_le_div_right (by omega)), if_neg hr] at hc
  have hround : L / 4 = r := hL.2.1
  have hcv : L % 4 = r % 4 := congrArg Fin.val hc
  omega

/-- No synchronous candidate is certified, on the adaptive schedule at period `4`. -/
theorem rt_hcert (N : ℕ) (coin : ℕ → Fin 4) (per : ℕ → ℕ)
    (hper : ∀ j, j ≤ intervalOf 8 N → per j = 4) :
    ∀ (j : ℕ) (L : ℕ), ¬ IsAsync 4 j →
      IsLeaderBlock (S := adaptiveSlots coin rtKnown 8 per) (rtDag N) j L →
      MahiMahi.certificates (rtDag N) 3 L j = ∅ := by
  intro j L hj hL
  rw [rt_known_candidate hper hj hL]
  exact rt_certificates_empty N j

/-- No synchronous slot is directly skipped in any view, on the adaptive schedule at period `4`. -/
theorem rt_hskip (N : ℕ) (coin : ℕ → Fin 4) (V : View (Fin 4) ℕ Unit (rtDag N)) (per : ℕ → ℕ)
    (hper : ∀ j, j ≤ intervalOf 8 N → per j = 4) :
    ∀ j, ¬ IsAsync 4 j → ¬ MahiMahi.DirectSkipIn (rtDag N) V 3
      ((adaptiveSlots coin rtKnown 8 per).leader j) j := by
  intro j hj
  by_cases hjN : j ≤ N
  · change ¬ MahiMahi.DirectSkipIn (rtDag N) V 3
      (if IsAsync (per (intervalOf 8 j)) j then coin j else rtKnown j) j
    rw [hper (intervalOf 8 j) (Nat.div_le_div_right (by omega)), if_neg hj]
    exact rt_no_skip N j hj V
  · exact rt_no_skip_above (by omega) V _

/-! ## The stall, and the period -/

/-- **At period `4` slot `3` is never decided**, in any view, for any coin, on the adaptive
schedule whose period is `4` at every interval the record reaches: SH8 on `rtDag N`. -/
theorem rt_stall (N : ℕ) (coin : ℕ → Fin 4) (V : View (Fin 4) ℕ Unit (rtDag N)) (per : ℕ → ℕ)
    (hper : ∀ j, j ≤ intervalOf 8 N → per j = 4) (v : Option ℕ) :
    ¬ Decided (S := adaptiveSlots coin rtKnown 8 per) (periodic 3 5 4) (rtDag N) V 3 v :=
  fun h => Steelhead.stall (S := adaptiveSlots coin rtKnown 8 per) (by decide) (by decide)
    (fun _ => rfl) (rt_hcert N coin per hper) (rt_hskip N coin V per hper) (by decide) h

/-- **Algorithm 2 answers period `4` at every anchor** of `rtDag N`, at hysteresis `1/2` and
whatever the anchor block: the window of an anchor spans at most nine rounds, on which periods
`1` and `2` score at least half of what period `4` can. The scan leaves a stalled period through
its failover, not through the replay. -/
theorem rt_update_four (N A : ℕ) : rtUpd N A 4 = 4 :=
  anchorUpdate_half_retains (rtDag N) rtConfig rfl rfl rfl A

/-- **The adaptive output never decides slot `3`** at any period sequence that is `4` on the
intervals the record reaches, the replay's answer at every anchor and not the failover's: a
derivation for slot `3` reads no wavelength above the record's top round. -/
theorem rt_adaptive_stall (N : ℕ) (hN : 3 ≤ N) (coin : ℕ → Fin 4)
    (V : View (Fin 4) ℕ Unit (rtDag N)) (per : ℕ → ℕ)
    (hper : ∀ j, j ≤ intervalOf 8 N → per j = 4) (v : Option ℕ) :
    ¬ Decided (S := adaptiveSlots coin rtKnown 8 per) (adaptiveWave 3 5 8 per) (rtDag N) V 3 v := by
  intro h
  refine rt_stall N coin V per hper v
    (decided_congr (S := adaptiveSlots coin rtKnown 8 per) (w₂ := periodic 3 5 4) (N := N)
      (fun b hb => rt_round_le (V.subset_ids hb)) ?_ h hN)
  intro r hr
  unfold adaptiveWave
  rw [hper (intervalOf 8 r) (Nat.div_le_div_right (by omega))]

/-- **No settled prefix of the adaptive output has more than three slots.** -/
theorem rt_prefix_le_three (N : ℕ) (hN : 3 ≤ N) (coin : ℕ → Fin 4)
    (V : View (Fin 4) ℕ Unit (rtDag N)) (per : ℕ → ℕ)
    (hper : ∀ j, j ≤ intervalOf 8 N → per j = 4) (g : ℕ → Option ℕ) (n : ℕ)
    (hg : ∀ r, r < n → Decided (S := adaptiveSlots coin rtKnown 8 per) (adaptiveWave 3 5 8 per)
      (rtDag N) V r (g r)) :
    n ≤ 3 := by
  by_contra hn
  exact rt_adaptive_stall N hN coin V per hper (g 3) (hg 3 (by omega))

/-- **No block above round `2` is ever output**: the ledger of a settled prefix holds the
histories of committed leaders at slots `0` to `2`, whose rounds are at most `2`. -/
theorem rt_no_output_above_two (N : ℕ) (hN : 3 ≤ N) (coin : ℕ → Fin 4)
    (V : View (Fin 4) ℕ Unit (rtDag N)) (per : ℕ → ℕ)
    (hper : ∀ j, j ≤ intervalOf 8 N → per j = 4) (g : ℕ → Option ℕ) (n : ℕ)
    (hg : ∀ r, r < n →
      Decided (S := adaptiveSlots coin rtKnown 8 per) (adaptiveWave 3 5 8 per) (rtDag N) V r (g r))
    {b : ℕ} (hb : b ∈ ledgerSet (rtDag N) g n) : ((rtDag N).block b).round ≤ 2 := by
  obtain ⟨k, hk, L, hL, hr⟩ := hb
  have hn := rt_prefix_le_three N hN coin V per hper g n hg
  have hd := hg k (by omega)
  rw [hL] at hd
  have hlead := AnchoredRule.isLeaderBlock_of_decided (S := adaptiveSlots coin rtKnown 8 per) hd
  have hround : ((rtDag N).block L).round = k := hlead.2.1
  have := round_le_of_reaches hlead.1 hr
  omega

/-- Validator `1`'s round-`3` block, an honest one, exists at every horizon from `3`. -/
theorem rt_honest_block (N : ℕ) (hN : 3 ≤ N) :
    13 ∈ (rtDag N).ids ∧ ((rtDag N).block 13).round = 3 ∧
      ((rtDag N).block 13).creator ∈ (Correct : Finset (Fin 4)) := by
  refine ⟨?_, rfl, ?_⟩
  · change 13 ∈ Finset.range (4 * (N + 1))
    rw [Finset.mem_range]
    omega
  · change (1 : Fin 4) ∈ (Correct : Finset (Fin 4))
    decide

#print axioms rtDag
#print axioms rt_update_four
#print axioms rt_adaptive_stall
#print axioms rt_no_output_above_two

end LeanDagTest
