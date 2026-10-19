import LeanDag.Node.Boot.Statement
import LeanDag.Node.Helpers.Agree
/-!
# Bootstrap — proof

Authentication and the hash at the end of the trace hold, so what the
honest nodes knew forms the run's record (`globalRecord`). By induction
over the trace every honest store is a cut of it and every decision a
verdict on a view of it (`IsCut.step`): a node bootstraps only at a
round with a block that `f + 1` distinct peers offered, one of them
honest, whose store held the block when it served it and was a cut of
the record then, so the record reaches the round. Two verdicts on one
slot agree (`AnchoredRule.decided_agree`).
-/

namespace LeanDag

namespace Node

namespace Boot

theorem agrees : Agrees := by
  intro Validator BlockId Payload _ _ _ cfg H tr hσ hadm hf htime hoff hinj
  -- authentication and the hash at the end of the trace
  have hinjR := hashInjective_of_trace hinj
  have hauthR := authentic_of_timely htime
  haveI : Validity.Quorate (ValidAt (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload) cfg.q Clause.none) cfg.q :=
    Validity.Quorate.of_validAt hadm.2.2.2.1 fun _ _ => Iff.rfl
  let U := globalRecord hinjR hauthR
  have ht : cfg.p.Tolerates H cfg.f cfg.q := ⟨hf, hadm.2.2.2.2, hadm.1⟩
  have hg := ground hinjR hauthR hadm.2.2.2.1
  have hK : ∀ v ∈ H, ∀ x ∈ knownOf cfg tr v, x ∈ knownAll cfg H tr :=
    fun v hv x hx => ⟨v, hv, hx⟩
  -- every honest store is a cut, and every decision a verdict
  have key : ∀ t, ∀ v ∈ H, IsCut U (stateBefore cfg tr t v).store ∧
      ∀ e ∈ commitsOf (run (cfg.at v) (State.init (cfg.at v)) (inputsBefore tr t v)).2,
        Verdict (cfg.at v) U e := by
    intro t
    induction t using Nat.strong_induction_on with
    | _ t ih =>
    intro v hv
    rcases t with _ | t
    · refine ⟨isCut_init hinjR hauthR (cfg.at v), fun e he => ?_⟩
      simp [inputsBefore, run, commitsOf] at he
    · rcases hj : tr[t]? with _ | ⟨w, inp⟩
      · have hL : tr.length ≤ t := List.getElem?_eq_none_iff.mp hj
        have h₁ : inputsBefore tr (t + 1) v = inputsBefore tr t v := by
          rw [inputsBefore_of_le (by omega), inputsBefore_of_le hL]
        have := ih t (by omega) v hv
        unfold stateBefore at this ⊢
        rw [h₁]
        exact this
      · by_cases hw : w = v
        · subst hw
          obtain ⟨hc, hv₀⟩ := ih t (by omega) w hv
          have hh : Held (cfg.at w) (stateBefore cfg tr t w) := Held.run _ Held.init
          have hi := Converge.inv_before (cfg := cfg) (tr := tr) t w
          obtain ⟨hd, hb⟩ := event_knownOf (cfg := cfg) hj
          -- a bootstrap is at a round the record reaches
          have hspan : ∀ p G bs s₂, inp = .baseOffer p G bs →
              tryBoot (cfg.at w) (withOffer (stateBefore cfg tr t w) p G bs) = some s₂ →
              Spans U s₂.store.base := by
            intro p G bs s₂ hinp hbt
            obtain ⟨t₀, G₂, hb₂, -, -, hroot, hst, -⟩ := tryBoot_some hbt
            have hbase : s₂.store.base = G₂ := by
              rw [hst, flush_base]
              change ((baseAt (cfg.at w) _ G₂).foldl (fun st e => Node.accept (cfg.at w) st e.1 e.2)
                ((withOffer (stateBefore cfg tr t w) p G bs).store.prune G₂ hb₂.le)).base = G₂
              rw [foldl_base]; rfl
            rw [hbase]
            have hmem := List.mem_filter.mp (List.max?_mem hroot)
            simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
              List.isEmpty_eq_false_iff] at hmem
            obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil _ hmem.2.2
            obtain ⟨-, hce⟩ := List.mem_filter.mp he
            simp only [decide_eq_true_eq] at hce
            obtain ⟨p', hp'l, hp'H⟩ := exists_mem_of_length hf (List.nodup_dedup _) hce.2.2
            obtain ⟨o, ho, rfl⟩ := List.mem_map.mp (List.mem_dedup.mp hp'l)
            obtain ⟨ho, hany⟩ := List.mem_filter.mp ho
            obtain ⟨x, hx, hxc⟩ := List.any_eq_true.mp hany
            simp only [decide_eq_true_eq] at hxc
            -- the offer was given before
            have hjo : ∃ j ≤ t, tr[j]? = some (w, .baseOffer o.1 o.2.1 o.2.2) := by
              rcases List.mem_cons.mp ho with rfl | ho
              · exact ⟨t, le_rfl, by rw [hj, hinp]⟩
              · obtain ⟨j, hjt, hj'⟩ := offers_before (cfg := cfg) w t o (List.mem_filter.mp ho).1
                exact ⟨j, hjt.le, hj'⟩
            obtain ⟨j, hjt, hj'⟩ := hjo
            obtain ⟨i, hij, hiv, hserve⟩ := hoff j w o.1 o.2.1 o.2.2 hj' hv hp'H
            obtain ⟨inp', hi'⟩ := Converge.event_of_map hiv
            rw [outputsAt_eq hi'] at hserve
            have hwin := serveBase_mem hserve
            rw [hwin] at hx
            obtain ⟨jid, hjid, rfl⟩ := List.mem_map.mp hx
            have hjid' : jid ∈ (stateBefore cfg tr i o.1).store.ids := (Finset.mem_sort _).mp hjid
            obtain ⟨hcut, -⟩ := ih i (by omega) o.1 hp'H
            obtain ⟨hU, hUb⟩ := hcut jid hjid'
            refine Or.inr ⟨jid, hU, ?_⟩
            have hr := congrArg Block.round hUb
            simp only [atBase_round, Store.blk, lookup] at hr
            rw [hr]
            exact hxc.2.ge
          obtain ⟨hc', hv'⟩ := IsCut.step (cfg := cfg.at w) hg hσ ht inp hc hh
            (fun e he => hK w hv e (knownBefore_knownOf (hi.pend e he)))
            (fun o ho e he hid => hK w hv e (knownBefore_knownOf (hi.offered o ho e he hid)))
            (fun e he => hK w hv e (hd e he))
            (fun e he => hK w hv e (hb e he)) hspan
          refine ⟨by rw [stateBefore_succ hj, if_pos rfl]; exact hc', fun e he => ?_⟩
          rw [inputsBefore_succ hj, if_pos rfl, run_append_single, commitsOf_append] at he
          rcases List.mem_append.mp he with he | he
          · exact hv₀ e he
          · exact hv' e he
        · have h₁ : inputsBefore tr (t + 1) v = inputsBefore tr t v := by
            rw [inputsBefore_succ hj, if_neg hw, List.append_nil]
          have := ih t (by omega) v hv
          unfold stateBefore at this ⊢
          rw [h₁]
          exact this
  intro v hv w hw k d d' hd hd'
  obtain ⟨V₁, h₁⟩ := (key tr.length v hv).2 _ hd
  obtain ⟨V₂, h₂⟩ := (key tr.length w hw).2 _ hd'
  letI := cfg.slots
  obtain ⟨-, -, -, hlaws⟩ := Scheme.coveredLaws (boundedSel (P := ValidAt cfg.q Clause.none)
    (honest := H) (Validator := Validator) (BlockId := BlockId) (Payload := Payload)) ht
  exact AnchoredRule.decided_agree hlaws trivial h₁ h₂

theorem holds : Statement := agrees

end Boot

end Node

end LeanDag
