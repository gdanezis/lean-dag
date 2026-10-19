import LeanDag.Node.Boot.Statement
import LeanDag.Node.Helpers.Agree
/-!
# Bootstrap — proof

A certificate with `q` distinct signers lists an honest one, since
`f < q`, and an honest signer proposes a prefix of its own decisions
(`propose_prefix`), which `Certified` is.

Authentication and the hash at the end of the trace hold, so what the
honest nodes knew forms the run's record (`globalRecord`). By induction
over the trace every honest store is a cut of it and every decision a
verdict on a view of it (`IsCut.step`): a node bootstraps only at a
round with a block that `f + 1` distinct peers offered, one of them
honest, whose store held the block when it served it and was a cut of
the record then, so the record reaches the round; and the decisions it
takes from a certificate are an honest signer's, verdicts earlier in the
trace. Two verdicts on one slot agree (`AnchoredRule.decided_agree`),
and a node's decisions are slots `0, 1, …` (`Local.decisions`), so two
nodes' decisions are prefix-comparable (`prefix_of_slots`).
-/

namespace LeanDag

namespace Node

namespace Boot

theorem certified : Certified := by
  intro Validator BlockId Payload _ _ _ cfg H tr hadm hf hcert j v p c hj hv hq hnd
  obtain ⟨u, hu, huH⟩ := exists_mem_of_length hf hnd (by have := hadm.2.2.2.2.2; omega)
  obtain ⟨i, -, hiu, hprop⟩ := hcert j v p c hj hv u hu huH
  obtain ⟨inp', hi'⟩ := Converge.event_of_map hiu
  exact ⟨u, huH, (propose_prefix hi' hprop).trans (commits_prefix u (i + 1))⟩

theorem agrees : Agrees := by
  intro Validator BlockId Payload _ _ _ cfg H tr hσ hadm hf htime hoff hcert hinj
  -- authentication and the hash at the end of the trace
  have hinjR := hashInjective_of_trace hinj
  have hauthR := authentic_of_timely htime
  haveI : Validity.Quorate (ValidAt (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload) cfg.q Clause.none) cfg.q :=
    Validity.Quorate.of_validAt hadm.2.2.2.1 fun _ _ => Iff.rfl
  let U := globalRecord hinjR hauthR
  have ht : cfg.p.Tolerates H cfg.f cfg.q := ⟨hf, hadm.2.2.2.2.1, hadm.1⟩
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
          have hspan : ∀ s₂ ads,
              tryBoot (cfg.at w) (withInput (stateBefore cfg tr t w) inp) = some (s₂, ads) →
              Spans U s₂.store.base := by
            intro s₂ ads hbt
            obtain ⟨t₀, G₂, c₂, hb₂, -, -, hroot, -, hst, -⟩ := tryBoot_some hbt
            have hbase : s₂.store.base = G₂ := by
              rw [hst, flush_base]
              change ((keptBase (cfg.at w) (baseAt (cfg.at w) _ G₂)).foldl
                (fun st e => Node.accept (cfg.at w) st e.1 e.2)
                ((withInput (stateBefore cfg tr t w) inp).store.prune G₂ hb₂.le)).base = G₂
              rw [foldl_base]; rfl
            rw [hbase]
            obtain ⟨e, he, -⟩ := baseAt_of_bootRound hroot
            obtain ⟨-, hce⟩ := List.mem_filter.mp he
            simp only [decide_eq_true_eq] at hce
            obtain ⟨p', hp'l, hp'H⟩ := exists_mem_of_length hf (List.nodup_dedup _) hce.2.2
            obtain ⟨o, ho, rfl⟩ := List.mem_map.mp (List.mem_dedup.mp hp'l)
            obtain ⟨ho, hany⟩ := List.mem_filter.mp ho
            obtain ⟨x, hx, hxc⟩ := List.any_eq_true.mp hany
            simp only [decide_eq_true_eq] at hxc
            -- the offer was given before
            have hjo : ∃ j ≤ t, tr[j]? = some (w, .baseOffer o.1 o.2.1 o.2.2) := by
              rcases withInput_offered.1 o ho with ho | hinp
              · obtain ⟨j, hjt, hj'⟩ := offers_before (cfg := cfg) w t o ho
                exact ⟨j, hjt.le, hj'⟩
              · exact ⟨t, le_rfl, by rw [hj, hinp]⟩
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
          -- the decisions a certificate gives are an honest signer's
          have hcv : ∀ c ∈ (withInput (stateBefore cfg tr t w) inp).certs,
              (cfg.at w).q ≤ c.signers.length → c.signers.Nodup →
                ∀ e ∈ c.decisions, Verdict (cfg.at w) U e := by
            intro c hc hq hnd e he
            have hjc : ∃ j ≤ t, ∃ p, tr[j]? = some (w, .certOffer p c) := by
              rcases withInput_offered.2 c hc with hc | ⟨p, hinp⟩
              · obtain ⟨j, hjt, p, hj'⟩ := certs_before (cfg := cfg) w t c hc
                exact ⟨j, hjt.le, p, hj'⟩
              · exact ⟨t, le_rfl, p, by rw [hj, hinp]⟩
            obtain ⟨j, hjt, p, hj'⟩ := hjc
            obtain ⟨u, hu, huH⟩ := exists_mem_of_length hf hnd
              (by have := hadm.2.2.2.2.2; change cfg.q ≤ _ at hq; omega)
            obtain ⟨i, hij, hiu, hprop⟩ := hcert j w p c hj' hv u hu huH
            obtain ⟨inp', hi'⟩ := Converge.event_of_map hiu
            exact (ih (i + 1) (by omega) u huH).2 e ((propose_prefix hi' hprop).subset he)
          obtain ⟨hc', hv'⟩ := IsCut.step (cfg := cfg.at w) hg hσ ht inp hc hh
            (fun e he => hK w hv e (knownBefore_knownOf (hi.pend e he)))
            (fun o ho e he hid => hK w hv e (knownBefore_knownOf (hi.offered o ho e he hid)))
            (fun e he => hK w hv e (hd e he))
            (fun e he => hK w hv e (hb e he)) hcv hspan
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
  have hL : ∀ u,
      (decisionsOf cfg tr u).map Prod.fst = List.range (decisionsOf cfg tr u).length := by
    intro u
    obtain ⟨-, hfst, -⟩ := Local.decisions _ _ _ (cfg.at u) (inputsBefore tr tr.length u)
    have hlen := congrArg List.length hfst
    simp only [List.length_map, List.length_range] at hlen
    unfold decisionsOf runOf
    rw [hfst, hlen]
  intro v hv w hw
  refine prefix_of_slots (hL v) (hL w) fun k d d' hd hd' => ?_
  obtain ⟨V₁, h₁⟩ := (key tr.length v hv).2 _ hd
  obtain ⟨V₂, h₂⟩ := (key tr.length w hw).2 _ hd'
  letI := cfg.slots
  obtain ⟨-, -, -, hlaws⟩ := Scheme.coveredLaws (boundedSel (P := ValidAt cfg.q Clause.none)
    (honest := H) (Validator := Validator) (BlockId := BlockId) (Payload := Payload)) ht
  exact AnchoredRule.decided_agree hlaws trivial h₁ h₂

theorem holds : Statement := ⟨certified, agrees⟩

end Boot

end Node

end LeanDag
