import LeanDag.Node.Boot.Statement
import LeanDag.Node.Helpers.Agree
/-!
# Bootstrap — proof

A certificate with `q` distinct signers lists an honest one, since
`f < q`, and an honest signer proposes the head of the chain of its own
decisions at the height (`propose_head`), which `Certified` is.

Authentication and the hash at the end of the trace hold, so what the
honest nodes knew forms the run's record (`globalRecord`). By induction
over the trace every honest store is a cut of it and every decision a
verdict on a view of it (`IsCut.step`): the decisions a node takes from
a certificate are an honest signer's, verdicts earlier in the trace, the
chain's hash making the decisions served with it the signer's; and a
recovering node's horizon lies at or below the round of a slot it
decided, which a verdict's record reaches (`Verdict.spans`).
Two verdicts on one slot agree (`AnchoredRule.decided_agree`),
and a node's decisions are slots `0, 1, …` (`Local.decisions`), so two
nodes' decisions are prefix-comparable (`prefix_of_slots`).
-/

namespace LeanDag

namespace Node

namespace Boot

theorem certified : Certified := by
  intro Validator BlockId Payload _ _ _ cfg H tr hadm hf hcert j v p c ds hj hv hq hnd
  obtain ⟨u, hu, huH⟩ := exists_mem_of_length hf hnd (by have := hadm.2.2.2.2.2.1; omega)
  obtain ⟨i, -, hiu, hprop⟩ := hcert j v p c ds hj hv u hu huH
  obtain ⟨inp', hi'⟩ := Converge.event_of_map hiu
  obtain ⟨hk, hkh⟩ := propose_head hi' hprop
  have hpre := commits_prefix (cfg := cfg) (tr := tr) u (i + 1)
  exact ⟨u, huH, hk.trans hpre.length_le, by rw [take_of_prefix hpre hk]; exact hkh⟩

theorem agrees : Agrees := by
  intro Validator BlockId Payload _ _ _ cfg H tr hσ hadm hf htime hcert hinj hchain
  haveI : Validity.Quorate (ValidAt (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload) cfg.q Clause.none) cfg.q :=
    Validity.Quorate.of_validAt hadm.2.2.2.1 fun _ _ => Iff.rfl
  have ht : cfg.p.Tolerates H cfg.f cfg.q := ⟨hf, hadm.2.2.2.2.1, hadm.1⟩
  have key := cut_before hσ hadm hf htime hcert hinj hchain
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
