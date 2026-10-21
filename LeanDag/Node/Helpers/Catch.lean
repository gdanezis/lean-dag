import LeanDag.Node.Helpers.Hold
import LeanDag.Node.Helpers.Reliable
/-!
# A reliable node's certificate catches up

`docs/validator.md` §13.8. A reliable node given a good certificate above
its own, at a height it decided, confirms it (`confirms_of`); at a height
it did not decide, it asks the sender, which serves its certificate with
the decisions above the asked slot (`serveFrom_eq`), and adopts them if
they agree with its own (`adoptable_of`). Along a trace, a reliable
node's certificate reaches the height of one a reliable peer announces
within `3Δ` past GST (`cert_catches`).
-/

namespace LeanDag

namespace Node

variable {Validator BlockId Payload : Type} [Fintype Validator] [DecidableEq Validator]
variable [LinearOrder BlockId]
variable {cfg : Config Validator BlockId Payload}

omit [Fintype Validator] in
/-- The chain extended by the decisions since the height last proposed and
more is the head of the decisions with them. -/
theorem chain_extend {s : State Validator BlockId Payload} (hL : Ledger cfg s)
    (ds : List (ℕ × Option BlockId)) :
    ((s.decided.take (s.lo - s.lastProposed)).reverse ++ ds).foldl cfg.extend s.chain =
      cfg.headOf (s.decided.reverse ++ ds) := by
  have hlen : s.decided.reverse.length = s.lo := by rw [List.length_reverse]; exact hL.length
  have hcs := chain_step (cfg := cfg) (D := s.decided.reverse) hL.2.1 (le_of_eq hlen.symm)
  have hX : ((s.decided.take (s.lo - s.lastProposed)).reverse).take (s.lo - s.lastProposed) =
      (s.decided.take (s.lo - s.lastProposed)).reverse :=
    List.take_of_length_le (by simp)
  rw [List.reverse_reverse, hlen, hX, ← hL.2.2, List.take_of_length_le (le_of_eq hlen)] at hcs
  rw [List.foldl_append, hcs, Config.headOf, Config.headOf, List.foldl_append]

omit [Fintype Validator] in
/-- **A node confirms a good certificate** above its own at a height it
decided, with the head of its decisions there. -/
theorem confirms_of {s : State Validator BlockId Payload} {c : Cert Validator BlockId}
    (hq : cfg.q ≤ c.signers.length) (hnd : c.signers.Nodup) (hm : cfg.m ∣ c.height)
    (hlt : s.certHeight < c.height) (hle : c.height ≤ s.lo)
    (hh : c.head = cfg.headOf (s.decided.reverse.take c.height)) : confirms cfg s c = true := by
  unfold confirms
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨hq, hnd⟩, hlt⟩, hle⟩, hm⟩, hh⟩

omit [Fintype Validator] in
/-- **A node adopts decisions** served with a certificate of `q` distinct
signers at a multiple of `m` above its next undecided slot, the slots from
there to its height, whose chain from its own has the certificate's head. -/
theorem adoptable_of {s : State Validator BlockId Payload} (hL : Ledger cfg s)
    {c : Cert Validator BlockId} {ds : List (ℕ × Option BlockId)}
    (hq : cfg.q ≤ c.signers.length) (hnd : c.signers.Nodup) (hm : cfg.m ∣ c.height)
    (hlt : s.lo < c.height) (hds : ds.map Prod.fst = List.range' s.lo (c.height - s.lo))
    (hh : cfg.headOf (s.decided.reverse ++ ds) = c.head) : adoptable cfg s c ds = true := by
  unfold adoptable
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨⟨hq, hnd⟩, hlt, hm⟩, hds⟩, by rw [chain_extend hL]; exact hh⟩

omit [Fintype Validator] in
/-- **What a node serves** asked from slot `lo` below its certificate's
height: the certificate, with its decisions from `lo` to the height. -/
theorem serveFrom_eq {s : State Validator BlockId Payload} (hL : Ledger cfg s) {peer : Validator}
    {lo : ℕ} {c : Cert Validator BlockId} (hc : s.cert = some c) (hlo : lo < c.height)
    (hle : c.height ≤ s.lo) :
    serveFrom s peer lo = [.serveCert peer c ((s.decided.reverse.take c.height).drop lo)] := by
  have hlen : s.decided.length = s.lo := hL.length
  unfold serveFrom
  rw [hc]
  dsimp only
  rw [if_pos ⟨hlo, hle⟩, List.take_reverse, List.drop_reverse, hlen]
  congr 3
  rw [List.length_drop, hlen]
  congr 1
  omega

omit [Fintype Validator] [DecidableEq Validator] [LinearOrder BlockId] in
/-- Of decisions of the slots from `a` on, those from `b` on are the
first `b − a` dropped. -/
theorem filter_from {α : Type} : ∀ (L : List (ℕ × α)) (a n b : ℕ),
    L.map Prod.fst = List.range' a n → L.filter (fun e => decide (b ≤ e.1)) = L.drop (b - a)
  | [], _, _, _, _ => by simp
  | x :: L, a, n, b, h => by
    cases n with
    | zero => simp at h
    | succ n =>
      rw [List.map_cons, List.range'_succ, List.cons.injEq] at h
      by_cases hb : b ≤ a
      · rw [show b - a = 0 by omega, List.drop_zero, List.filter_eq_self]
        intro e he
        have : e.1 ∈ List.range' a (n + 1) := by
          rw [List.range'_succ, ← h.2, ← h.1]
          rcases List.mem_cons.mp he with rfl | he
          · exact List.mem_cons_self ..
          · exact List.mem_cons_of_mem _ (List.mem_map_of_mem he)
        simp only [List.mem_range'] at this
        simp only [decide_eq_true_eq]; omega
      · rw [List.filter_cons_of_neg (by simp [h.1]; omega), filter_from L (a + 1) n b h.2,
          show b - a = (b - (a + 1)) + 1 by omega, List.drop_succ_cons]

omit [Fintype Validator] [DecidableEq Validator] [LinearOrder BlockId] in
theorem slots_take_drop {α : Type} {D : List (ℕ × α)} {L : ℕ} (hD : D.map Prod.fst = List.range L)
    {a h : ℕ} (hh : h ≤ L) (ha : a ≤ h) :
    ((D.take h).drop a).map Prod.fst = List.range' a (h - a) := by
  rw [List.map_drop, List.map_take, hD, List.take_range, List.range_eq_range', List.drop_range']
  congr 1 <;> omega

omit [Fintype Validator] [DecidableEq Validator] [LinearOrder BlockId] in
/-- Of two prefix-comparable lists, the first `k` agree, for `k` at most
both lengths. -/
theorem take_eq_of_comparable {α : Type} {l₁ l₂ : List α} (h : l₁ <+: l₂ ∨ l₂ <+: l₁) {k : ℕ}
    (h₁ : k ≤ l₁.length) (h₂ : k ≤ l₂.length) : l₁.take k = l₂.take k := by
  rcases h with ⟨t, rfl⟩ | ⟨t, rfl⟩
  · rw [List.take_append_of_le_length h₁]
  · rw [List.take_append_of_le_length h₂]

omit [Fintype Validator] in
/-- **A good certificate's head** is the head of the decisions of any
state whose decisions are comparable and reach its height. -/
theorem GoodFor.head_at {P : List (Validator × ℕ × BlockId)} {c : Cert Validator BlockId}
    {X Y : State Validator BlockId Payload} (h : GoodFor cfg c X) (hK : Kept cfg P X)
    (hcmp : X.decided.reverse <+: Y.decided.reverse ∨ Y.decided.reverse <+: X.decided.reverse)
    (hle : c.height ≤ Y.decided.reverse.length) :
    c.head = cfg.headOf (Y.decided.reverse.take c.height) := by
  have hX : c.height ≤ X.decided.reverse.length := by
    rw [List.length_reverse, hK.ledger.length]; exact h.2.2.2.1.trans hK.certHeight_le
  rw [h.2.2.2.2, take_eq_of_comparable hcmp hX hle]

theorem confirm_certHeight {s : State Validator BlockId Payload} (hs : s.recovering = false)
    (c : Cert Validator BlockId) : c.height ≤ (Node.confirm cfg s c).1.certHeight := by
  unfold Node.confirm
  have := (rises_settle (cfg := cfg)
    (s := { s with cert := some c, props := Node.above (some c) s.props }) hs).2.2.2
  simpa [State.certHeight] using this

theorem adopt_certHeight {s : State Validator BlockId Payload} (hs : s.recovering = false)
    {c : Cert Validator BlockId} {ds : List (ℕ × Option BlockId)} (hlt : s.certHeight < c.height) :
    c.height ≤ (Node.adopt cfg s c ds).1.certHeight := by
  rw [adopt_eq]
  change c.height ≤ (Node.settle cfg (adopted s c ds)).1.certHeight
  have := (rises_settle (cfg := cfg) (s := adopted s c ds) hs).2.2.2
  unfold State.certHeight at hlt
  simp only [adopted, State.certHeight, if_pos hlt] at this ⊢
  simpa using this

/-! ## Along a trace -/

variable {tr : Trace Validator BlockId Payload} {H : Finset Validator}

/-- **Two honest nodes' decisions are prefix-comparable**, before any
events, under the assumptions of agreement. -/
theorem decided_comparable (hσ : cfg.σ = boundedSel) (hadm : cfg.Admissible)
    (hf : Hᶜ.card ≤ cfg.f) (htime : Converge.TimelyAuthentic cfg H tr)
    (hoff : Boot.TimelyOffers cfg H tr) (hcert : Boot.TimelyCerts cfg H tr)
    (hinj : Converge.HashInjective cfg H tr) (hchain : Boot.ChainInjective cfg H tr)
    {u v : Validator} (hu : u ∈ H) (hv : v ∈ H) (i j : ℕ) :
    (stateBefore cfg tr i u).decided.reverse <+: (stateBefore cfg tr j v).decided.reverse ∨
      (stateBefore cfg tr j v).decided.reverse <+: (stateBefore cfg tr i u).decided.reverse := by
  haveI : Validity.Quorate (ValidAt (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload) cfg.q Clause.none) cfg.q :=
    Validity.Quorate.of_validAt hadm.2.2.2.1 fun _ _ => Iff.rfl
  have ht : cfg.p.Tolerates H cfg.f cfg.q := ⟨hf, hadm.2.2.2.2.1, hadm.1⟩
  have key := cut_before hσ hadm hf htime hoff hcert hinj hchain
  have hD : ∀ w t, (stateBefore cfg tr t w).decided.reverse =
      commitsOf (run (cfg.at w) (State.init (cfg.at w)) (inputsBefore tr t w)).2 :=
    fun w t => (Local.decisions _ _ _ (cfg.at w) (inputsBefore tr t w)).1
  have hL : ∀ w t, (commitsOf (run (cfg.at w) (State.init (cfg.at w))
      (inputsBefore tr t w)).2).map Prod.fst = List.range (commitsOf (run (cfg.at w)
        (State.init (cfg.at w)) (inputsBefore tr t w)).2).length := by
    intro w t
    obtain ⟨-, hfst, -⟩ := Local.decisions _ _ _ (cfg.at w) (inputsBefore tr t w)
    have hlen := congrArg List.length hfst
    simp only [List.length_map, List.length_range] at hlen
    rw [hfst, hlen]
  rw [hD, hD]
  refine prefix_of_slots (hL u i) (hL v j) fun k d d' hd hd' => ?_
  obtain ⟨V₁, h₁⟩ := (key i u hu).2 _ hd
  obtain ⟨V₂, h₂⟩ := (key j v hv).2 _ hd'
  letI := cfg.slots
  obtain ⟨-, -, -, hlaws⟩ := Scheme.coveredLaws (boundedSel (P := ValidAt cfg.q Clause.none)
    (honest := H) (Validator := Validator) (BlockId := BlockId) (Payload := Payload)) ht
  exact AnchoredRule.decided_agree hlaws trivial h₁ h₂

/-- **A reliable node keeps what it keeps** before every event. -/
theorem kept_before {v : Validator} (hnr : ∀ i : ℕ, tr[i]? ≠ some (v, Input.restart)) (i : ℕ) :
    Kept (cfg.at v) [] (stateBefore cfg tr i v) ∧ Covered (cfg.at v) (stateBefore cfg tr i v) :=
  inv_before (cfg := cfg) hnr (fun s => Kept (cfg.at v) [] s ∧ Covered (cfg.at v) s)
    ⟨Kept.init, Covered.init⟩ (fun _ _ h hs hr =>
      have h' := h.1.step h.2 (by simp) hs hr (by simp); ⟨h'.1, h'.2.1⟩) i

/-- **A certificate a reliable node announces** is good for its state
after the event. -/
theorem announce_good {u : Validator} (hnr : ∀ i : ℕ, tr[i]? ≠ some (u, Input.restart)) {e : ℕ}
    {inp : Input Validator BlockId Payload} (he : tr[e]? = some (u, inp))
    {c : Cert Validator BlockId} (hc : Output.announce c ∈ outputsAt cfg tr e) :
    GoodFor (cfg.at u) c (stateBefore cfg tr (e + 1) u) := by
  rw [outputsAt_eq he] at hc
  rw [stateBefore_succ he, if_pos rfl]
  have hk := kept_before (cfg := cfg) hnr e
  exact (hk.1.step hk.2 (by simp) (fired_before (cfg := cfg) hnr e).1
    (fun h => hnr e (by rw [he, h])) (by simp)).2.2 c hc

variable {time : ℕ → ℕ} {gst Δ t₁ : ℕ}

/-- **A reliable node's certificate catches up** with a certificate a
reliable peer announces, within `3Δ` past GST: it confirms it, or asks
the peer for the decisions it certifies and adopts or confirms what the
peer serves. -/
theorem cert_catches {T : Finset Validator}
    (hcmp : ∀ u ∈ T, ∀ v ∈ T, ∀ i j, (stateBefore cfg tr i u).decided.reverse <+:
      (stateBefore cfg tr j v).decided.reverse ∨
        (stateBefore cfg tr j v).decided.reverse <+: (stateBefore cfg tr i u).decided.reverse)
    (hnr : Converge.NoRestart T tr) (hdel : Live.DeliveredWithin cfg T tr time gst Δ t₁)
    {u v : Validator} (hu : u ∈ T) (hv : v ∈ T) (huv : u ≠ v) {e : ℕ}
    {inp : Input Validator BlockId Payload} (he : tr[e]? = some (u, inp))
    {c : Cert Validator BlockId} (hc : Output.announce c ∈ outputsAt cfg tr e)
    (ht : max (time e) gst + 3 * Δ ≤ t₁) :
    ∃ l, e < l ∧ (tr[l]?.map Prod.fst) = some v ∧ time l ≤ max (time e) gst + 3 * Δ ∧
      c.height ≤ (stateBefore cfg tr (l + 1) v).certHeight := by
  have hnu : ∀ i : ℕ, tr[i]? ≠ some (u, Input.restart) := fun i => hnr i u hu
  have hnv : ∀ i : ℕ, tr[i]? ≠ some (v, Input.restart) := fun i => hnr i v hv
  obtain ⟨hq, hnd, hm, -, -⟩ := announce_good (cfg := cfg) hnu he hc
  have hgood := announce_good (cfg := cfg) hnu he hc
  -- the announcement arrives
  obtain ⟨j, hej, hj, htj⟩ := hdel e u inp he hu (v, .announced u c)
    ⟨.announce c, hc, Ne.symm huv, rfl⟩ hv (by omega)
  have hrj := (fired_before (cfg := cfg) hnv j).1
  have hsj : stateBefore cfg tr (j + 1) v =
      (Node.step (cfg.at v) (stateBefore cfg tr j v) (.announced u c)).1 := by
    rw [stateBefore_succ hj, if_pos rfl]
  have hlj : (tr[j]?.map Prod.fst) = some v := by rw [hj]; rfl
  by_cases hge : c.height ≤ (stateBefore cfg tr j v).certHeight
  · exact ⟨j, hej, hlj, by omega,
      hge.trans (rises_before (cfg := cfg) hnv (Nat.le_succ j)).2.2.2⟩
  have hlt := not_le.mp hge
  obtain ⟨hKj, hcovj⟩ := kept_before (cfg := cfg) hnv j
  have hKe := (kept_before (cfg := cfg) hnu (e + 1)).1
  have hst : Node.step (cfg.at v) (stateBefore cfg tr j v) (.announced u c) =
      if confirms (cfg.at v) (stateBefore cfg tr j v) c then
        Node.confirm (cfg.at v) (stateBefore cfg tr j v) c
      else if cfg.q ≤ c.signers.length ∧ (stateBefore cfg tr j v).lo < c.height then
        (stateBefore cfg tr j v, [.requestDecisions u (stateBefore cfg tr j v).lo])
      else (stateBefore cfg tr j v, []) := by
    rw [step_announced, if_neg (show u ≠ (cfg.at v).me from huv)]
    rfl
  by_cases hle : c.height ≤ (stateBefore cfg tr j v).lo
  · -- the node decided the certificate's height: it confirms
    have hcf := confirms_of (cfg := cfg.at v) hq hnd hm hlt hle
      (hgood.head_at hKe (hcmp u hu v hv _ _) (by
        rw [List.length_reverse, hKj.ledger.length]; exact hle))
    refine ⟨j, hej, hlj, by omega, ?_⟩
    rw [hsj, hst, if_pos hcf]
    exact confirm_certHeight hrj c
  have hlo := not_le.mp hle
  have hncf : confirms (cfg.at v) (stateBefore cfg tr j v) c = false := by
    unfold confirms
    simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]
    exact Or.inl (Or.inl (Or.inr (by omega)))
  -- it asks the peer for the decisions from its next undecided slot
  have hout : outputsAt cfg tr j = [.requestDecisions u (stateBefore cfg tr j v).lo] := by
    rw [outputsAt_eq hj, hst, if_neg (by simp [hncf]), if_pos ⟨hq, hlo⟩]
  set lo := (stateBefore cfg tr j v).lo with hlo_def
  obtain ⟨k, hjk, hk, htk⟩ := hdel j v _ hj hv (u, .decisionRequest v lo)
    ⟨.requestDecisions u lo, by rw [hout]; exact List.mem_singleton_self _, rfl, rfl⟩ hu
    (by show max (time j) gst + Δ ≤ t₁; omega)
  -- the peer serves its certificate, at or above the one it announced
  obtain ⟨hKk, -⟩ := kept_before (cfg := cfg) hnu k
  have hck : c.height ≤ (stateBefore cfg tr k u).certHeight :=
    hgood.2.2.2.1.trans (rises_before (cfg := cfg) hnu (by omega : e + 1 ≤ k)).2.2.2
  obtain ⟨c', hc'⟩ : ∃ c', (stateBefore cfg tr k u).cert = some c' := by
    rcases h : (stateBefore cfg tr k u).cert with _ | c'
    · simp [State.certHeight, h] at hck; omega
    · exact ⟨c', rfl⟩
  have hcc' : c.height ≤ c'.height := by simpa [State.certHeight, hc'] using hck
  obtain ⟨hq', hnd', hle', hhd', hm'⟩ := hKk.cert c' hc'
  have hserve := serveFrom_eq (cfg := cfg.at u) hKk.ledger (peer := v) (lo := lo) hc'
    (by omega) hle'
  set ds := ((stateBefore cfg tr k u).decided.reverse.take c'.height).drop lo with hds_def
  have houtk : outputsAt cfg tr k = [.serveCert v c' ds] := by
    rw [outputsAt_eq hk]
    change (if v ≠ (cfg.at u).me then serveFrom (stateBefore cfg tr k u) v lo else []) = _
    rw [if_pos (show v ≠ (cfg.at u).me from Ne.symm huv), hserve]
  obtain ⟨l, hkl, hl, htl⟩ := hdel k u _ hk hu (v, .certOffer u c' ds)
    ⟨.serveCert v c' ds, by rw [houtk]; exact List.mem_singleton_self _, rfl, rfl⟩ hv
    (by omega)
  have hll : (tr[l]?.map Prod.fst) = some v := by rw [hl]; rfl
  refine ⟨l, by omega, hll, by omega, ?_⟩
  -- the node takes the served certificate
  have hrl := (fired_before (cfg := cfg) hnv l).1
  have hsl : stateBefore cfg tr (l + 1) v =
      (Node.step (cfg.at v) (stateBefore cfg tr l v) (.certOffer u c' ds)).1 := by
    rw [stateBefore_succ hl, if_pos rfl]
  by_cases hge' : c'.height ≤ (stateBefore cfg tr l v).certHeight
  · exact hcc'.trans (hge'.trans (rises_before (cfg := cfg) hnv (Nat.le_succ l)).2.2.2)
  have hlt' := not_le.mp hge'
  refine hcc'.trans ?_
  obtain ⟨hKl, hcovl⟩ := kept_before (cfg := cfg) hnv l
  have hlol : lo ≤ (stateBefore cfg tr l v).lo :=
    (rises_before (cfg := cfg) hnv (by omega : j ≤ l)).2.2.1
  have hcmpl := hcmp u hu v hv k l
  have hlenk : (stateBefore cfg tr k u).decided.reverse.length = (stateBefore cfg tr k u).lo := by
    rw [List.length_reverse, hKk.ledger.length]
  rw [hsl, step_certOffer, if_neg (by simp [hrl]), certState_of hrl]
  by_cases hlo' : (stateBefore cfg tr l v).lo < c'.height
  · -- below the height: it adopts the decisions served
    have hsl' := slots_take_drop hKk.ledger.1 hle' (by omega : lo ≤ c'.height)
    have hf := filter_from ds lo (c'.height - lo) (stateBefore cfg tr l v).lo hsl'
    have hds' : (ds.filter fun e => decide ((stateBefore cfg tr l v).lo ≤ e.1)) =
        ((stateBefore cfg tr k u).decided.reverse.take c'.height).drop
          (stateBefore cfg tr l v).lo := by
      rw [hf, hds_def, List.drop_drop]; congr 1; omega
    have hlenl : (stateBefore cfg tr l v).decided.reverse.length = (stateBefore cfg tr l v).lo := by
      rw [List.length_reverse, hKl.ledger.length]
    have hpre : (stateBefore cfg tr l v).decided.reverse =
        ((stateBefore cfg tr k u).decided.reverse.take c'.height).take
          (stateBefore cfg tr l v).lo := by
      rw [List.take_take, min_eq_left hlo'.le,
        take_eq_of_comparable hcmpl (k := (stateBefore cfg tr l v).lo) (by omega) (by omega),
        ← hlenl, List.take_length]
    have ha : adoptable (cfg.at v) (stateBefore cfg tr l v) c'
        (ds.filter fun e => decide ((stateBefore cfg tr l v).lo ≤ e.1)) = true := by
      refine adoptable_of hKl.ledger hq' hnd' hm' hlo' ?_ ?_
      · rw [hds']
        exact slots_take_drop hKk.ledger.1 hle' hlo'.le
      · rw [hds', hpre, List.take_append_drop, hhd']; rfl
    rw [if_pos ⟨huv, ha⟩]
    exact adopt_certHeight hrl hlt'
  · -- at or above the height: it confirms
    have hle'' := not_lt.mp hlo'
    have hna : adoptable (cfg.at v) (stateBefore cfg tr l v) c'
        (ds.filter fun e => decide ((stateBefore cfg tr l v).lo ≤ e.1)) = false := by
      by_contra h
      have := adoptable_lo (Bool.not_eq_false _ ▸ h)
      omega
    have hcf := confirms_of (cfg := cfg.at v) hq' hnd' hm' hlt' hle''
      (by
        rw [hhd', take_eq_of_comparable hcmpl (by omega) (by
          rw [List.length_reverse, hKl.ledger.length]; exact hle'')]; rfl)
    rw [if_neg (by simp [hna]), if_pos ⟨huv, hcf⟩]
    exact confirm_certHeight hrl c'

end Node

end LeanDag
