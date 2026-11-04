import LeanDag.Node.Helpers.Base
import LeanDag.Node.Helpers.Wait
import LeanDag.Node.Helpers.SyncInv
import LeanDag.Node.Live.Statement
/-!
# A reliable node's builds along a trace

`docs/validator.md` §5.3. Over a stretch of a trace on which a record is a
base (`Base`), each block a reliable node builds at an event comes from one
build, at a state whose disk is read as the record reads it from the base's
round up, grown from the disk before the event (`build_witness`). A block
of the record above that round by a reliable node was built at the node's
first event persisting a block of its round (`builtAt_first`,
`built_block`).
-/

namespace LeanDag

namespace Node

variable {Validator BlockId Payload : Type} [Fintype Validator] [DecidableEq Validator]
variable [LinearOrder BlockId]
variable {cfg : Config Validator BlockId Payload} {tr : Trace Validator BlockId Payload}
variable {H : Finset Validator}

/-- **Each block a reliable node builds at an event before a base's end
comes from one build**, at a state whose disk is read as the base's record
reads it, and keeps the disk before the event from its floor up. -/
theorem build_witness {R : BlockRecord Validator BlockId Payload (ValidAt cfg.q Clause.none) H}
    {B E₀ E₁ : ℕ} (hbase : Base cfg H tr R B E₀ E₁) {v : Validator} (hv : v ∈ H) {i : ℕ}
    {inp : Input Validator BlockId Payload} (hi : tr[i]? = some (v, inp)) (h₁ : i + 1 ≤ E₁)
    {e : BlockId × Block Validator BlockId Payload}
    (he : e ∈ persists (outputsAt cfg tr i)) (hr : e.2.round ≠ 0) :
    ∃ x y o, BuildState (cfg.at v) R B (knownAll cfg H tr) (stateBefore cfg tr i v) inp x ∧
      tryBuild (cfg.at v) x = some (y, o) ∧ e ∈ persists o ∧
      DiskRises (cfg.at v) x (stateBefore cfg tr (i + 1) v) := by
  have hK : ∀ x ∈ knownOf cfg tr v, x ∈ knownAll cfg H tr := fun x hx => ⟨v, hv, hx⟩
  have hinv := Converge.inv_before (cfg := cfg) (tr := tr) i v
  obtain ⟨hd, hb⟩ := event_knownOf (cfg := cfg) hi
  obtain ⟨hcut, -, -⟩ := hbase.disk v hv i (by omega)
  have hfin := (hbase.disk v hv (i + 1) h₁).2.2
  rw [Converge.step_before hi] at hfin
  rw [outputsAt_eq hi] at he
  rcases step_witness (cfg := cfg.at v) ⟨hbase.grounds v hv, hbase.known⟩
      (hinv.mono fun x hx => hK x (knownBefore_knownOf hx)) hcut
      (ownTop_before (cfg := cfg) i)
      (fun hfa => Converge.kept_before (cfg := cfg) (tr := tr) hfa v i)
      (fun x hx => hK _ (knownBefore_knownOf (hinv.pend x hx)))
      (fun x hx => hK x (hd x hx)) (fun x hx => hK x (hb x hx)) hfin e he with h | h
  · exact absurd h hr
  · rw [stateBefore_succ hi, if_pos rfl]; exact h

omit [Fintype Validator] [DecidableEq Validator] [LinearOrder BlockId] in
/-- A pair is persisted by outputs exactly when its `persist` output is among them. -/
theorem mem_persists_iff {out : List (Output Validator BlockId Payload)}
    {x : BlockId × Block Validator BlockId Payload} :
    x ∈ persists out ↔ Output.persist x.1 x.2 ∈ out := by
  unfold persists
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨o, ho, h⟩
    cases o <;> simp only [reduceCtorEq, Option.some.injEq] at h
    rw [← h]; exact ho
  · intro h; exact ⟨_, h, rfl⟩

variable (time : ℕ → ℕ) {t₁ : ℕ}

/-- **When `v` built its round-`n` block**: at the first of `v`'s events
persisting a round-`n` block, if one persists any. -/
theorem builtAt_first {v : Validator} {n i : ℕ}
    (hi : (tr[i]?.map Prod.fst) = some v)
    (he : ∃ e ∈ persists (outputsAt cfg tr i), e.2.round = n) :
    ∃ i₀ ≤ i, builtAt cfg tr time v n = time i₀ ∧ (tr[i₀]?.map Prod.fst) = some v ∧
      ∃ e ∈ persists (outputsAt cfg tr i₀), e.2.round = n := by
  have hlt : i < tr.length := by
    rcases h : tr[i]? with _ | x
    · rw [h] at hi; cases hi
    · exact (List.getElem?_eq_some_iff.mp h).1
  let p : ℕ → Bool := fun i => decide ((tr[i]?.map Prod.fst) = some v) &&
    (persists (outputsAt cfg tr i)).any (fun e => decide (e.2.round = n))
  have hp : p i = true := by
    obtain ⟨e, he, her⟩ := he
    simp only [p, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true]
    exact ⟨hi, e, he, by simp [her]⟩
  obtain ⟨i₀, hfind⟩ : ∃ i₀, (List.range tr.length).find? p = some i₀ := by
    rcases h : (List.range tr.length).find? p with _ | i₀
    · exact absurd (List.find?_isSome.mpr ⟨i, List.mem_range.mpr hlt, hp⟩) (by rw [h]; simp)
    · exact ⟨i₀, rfl⟩
  obtain ⟨hp₀, -, hmin⟩ := List.find?_range_eq_some.mp hfind
  have hle : i₀ ≤ i := by
    by_contra h
    have := hmin i (by omega)
    rw [hp] at this
    cases this
  refine ⟨i₀, hle, ?_, ?_⟩
  · unfold builtAt
    rw [hfind]
  · simp only [p, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true] at hp₀
    obtain ⟨hv₀, e, he, her⟩ := hp₀
    exact ⟨hv₀, e, he, by simpa using her⟩

/-- **A reliable node's block in the run's record was built at `v`'s
first event building its round**, from a state it builds from, whose
disk grows into the disk after the event, by the build rule: its
references are `refsAt`'s on that state's disk, held there, and pass
the reach and certificate tests, or follow the round's timer with
`refsFor`'s, or follow the node's being behind with `refsFor`'s, when, at a
node that drops, it built no block of the round before `E₀`. -/
theorem built_block (hσ : cfg.σ = boundedSel)
    (htime : Converge.TimelyAuthentic cfg H tr) (hinj : Converge.HashInjective cfg H tr)
    {R : BlockRecord Validator BlockId Payload (ValidAt cfg.q Clause.none) H} {B E₀ E₁ : ℕ}
    (hbase : Base cfg H tr R B E₀ E₁) {v : Validator} (hv : v ∈ H) {c : BlockId} {r : ℕ}
    (hcU : c ∈ R.ids) (hcv : (R.block c).creator = v) (hcr : (R.block c).round = r + 1)
    (hrB : B ≤ r) (hrV : cfg.drops = true → B + 1 + cfg.p.voteOffset ≤ r)
    (hwin : ∃ j, j + 1 ≤ E₁ ∧ (tr[j]?.map Prod.fst) = some v ∧
      ∃ e ∈ persists (outputsAt cfg tr j), e.2.round = r + 1)
    (hE₀ : cfg.drops = true → ∀ k < E₀, (tr[k]?.map Prod.fst) = some v →
      ∀ e ∈ persists (outputsAt cfg tr k), e.2.round ≠ r + 1) :
    ∃ i₀ inp x ow, tr[i₀]? = some (v, inp) ∧ builtAt cfg tr time v (r + 1) = time i₀ ∧
      BuildState (cfg.at v) R B (knownAll cfg H tr) (stateBefore cfg tr i₀ v) inp x ∧
        (x.top.isSome ∧ x.top.getD 0 ≤ r ∧
          ((x.top = some r ∧ ow = x.own) ∨
            ((x.recovering = true ∨ (cfg.drops = true ∧ x.top.getD 0 < x.floor)) ∧ ow = none ∧
            reachReady (cfg.at v) x.disk (refsAt (cfg.at v) x.disk r ow x.evidence) r
              (excluded (cfg.at v) x.disk r x.evidence) = true ∧
            certReady (cfg.at v) x.disk (refsAt (cfg.at v) x.disk r ow x.evidence) r
              (excluded (cfg.at v) x.disk r x.evidence) = true))) ∧
        c ∉ x.disk.ids ∧
      (∃ y o, tryBuild (cfg.at v) x = some (y, o) ∧
        (c, R.block c) ∈ persists o ∧ (c, R.block c) ∈ persists (outputsAt cfg tr i₀)) ∧
      (R.block c).refs =
        refsAt (cfg.at v) x.disk r ow x.evidence ∧
      refsAt (cfg.at v) x.disk r ow x.evidence ⊆ x.disk.ids ∧
      DiskRises (cfg.at v) x (stateBefore cfg tr (i₀ + 1) v) ∧
      ((reachReady (cfg.at v) x.disk (refsAt (cfg.at v) x.disk r ow x.evidence) r
        (excluded (cfg.at v) x.disk r x.evidence) = true ∧
          certReady (cfg.at v) x.disk (refsAt (cfg.at v) x.disk r ow x.evidence) r
            (excluded (cfg.at v) x.disk r x.evidence) = true) ∨
        ((x.top = some r ∧ r ∈ x.fired ∨ behind (cfg.at v) x.disk r) ∧
          (refsAt (cfg.at v) x.disk r ow x.evidence = refsFor (cfg.at v) x.disk r ow x.evidence ∨
            buildable (cfg.at v) x.disk r (refsFor (cfg.at v) x.disk r ow x.evidence)
              x.evidence = false))) ∧
      (R.block c).payload =
        payloadFor (cfg.at v) x.disk r (refsAt (cfg.at v) x.disk r ow x.evidence) x.evidence
    := by
  have hinjR := hashInjective_of_trace hinj
  have hauthR := authentic_of_timely htime
  -- the block, as the honest nodes knew it, is one of `v`'s own
  obtain ⟨x, hxdef⟩ : ∃ x : BlockId × Block Validator BlockId Payload, x = (c, R.block c) :=
    ⟨_, rfl⟩
  have hxK : x ∈ knownAll cfg H tr := hxdef ▸ hbase.real c hcU (by rw [hcr]; omega)
  have hxc : x.2.creator = v := by rw [hxdef]; exact hcv
  have hxr : x.2.round = r + 1 := by rw [hxdef]; exact hcr
  have hxp := mem_persists_of_known hinjR hauthR hxK (by rw [hxc]; exact hv)
  rw [hxc] at hxp
  -- the first event building round `r + 1` builds it
  obtain ⟨j, hj₁, hjv, hje⟩ := hwin
  obtain ⟨i₀, hi₀j, hbt, hi₀v, e₀, he₀, he₀r⟩ := builtAt_first (cfg := cfg) time hjv hje
  obtain ⟨inp, hi₀⟩ : ∃ inp, tr[i₀]? = some (v, inp) := by
    rcases h : tr[i₀]? with _ | ⟨w, inp⟩
    · rw [h] at hi₀v; cases hi₀v
    · rw [h] at hi₀v; cases hi₀v; exact ⟨inp, rfl⟩
  have he₀p : e₀ ∈ persists (runOf cfg tr v).2 :=
    mem_persists_iff.mpr (mem_outputs_of_event hi₀ (mem_persists_iff.mp he₀))
  have hex : e₀ = x := eq_of_persists v he₀p hxp (by rw [he₀r, hxr])
  subst hex
  have hc₁ : e₀.1 = c := by rw [hxdef]
  subst hc₁
  have hw₁ : i₀ + 1 ≤ E₁ := by omega
  obtain ⟨x', y, o, hbs, hb, heo, hgx⟩ := build_witness hbase hv hi₀ hw₁ he₀
    (by rw [he₀r]; omega)
  obtain ⟨r', ow, hsome, hle, hro, -, hexit, hout⟩ := tryBuild_exit hb
  -- it builds round `r + 1`
  have hr'r : r' = r := by
    obtain ⟨r'', id, b, -, -, -, -, hbr, -, -, -, -, -, -, -, hout'⟩ := tryBuild_some hb
    have h₁ := congrArg persists (hout.symm.trans hout')
    rw [persists_built, persists_built, List.singleton_inj] at h₁
    have h₂ := congrArg (fun e => e.2.round) h₁
    simp only [blockOn] at h₂
    have heo' := heo
    rw [hout', persists_built, List.mem_singleton] at heo'
    have h₃ := congrArg (fun e => e.2.round) heo'
    simp only at h₃
    omega
  -- the step is regular, so the node builds at or above its floor
  have hreg : ¬ (cfg.drops = true ∧ x'.top.getD 0 < x'.floor) := by
    rintro ⟨hdr, hlt⟩
    have hE : E₀ ≤ i₀ := by
      by_contra h
      exact hE₀ hdr i₀ (by omega) hi₀v e₀ he₀ he₀r
    obtain ⟨-, hft, hrg⟩ := hbase.window v hv i₀ hE (by omega)
    obtain ⟨-, -, -, hfl⟩ := hrg (by omega) hdr
    have h₁ := hgx.1.1
    have h₂ := hbs.top
    rw [hfl] at h₁
    omega
  replace hro : (x'.top = some r' ∧ ow = x'.own) ∨
      ((x'.recovering = true ∨ (cfg.drops = true ∧ x'.top.getD 0 < x'.floor)) ∧ ow = none ∧
        reachReady (cfg.at v) x'.memory (refsAt (cfg.at v) x'.memory r' ow x'.evidence) r'
          (excluded (cfg.at v) x'.memory r' x'.evidence) = true ∧
        certReady (cfg.at v) x'.memory (refsAt (cfg.at v) x'.memory r' ow x'.evidence) r'
          (excluded (cfg.at v) x'.memory r' x'.evidence) = true) := by
    rcases hro with h | ⟨hrec, h⟩ | h
    · exact Or.inl h
    · exact Or.inr ⟨Or.inl hrec, h⟩
    · exact absurd ⟨h.1, h.2.1⟩ hreg
  replace hexit := hexit.imp_right fun h => h.resolve_right hreg
  -- at a node that drops, its floor lies at or below the round above the base
  have hFl : cfg.drops = true → x'.floor ≤ B + 1 := fun hdr => by
    obtain ⟨Bs, hi⟩ := hbs.inv
    have h₁ := hi.floor
    unfold floorOf at h₁
    rw [if_pos (show (cfg.at v).drops = true from hdr)] at h₁
    exact h₁.trans (hbs.slot hdr)
  -- the build read in memory as on disk
  have hF : x'.floor ≤ r' - (cfg.at v).p.voteOffset := by
    cases hdr : cfg.drops
    · obtain ⟨Bs, hi⟩ := hbs.inv
      exact hi.floor.trans ((floorOf_le_top (cfg := cfg.at v) hdr _).trans
        (Nat.sub_le_sub_right hle _))
    · have := hFl hdr; have := hrV hdr
      change x'.floor ≤ r' - cfg.p.voteOffset
      omega
  have ho : ∀ j, ow = some j → j ∈ x'.disk.ids ∧ (x'.disk.blk j).round = r' := fun j hj => by
    rcases hro with ⟨hr', rfl⟩ | ⟨-, hnone, -⟩
    · obtain ⟨j', hj', hjd, hjr, -⟩ := hbs.own r' hr'
      rw [hj', Option.some.injEq] at hj
      exact hj ▸ ⟨hjd, hjr⟩
    · rw [hnone] at hj; cases hj
  have hreads := x'.mirrors.build_reads (cfg := cfg.at v) hσ (r := r') (o := ow)
    (E := x'.evidence) hF ho
  obtain ⟨e₁, e₂, e₃, e₄, e₅, e₆⟩ := hreads
  have hbl : buildable (cfg.at v) x'.memory r' (refsFor (cfg.at v) x'.disk r' ow x'.evidence)
      x'.evidence = buildable (cfg.at v) x'.disk r' (refsFor (cfg.at v) x'.disk r' ow x'.evidence)
      x'.evidence :=
    x'.mirrors.buildable_eq (le_trans hF (Nat.sub_le _ _)) (fun c hc => by
      rcases mem_refsFor_of hc with hc | hc
      · exact Store.mem_atRound.mp hc
      · exact ho c hc) _
  rw [e₁, e₂, e₄, e₅, e₃, hbl] at hexit
  rw [e₁, e₄, e₅] at hro
  rw [e₁] at hout
  obtain ⟨r'', id, b, hnew, hrefs, hpred, -, hbr, -, hid, -, hst, -, -, -, hout'⟩ :=
    tryBuild_some hb
  have hrr' : r'' = r' := by
    have h1 := congrArg persists (hout.symm.trans hout')
    rw [persists_built, persists_built, List.singleton_inj] at h1
    have := congrArg (fun e => e.2.round) h1
    simp only [blockOn] at this
    omega
  subst r''
  rw [hout, persists_built, List.mem_singleton] at heo
  have hrr : r' = r := by
    have := congrArg (fun e => e.2.round) heo
    simp only [blockOn] at this
    omega
  subst hrr
  -- the record reads the block as built
  have hy := BuildState.tryBuild (cfg := cfg.at v) ⟨hbase.grounds v hv, hbase.known⟩
    hbs hb (fun e he => by
    rw [hout, persists_built, List.mem_singleton] at he
    have : e = e₀ := he.trans heo.symm
    rw [this]; exact hxK)
  have hAB := congrArg persists (hout.symm.trans hout')
  rw [persists_built, persists_built, List.singleton_inj] at hAB
  have heo' : e₀ = (id, b) := heo.trans hAB
  have hcy : e₀.1 ∈ y.disk.ids := by
    rw [heo', hst.ids]; exact Store.mem_insert_self
  have hyb : y.disk.full e₀.1 = b := by
    rw [heo', hst.full, Store.full_insert, if_pos rfl]
  have hUb : R.block e₀.1 = b := by
    have hround : (y.disk.full e₀.1).round = e₀.2.round := by rw [hyb, heo']
    exact ((hy.cut e₀.1 hcy (by rw [hround]; omega)).2.2.2 (by rw [hround]; omega)).trans hyb
  have hbrefs : b.refs = refsAt (cfg.at v) x'.disk r' ow x'.evidence := by
    have := congrArg (fun e => e.2.refs) hAB
    simp only at this
    exact this.symm
  have hbpay : b.payload = payloadFor (cfg.at v) x'.disk r'
      (refsAt (cfg.at v) x'.disk r' ow x'.evidence) x'.evidence := by
    have := congrArg (fun e => e.2.payload) hAB
    simp only [blockOn] at this
    rw [← e₆]; exact this.symm
  have hce : (e₀.1, R.block e₀.1) = e₀ := by rw [hUb, heo']
  refine ⟨i₀, inp, x', ow, hi₀, hbt, hbs, ⟨hsome, hle,
    hro⟩,
    by rw [heo']; exact hnew,
    ⟨y, o, hb, by rw [hce, hout, persists_built, List.mem_singleton]; exact heo,
      by rw [hce]; exact he₀⟩, by rw [hUb, hbrefs], ?_, hgx, hexit, by rw [hUb, hbpay]⟩
  rw [← hbrefs]
  exact hrefs

end Node

end LeanDag
