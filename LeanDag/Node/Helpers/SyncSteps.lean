import LeanDag.Node.Helpers.Steps
import LeanDag.Node.Helpers.SyncWalk
/-!
# What a step does to one sync

A detected author has two blocks at one round on the disk (`TwinsOn`,
`TwinsOn.step`). The syncs name distinct peers, none the node itself,
ask for distinct names and hold blocks of their peers (`SyncsOn`,
`SyncsOn.step`, `step_peer_ne`, `syncsOn_run`), so there are at most
`n − 1` (`syncs_length_le`). A settle only drops syncs whose block is held
or whose peer is detected, and asks for nothing (`Thins.settle`,
`noAsk_settle`). For one sync `(u, t, A)`, a step keeps it unless its
block is held, its peer detected, or a delivery from its peer is above
its block (`step_keeps`); a sync after a step was asked for there or
held before (`step_origin`); its names after a step are those of every
request for it there (`step_ask`), and with no such request among the
old names (`step_same`). A stream piece that leads to no request for a
sync it answers gains no block, and each reference of the piece's part
in the sync's history that the disk lacks was asked for by name
(`step_stream_stuck`).
-/

namespace LeanDag

namespace Node

variable {Validator BlockId Payload : Type} [Fintype Validator] [DecidableEq Validator]
variable [LinearOrder BlockId]
variable {cfg : Config Validator BlockId Payload}

omit [Fintype Validator] in
/-- **A build keeps `Kept`** under a faithful payload source: the block
carries part of the node's evidence. -/
theorem Kept.tryBuild (hf : cfg.Faithful) {s s' : State Validator BlockId Payload}
    {out : List (Output Validator BlockId Payload)} (h : Kept cfg s)
    (hb : Node.tryBuild cfg s = some (s', out)) : Kept cfg s' := by
  obtain ⟨t, r, o, -, hb', -⟩ := tryBuild_cases hb
  obtain ⟨id, b, hnew, hrefs, hpred, -, -, -, -, hbdef, -, hd, -⟩ := buildAbove_some hb'
  have hev := (tryBuild_detected hb).2
  refine h.insert hd (by rw [hev]) fun e he hne => ?_
  rw [hev]
  rw [hbdef] at he
  simp only [blockOn, payloadFor] at he
  rw [(hf _ _ _).1] at he
  exact (Finset.mem_filter.mp he).1

/-! ## Thinning the syncs -/

variable (cfg) in
/-- **`s'` thins the syncs of `s`**: it keeps a part of them, dropping only
those whose block it holds or whose peer it detected, grows the disk and
the detected authors, and keeps `EvidenceOn`, and `Kept` under a faithful
payload source. -/
structure Thins (s s' : State Validator BlockId Payload) : Prop where
  sub : s'.syncs.Sublist s.syncs
  kept : ∀ e ∈ s.syncs, e ∈ s'.syncs ∨ e.2.1.1 ∈ s'.disk.ids ∨ e.1 ∈ s'.detected
  grows : Grows s.disk s'.disk
  det : s.detected ⊆ s'.detected
  twins : EvidenceOn cfg s → EvidenceOn cfg s'
  holds : cfg.Faithful → Kept cfg s → Kept cfg s'

omit [Fintype Validator] in
theorem Thins.refl (s : State Validator BlockId Payload) : Thins cfg s s :=
  ⟨List.Sublist.refl _, fun _ h => Or.inl h, Grows.refl _, subset_rfl, id, fun _ h => h⟩

omit [Fintype Validator] in
theorem Thins.trans {a b c : State Validator BlockId Payload} (h₁ : Thins cfg a b) (h₂ : Thins cfg
    b c) :
    Thins cfg a c := by
  refine ⟨h₂.sub.trans h₁.sub, fun e he => ?_, h₁.grows.trans h₂.grows, h₁.det.trans h₂.det,
    h₂.twins ∘ h₁.twins, fun hf h => h₂.holds hf (h₁.holds hf h)⟩
  rcases h₁.kept e he with h | h | h
  · exact h₂.kept e h
  · exact Or.inr (Or.inl (h₂.grows.1 h))
  · exact Or.inr (Or.inr (h₂.det h))

omit [Fintype Validator] in
/-- A state with the syncs, the detected authors and the evidence kept,
and the disk grown keeping `Kept`, thins the syncs. -/
theorem Thins.of_grows {s s' : State Validator BlockId Payload} (hg : Grows s.disk s'.disk)
    (hs : s'.syncs = s.syncs) (hd : s'.detected = s.detected)
    (he : s'.evidence = s.evidence) (hk : cfg.Faithful → Kept cfg s → Kept cfg s') :
    Thins cfg s s' :=
  ⟨hs ▸ List.Sublist.refl _, fun _ he => Or.inl (hs ▸ he), hg, hd ▸ subset_rfl,
    fun h => h.grow hg hd he, hk⟩

omit [Fintype Validator] in
/-- A state with the disk, the syncs, the detected authors and the evidence
kept thins the syncs. -/
theorem Thins.of_same {s s' : State Validator BlockId Payload} (hdk : s'.disk = s.disk)
    (hs : s'.syncs = s.syncs) (hd : s'.detected = s.detected)
    (he : s'.evidence = s.evidence) : Thins cfg s s' :=
  Thins.of_grows (hdk ▸ Grows.refl _) hs hd he fun _ h => h.of_eq hdk he

omit [Fintype Validator] in
theorem Thins.accept (s : State Validator BlockId Payload) (id : BlockId)
    (b : Block Validator BlockId Payload) : Thins cfg s (Node.accept cfg s id b) := by
  have hr := accept_rest (cfg := cfg) (s := s) (id := id) (b := b)
  refine ⟨hr.2.1 ▸ List.Sublist.refl _, fun e he => Or.inl (hr.2.1 ▸ he), ?_, hr.2.2.2.2.2.2.2.2.2,
    fun h => h.accept id b, fun _ h => h.accept id b⟩
  rw [accept_disk]; exact Grows.accept _ _ _

omit [Fintype Validator] in
theorem Thins.absorb (s : State Validator BlockId Payload) :
    ∀ L : List (BlockId × Block Validator BlockId Payload), Thins cfg s (Node.absorb cfg s L)
  | [] => Thins.refl s
  | x :: L => by
    unfold Node.absorb
    rw [List.foldl_cons]
    exact (Thins.accept s x.1 x.2).trans (Thins.absorb _ L)

omit [Fintype Validator] in
theorem Thins.tidy (s : State Validator BlockId Payload) : Thins cfg s (Node.tidy s) := by
  refine ⟨List.filter_sublist, fun e he => ?_, Grows.refl _, subset_rfl, id, fun _ h => h⟩
  by_cases hk : e.2.1.1 ∉ s.disk.ids ∧ e.1 ∉ s.detected
  · exact Or.inl (List.mem_filter.mpr ⟨he, by simp only [decide_eq_true_eq]; exact hk⟩)
  · right
    by_cases h₁ : e.2.1.1 ∈ s.disk.ids
    · exact Or.inl h₁
    · exact Or.inr (by by_contra h₂; exact hk ⟨h₁, h₂⟩)

omit [Fintype Validator] in
theorem Thins.takeIn (s : State Validator BlockId Payload)
    (t : BlockId × Block Validator BlockId Payload)
    (L : List (BlockId × Block Validator BlockId Payload)) :
    Thins cfg s (Node.takeIn cfg s t L) := by
  unfold Node.takeIn
  split
  · exact (Thins.absorb s L).trans (Thins.tidy _)
  · exact Thins.refl s

omit [Fintype Validator] in
theorem Thins.flushSyncs : ∀ (fuel : ℕ) (s : State Validator BlockId Payload),
    Thins cfg s (Node.flushSyncs cfg fuel s)
  | 0, s => Thins.refl s
  | fuel + 1, s => by
    unfold Node.flushSyncs
    dsimp only
    split
    · exact Thins.refl s
    · exact ((Thins.absorb s _).trans (Thins.tidy _)).trans (Thins.flushSyncs fuel _)

omit [Fintype Validator] in
theorem Thins.progress : ∀ (fuel : ℕ) (s : State Validator BlockId Payload),
    Thins cfg s (Node.progress cfg fuel s).1
  | 0, s => Thins.refl s
  | fuel + 1, s => by
    unfold Node.progress
    split
    · rename_i s₁ out h
      have h₁ : Thins cfg s s₁ := by
        refine Thins.of_grows ?_ (tryBuild_syncs h) (tryBuild_detected h).1
          (tryBuild_detected h).2 fun hf hk => hk.tryBuild hf h
        obtain ⟨_, _, _, _, _, _, -, -, -, -, -, hd, -⟩ := tryBuild_some h
        rw [hd]; exact Grows.insert _
      exact h₁.trans (Thins.progress fuel s₁)
    · exact Thins.refl s

omit [Fintype Validator] in
theorem Thins.decideStep (s : State Validator BlockId Payload) :
    Thins cfg s (Node.decideStep cfg s).1 := by
  have hd : (Node.decideStep cfg s).1.detected = s.detected ∧
      (Node.decideStep cfg s).1.evidence = s.evidence := by
    unfold Node.decideStep
    dsimp only
    split
    · simp
    · exact ⟨rfl, rfl⟩
  exact Thins.of_same (decideStep_disk s) (decideStep_syncs s) hd.1 hd.2

omit [Fintype Validator] in
theorem Thins.advance (s : State Validator BlockId Payload) : Thins cfg s (Node.advance cfg s).1 :=
    by
  obtain ⟨a, ha⟩ := arm_eq (cfg := cfg) (Node.pass cfg s).1
  have hp : Thins cfg s (Node.pass cfg s).1 :=
    ((Thins.progress _ s).trans (Thins.decideStep _)).trans (Thins.flushSyncs _ _)
  unfold Node.advance
  dsimp only
  rw [ha]
  exact hp.trans (Thins.of_same rfl rfl rfl rfl)

omit [Fintype Validator] in
theorem Thins.settle (s : State Validator BlockId Payload) : Thins cfg s (Node.settle cfg s).1 :=
  (quiesce_rel (P := fun _ => True) (R := fun a _ b => Thins cfg a b)
    (fun s => Thins.refl s) (fun _ _ _ _ _ h₁ h₂ => h₁.trans h₂)
    (fun s _ => ⟨Thins.advance s, trivial⟩) _ s trivial).1

/-! ## Passes ask for nothing -/

/-- **No output asks for a block.** -/
def NoAsk (out : List (Output Validator BlockId Payload)) : Prop :=
  ∀ o ∈ out, ∀ peer t fr ids, o ≠ .sync peer t fr ids

omit [Fintype Validator] [DecidableEq Validator] [LinearOrder BlockId] in
theorem NoAsk.append {a b : List (Output Validator BlockId Payload)} (ha : NoAsk a)
    (hb : NoAsk b) : NoAsk (a ++ b) := fun o ho => by
  rcases List.mem_append.mp ho with h | h
  · exact ha o h
  · exact hb o h

omit [Fintype Validator] [DecidableEq Validator] [LinearOrder BlockId] in
theorem noAsk_quiet {out : List (Output Validator BlockId Payload)}
    (h : ∀ o ∈ out, (∃ r d, o = .setTimer r d) ∨ (∃ k d, o = .commit k d) ∨
      (∃ id b, o = .persist id b) ∨ ∃ id b, o = .broadcast id b) : NoAsk out := by
  intro o ho peer t fr ids he
  subst he
  rcases h _ ho with ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ <;> cases h

omit [Fintype Validator] in
theorem noAsk_progress : ∀ (fuel : ℕ) (s : State Validator BlockId Payload),
    NoAsk (Node.progress cfg fuel s).2
  | 0, _ => fun o ho => absurd ho List.not_mem_nil
  | fuel + 1, s => by
    unfold Node.progress
    split
    · rename_i s₁ out h
      refine NoAsk.append ?_ (noAsk_progress fuel s₁)
      obtain ⟨id, b, rfl, -⟩ := tryBuild_own h
      refine noAsk_quiet fun o ho => ?_
      simp only [built, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_cons,
        List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl | rfl
      · exact Or.inr (Or.inr (Or.inl ⟨_, _, rfl⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨_, _, rfl⟩))
      · exact Or.inl ⟨_, _, rfl⟩
    · exact fun o ho => absurd ho List.not_mem_nil

omit [Fintype Validator] in
theorem noAsk_decideStep (s : State Validator BlockId Payload) :
    NoAsk (Node.decideStep cfg s).2 := by
  unfold Node.decideStep
  dsimp only
  split
  · refine noAsk_quiet fun o ho => ?_
    obtain ⟨e, -, rfl⟩ := List.mem_map.mp ho
    exact Or.inr (Or.inl ⟨_, _, rfl⟩)
  · exact fun o ho => absurd ho List.not_mem_nil

omit [Fintype Validator] in
theorem noAsk_advance (s : State Validator BlockId Payload) : NoAsk (Node.advance cfg s).2 := by
  unfold Node.advance Node.pass
  dsimp only
  refine ((noAsk_progress _ s).append (noAsk_decideStep _)).append (noAsk_quiet fun o ho => ?_)
  obtain ⟨r, -, -, -, rfl⟩ := mem_arm ho
  exact Or.inl ⟨_, _, rfl⟩

omit [Fintype Validator] in
theorem noAsk_settle (s : State Validator BlockId Payload) : NoAsk (Node.settle cfg s).2 :=
  (quiesce_rel (P := fun _ => True) (R := fun _ o _ => NoAsk o)
    (fun _ _ ho => absurd ho List.not_mem_nil) (fun _ _ _ _ _ h₁ h₂ => h₁.append h₂)
    (fun s _ => ⟨noAsk_advance s, trivial⟩) _ s trivial).1

/-! ## The syncs' shape -/

/-- **The syncs name distinct peers**, each asking for distinct names, for a
block of its peer. -/
def SyncsOn (s : State Validator BlockId Payload) : Prop :=
  (s.syncs.map (·.1)).Nodup ∧ ∀ e ∈ s.syncs, e.2.2.Nodup ∧ e.2.1.2.creator = e.1

omit [Fintype Validator] [DecidableEq Validator] in
theorem SyncsOn.sublist {s s' : State Validator BlockId Payload} (h : SyncsOn s)
    (hs : s'.syncs.Sublist s.syncs) : SyncsOn s' :=
  ⟨(hs.map _).nodup h.1, fun e he => h.2 e (hs.subset he)⟩

omit [Fintype Validator] [DecidableEq Validator] in
theorem SyncsOn.eq {s : State Validator BlockId Payload} (h : SyncsOn s)
    {e e' : Validator × (BlockId × Block Validator BlockId Payload) × List BlockId}
    (he : e ∈ s.syncs) (he' : e' ∈ s.syncs) (hp : e.1 = e'.1) : e = e' :=
  List.inj_on_of_nodup_map h.1 he he' hp

omit [Fintype Validator] in
/-- **A peer's sync is the one found for it.** -/
theorem SyncsOn.find {s : State Validator BlockId Payload} (h : SyncsOn s)
    {e : Validator × (BlockId × Block Validator BlockId Payload) × List BlockId}
    (he : e ∈ s.syncs) : (s.syncs.find? fun x => decide (x.1 = e.1)) = some e := by
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp
    ((List.find?_isSome (p := fun x => decide (x.1 = e.1))).mpr ⟨e, he, by simp⟩)
  have hxp : x.1 = e.1 := by simpa using List.find?_some hx
  rw [hx, h.eq (List.mem_of_find?_eq_some hx) he hxp]

omit [Fintype Validator] [DecidableEq Validator] in
/-- Adding names to distinct ones without growing the list adds none. -/
theorem mem_of_dedup_length {A M : List BlockId} (hA : A.Nodup)
    (h : (A ++ M).dedup.length = A.length) {y : BlockId} (hy : y ∈ M) : y ∈ A := by
  by_contra hyA
  have hsub : (y :: A).Subperm (A ++ M).dedup :=
    (List.nodup_cons.mpr ⟨hyA, hA⟩).subperm fun x hx => List.mem_dedup.mpr (by
      rcases List.mem_cons.mp hx with rfl | hx
      · exact List.mem_append_right _ hy
      · exact List.mem_append_left _ hx)
  have := hsub.length_le
  simp only [List.length_cons] at this
  omega

/-! ## The step's shape -/

variable (cfg) in
/-- **A plain step**: it thins the syncs, and asks only as an old sync
does. -/
structure Plain (s s' : State Validator BlockId Payload)
    (out : List (Output Validator BlockId Payload)) : Prop where
  thins : Thins cfg s s'
  asks : ∀ peer i fr ids, Output.sync peer i fr ids ∈ out →
    ∃ e ∈ s.syncs, e.1 = peer ∧ e.2.1.1 = i ∧ e.2.2 = ids

omit [Fintype Validator] in
theorem Plain.of {s s' : State Validator BlockId Payload}
    {out : List (Output Validator BlockId Payload)}
    (ht : Thins cfg s s') (hn : NoAsk out) : Plain cfg s s' out :=
  ⟨ht, fun peer i fr ids ho => absurd rfl (hn _ ho peer i fr ids)⟩

omit [Fintype Validator] in
theorem resend_asks {s : State Validator BlockId Payload} {peer : Validator} {i : BlockId}
    {fr : Validator → ℕ} {ids : List BlockId} (h : Output.sync peer i fr ids ∈ resend cfg s) :
    ∃ e ∈ s.syncs, e.1 = peer ∧ e.2.1.1 = i ∧ e.2.2 = ids := by
  unfold resend at h
  rcases List.mem_append.mp h with h | h
  · split at h <;> simp at h
  · unfold resync at h
    obtain ⟨e, he, heq⟩ := List.mem_map.mp h
    simp only [request, Output.sync.injEq] at heq
    exact ⟨e, he, heq.1, heq.2.1, heq.2.2.2⟩

/-- **A delivery**: nothing, an acceptance, or a new sync for its peer, with
its block above the peer's old one. -/
theorem step_deliver_cases {s : State Validator BlockId Payload} (hs : SyncsOn s) (u : Validator)
    (id : BlockId) (b : Block Validator BlockId Payload) :
    Node.step cfg s (.deliver u id b) = (s, []) ∨
      Node.step cfg s (.deliver u id b) = Node.settle cfg (tidy (Node.accept cfg s id b)) ∨
      (id = cfg.idOf b ∧ b.creator = u ∧ u ≠ cfg.me ∧
        (∀ e ∈ s.syncs, e.1 = u → e.2.1.2.round < b.round) ∧
        Node.step cfg s (.deliver u id b) =
          ((Node.settle cfg { s with syncs := (u, (id, b), ([] : List BlockId)) ::
              (s.syncs.filter fun e => decide (e.1 ≠ u)) }).1,
            request { s with syncs := (u, (id, b), ([] : List BlockId)) ::
              (s.syncs.filter fun e => decide (e.1 ≠ u)) } (u, (id, b), []) ::
            (Node.settle cfg { s with syncs := (u, (id, b), ([] : List BlockId)) ::
              (s.syncs.filter fun e => decide (e.1 ≠ u)) }).2)) := by
  rw [step_deliver_eq]
  split_ifs with hg hr hc
  · exact Or.inr (Or.inl rfl)
  · refine Or.inr (Or.inr ⟨hg.1, hg.2.1, hg.2.2.1, fun e he heu => ?_, rfl⟩)
    have hf := hs.find he
    rw [heu] at hf
    rw [hf] at hc
    simpa using hc.2
  · exact Or.inl rfl
  · exact Or.inl rfl

/-- **A stream piece for a sync**: its part in the sync's block's history
taken in, then the sync dropped, or its names asked for extended. -/
theorem step_stream_cases {s : State Validator BlockId Payload} (hs : SyncsOn s) {u : Validator}
    {t : BlockId × Block Validator BlockId Payload} {A : List BlockId} (he : (u, t, A) ∈ s.syncs)
    (L : List (BlockId × Block Validator BlockId Payload)) :
    ((u, t, A) ∉ (takeIn cfg s t (inHistory cfg t L)).syncs ∧
      Node.step cfg s (.stream u L) = Node.settle cfg (takeIn cfg s t (inHistory cfg t L))) ∨
    ((u, t, A) ∈ (takeIn cfg s t (inHistory cfg t L)).syncs ∧
      Node.step cfg s (.stream u L) =
        let s₁ := takeIn cfg s t (inHistory cfg t L)
        let asked := (A ++ missingIn s₁ (t :: inHistory cfg t L)).dedup
        let s₂ := { s₁ with syncs := s₁.syncs.map fun x => if x.1 = u then (u, t, asked) else x }
        ((Node.settle cfg s₂).1,
          (if s₂.disk.ids.card ≠ s.disk.ids.card ∨ asked.length ≠ A.length then
            [request s₂ (u, t, asked)] else []) ++ (Node.settle cfg s₂).2)) := by
  have hf := hs.find he
  rw [step_stream_eq s u L hf]
  split
  · rename_i hn
    refine Or.inl ⟨fun hin => ?_, rfl⟩
    have := List.find?_eq_none.mp hn _ hin
    simp at this
  · rename_i e₁ hn
    have he₁ := List.mem_of_find?_eq_some hn
    have hp := List.find?_some hn
    simp only [decide_eq_true_eq] at hp
    have hsub := Thins.takeIn (cfg := cfg) s t (inHistory cfg t L)
    obtain rfl : e₁ = (u, t, A) := hs.eq (hsub.sub.subset he₁) he hp
    exact Or.inr ⟨he₁, rfl⟩

/-- **A start**, unfolded. -/
theorem step_start_eq (s : State Validator BlockId Payload) :
    Node.step cfg s .start =
      if s.top = none ∧ cfg.Admissible then
        if h : cfg.idOf cfg.genesis ∉ s.disk.ids ∧
            rowValid cfg.q cfg.xp (Function.update s.disk.blk (cfg.idOf cfg.genesis) cfg.genesis)
              cfg.genesis then
          ((Node.settle cfg { Node.keep s (cfg.idOf cfg.genesis) cfg.genesis h.1
              (fun _ hj => absurd hj (Finset.notMem_empty _))
              (fun j hj => absurd hj (Finset.notMem_empty j)) with
              top := some 0, own := some (cfg.idOf cfg.genesis), recovering := false }).1,
            [.persist (cfg.idOf cfg.genesis) cfg.genesis,
              .broadcast (cfg.idOf cfg.genesis) cfg.genesis,
              .setTimer 0 (2 * cfg.timeout 0)] ++
            (Node.settle cfg { Node.keep s (cfg.idOf cfg.genesis) cfg.genesis h.1
              (fun _ hj => absurd hj (Finset.notMem_empty _))
              (fun j hj => absurd hj (Finset.notMem_empty j)) with
              top := some 0, own := some (cfg.idOf cfg.genesis), recovering := false }).2)
        else (s, [])
      else (s, []) := rfl

/-- **A start is plain.** -/
theorem step_start_plain (s : State Validator BlockId Payload) :
    Plain cfg s (Node.step cfg s .start).1 (Node.step cfg s .start).2 := by
  rw [step_start_eq]
  split_ifs with h₁ h₂
  · refine Plain.of (Thins.trans ?_ (Thins.settle _)) (NoAsk.append (noAsk_quiet fun o ho => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
        rcases ho with rfl | rfl | rfl
        · exact Or.inr (Or.inr (Or.inl ⟨_, _, rfl⟩))
        · exact Or.inr (Or.inr (Or.inr ⟨_, _, rfl⟩))
        · exact Or.inl ⟨_, _, rfl⟩) (noAsk_settle _))
    exact Thins.of_grows (Grows.insert (hrefs := fun _ hj => absurd hj (Finset.notMem_empty _))
      (hpred := fun j hj => absurd hj (Finset.notMem_empty j)) _) rfl rfl rfl fun hf hk =>
        hk.insert (hnew := h₂.1) (hrefs := fun _ hj => absurd hj (Finset.notMem_empty _))
          (hpred := fun j hj => absurd hj (Finset.notMem_empty j)) rfl subset_rfl fun e he => by
          simp only [Config.genesis] at he
          rw [(hf _ _ _).1] at he
          exact absurd he (Finset.notMem_empty _)
  · exact Plain.of (Thins.refl s) fun o ho => absurd ho List.not_mem_nil
  · exact Plain.of (Thins.refl s) fun o ho => absurd ho List.not_mem_nil

/-- **A timer is plain.** -/
theorem step_timer_plain (s : State Validator BlockId Payload) (r : ℕ) :
    Plain cfg s (Node.step cfg s (.timer r)).1 (Node.step cfg s (.timer r)).2 := by
  refine ⟨by
    rw [step_timer_fst]
    exact Thins.trans (b := { s with fired := fire s r, recovering := false })
      (Thins.of_same rfl rfl rfl rfl) (Thins.settle _), fun peer i fr ids ho => ?_⟩
  rcases step_timer_snd (cfg := cfg) s r with h | h
  · rw [h] at ho; exact absurd rfl (noAsk_settle _ _ ho peer i fr ids)
  · rw [h] at ho
    rcases List.mem_append.mp ho with ho | ho
    · exact absurd rfl (noAsk_settle _ _ ho peer i fr ids)
    · obtain ⟨e, he, h₁⟩ := resend_asks ho
      exact ⟨e, (Thins.settle (cfg := cfg)
        { s with fired := fire s r, recovering := false }).sub.subset he, h₁⟩

/-- **A request for a stream is plain.** -/
theorem step_syncRequest_plain (s : State Validator BlockId Payload) (peer : Validator)
    (t : BlockId) (fr : Validator → ℕ) (ids : List BlockId) :
    Plain cfg s (Node.step cfg s (.syncRequest peer t fr ids)).1
      (Node.step cfg s (.syncRequest peer t fr ids)).2 := by
  have h : Node.step cfg s (.syncRequest peer t fr ids) =
      (s, if peer ∈ s.detected ∨ (streamOf s.disk t fr ids).isEmpty then [] else
        [.stream peer (streamOf s.disk t fr ids)]) := rfl
  rw [h]
  refine ⟨Thins.refl s, fun peer' i fr' ids' ho => ?_⟩
  split at ho <;> simp at ho

/-- **A request for a round's block is plain.** -/
theorem step_ask_plain (s : State Validator BlockId Payload) (peer : Validator) (r : ℕ) :
    Plain cfg s (Node.step cfg s (.ask peer r)).1 (Node.step cfg s (.ask peer r)).2 := by
  have h : Node.step cfg s (.ask peer r) = (s, if peer ∈ s.detected then [] else
      match ownAt cfg s r with
      | some i => [.send peer i (s.disk.blk i)]
      | none => []) := rfl
  rw [h]
  refine Plain.of (Thins.refl s) fun o ho p t fr ids he => ?_
  subst he
  split at ho <;> (try split at ho) <;> simp at ho

/-- **A restart is plain.** -/
theorem step_restart_plain (s : State Validator BlockId Payload) :
    Plain cfg s (Node.step cfg s .restart).1 (Node.step cfg s .restart).2 := by
  refine ⟨by
    rw [step_restart_fst]
    exact Thins.trans (b := { s with recovering := true })
      (Thins.of_same rfl rfl rfl rfl) (Thins.settle _), fun peer i fr ids ho => ?_⟩
  change Output.sync peer i fr ids ∈
    resend cfg s ++ rearm cfg s ++ (Node.settle cfg { s with recovering := true }).2 at ho
  rcases List.mem_append.mp ho with ho | ho
  · rcases List.mem_append.mp ho with ho | ho
    · exact resend_asks ho
    · obtain ⟨r, -, -, h⟩ := mem_rearm ho; cases h
  · exact absurd rfl (noAsk_settle _ _ ho peer i fr ids)

/-- **The step's shape**: plain, a new sync for a delivery's peer, or a
stream piece extending a sync. -/
theorem step_form {s : State Validator BlockId Payload} (hs : SyncsOn s)
    (inp : Input Validator BlockId Payload) :
    Plain cfg s (Node.step cfg s inp).1 (Node.step cfg s inp).2 ∨
    (∃ u id b, inp = .deliver u id b ∧ id = cfg.idOf b ∧ b.creator = u ∧ u ≠ cfg.me ∧
      (∀ e ∈ s.syncs, e.1 = u → e.2.1.2.round < b.round) ∧
      Thins cfg { s with syncs := (u, (id, b), ([] : List BlockId)) ::
        (s.syncs.filter fun e => decide (e.1 ≠ u)) } (Node.step cfg s inp).1 ∧
      (∀ peer i fr ids, Output.sync peer i fr ids ∈ (Node.step cfg s inp).2 →
        peer = u ∧ i = id ∧ ids = []) ∧
      ∃ fr, Output.sync u id fr [] ∈ (Node.step cfg s inp).2) ∨
    (∃ u L t A, inp = .stream u L ∧ (u, t, A) ∈ s.syncs ∧
      (u, t, A) ∈ (takeIn cfg s t (inHistory cfg t L)).syncs ∧
      let s₁ := takeIn cfg s t (inHistory cfg t L)
      let asked := (A ++ missingIn s₁ (t :: inHistory cfg t L)).dedup
      let s₂ := { s₁ with syncs := s₁.syncs.map fun x => if x.1 = u then (u, t, asked) else x }
      Thins cfg s₂ (Node.step cfg s inp).1 ∧
      (∀ peer i fr ids, Output.sync peer i fr ids ∈ (Node.step cfg s inp).2 →
        peer = u ∧ i = t.1 ∧ ids = asked) ∧
      ((∀ fr ids, Output.sync u t.1 fr ids ∉ (Node.step cfg s inp).2) →
        s₂.disk.ids.card = s.disk.ids.card ∧ asked.length = A.length)) := by
  cases inp with
  | start => exact Or.inl (step_start_plain s)
  | deliver u id b =>
    rcases step_deliver_cases hs u id b with h | h | ⟨hid, hc, hme, hr, h⟩
    · left; rw [h]; exact Plain.of (Thins.refl s) fun o ho => absurd ho List.not_mem_nil
    · left; rw [h]
      exact Plain.of (((Thins.accept s id b).trans (Thins.tidy _)).trans (Thins.settle _))
        (noAsk_settle _)
    · right; left
      refine ⟨u, id, b, rfl, hid, hc, hme, hr, ?_, fun peer i fr ids ho => ?_, ?_⟩
      · rw [h]; exact Thins.settle _
      · rw [h] at ho
        rcases List.mem_cons.mp ho with ho | ho
        · simp only [request, Output.sync.injEq] at ho
          exact ⟨ho.1, ho.2.1, ho.2.2.2⟩
        · exact absurd rfl (noAsk_settle _ _ ho peer i fr ids)
      · rw [h]; exact ⟨_, List.mem_cons_self⟩
  | stream u L =>
    cases hf : s.syncs.find? fun e => decide (e.1 = u) with
    | none =>
      left
      have : Node.step cfg s (.stream u L) = (s, []) := by simp only [Node.step, hf]
      rw [this]; exact Plain.of (Thins.refl s) fun o ho => absurd ho List.not_mem_nil
    | some e =>
      have he := List.mem_of_find?_eq_some hf
      have hp := List.find?_some hf
      simp only [decide_eq_true_eq] at hp
      obtain ⟨w, t, A⟩ := e
      simp only at hp
      subst hp
      rcases step_stream_cases (cfg := cfg) hs he L with ⟨-, h⟩ | ⟨hin, h⟩
      · left; rw [h]
        exact Plain.of ((Thins.takeIn s _ _).trans (Thins.settle _))
          (noAsk_settle _)
      · right; right
        refine ⟨w, L, t, A, rfl, he, hin, ?_, fun peer i fr ids ho => ?_, fun hno => ?_⟩
        · rw [h]; exact Thins.settle _
        · rw [h] at ho
          rcases List.mem_append.mp ho with ho | ho
          · split at ho
            · rw [List.mem_singleton] at ho
              simp only [request, Output.sync.injEq] at ho
              exact ⟨ho.1, ho.2.1, ho.2.2.2⟩
            · exact absurd ho List.not_mem_nil
          · exact absurd rfl (noAsk_settle _ _ ho peer i fr ids)
        · rw [h] at hno
          by_contra hm
          exact hno _ _ (List.mem_append_left _
            (List.mem_ite_nil_right.mpr ⟨not_and_or.mp hm, List.mem_singleton_self _⟩))
  | timer r => exact Or.inl (step_timer_plain s r)
  | syncRequest peer t fr ids => exact Or.inl (step_syncRequest_plain s peer t fr ids)
  | ask peer r => exact Or.inl (step_ask_plain s peer r)
  | restart => exact Or.inl (step_restart_plain s)

/-! ## One sync across a step -/

omit [Fintype Validator] [LinearOrder BlockId] in
theorem map_peers
    {S : List (Validator × (BlockId × Block Validator BlockId Payload) × List BlockId)}
    {u : Validator} {x : (BlockId × Block Validator BlockId Payload) × List BlockId} :
    (S.map fun y => if y.1 = u then (u, x) else y).map (·.1) = S.map (·.1) := by
  rw [List.map_map]
  refine List.map_congr_left fun y _ => ?_
  simp only [Function.comp_apply]
  split
  · rename_i h; exact h.symm
  · rfl

omit [Fintype Validator] in
theorem SyncsOn.fresh {s : State Validator BlockId Payload} (h : SyncsOn s) {u : Validator}
    {id : BlockId} {b : Block Validator BlockId Payload} (hc : b.creator = u) :
    SyncsOn { s with syncs := (u, (id, b), ([] : List BlockId)) ::
      (s.syncs.filter fun e => decide (e.1 ≠ u)) } := by
  refine ⟨?_, fun e he => ?_⟩
  · rw [List.map_cons, List.nodup_cons]
    refine ⟨fun hu => ?_, (List.filter_sublist.map _).nodup h.1⟩
    obtain ⟨e, he, heu⟩ := List.mem_map.mp hu
    have := (List.mem_filter.mp he).2
    simp only [decide_eq_true_eq] at this
    exact this heu
  · rcases List.mem_cons.mp he with rfl | he
    · exact ⟨List.nodup_nil, hc⟩
    · exact h.2 e (List.mem_of_mem_filter he)

omit [Fintype Validator] in
theorem SyncsOn.extend {s s₁ : State Validator BlockId Payload} (h : SyncsOn s)
    (hs : s₁.syncs.Sublist s.syncs) {u : Validator} {t : BlockId × Block Validator BlockId Payload}
    {A M : List BlockId} (he : (u, t, A) ∈ s.syncs) :
    SyncsOn { s₁ with
      syncs := s₁.syncs.map fun x => if x.1 = u then (u, t, (A ++ M).dedup) else x } := by
  have h₁ := h.sublist (s' := s₁) hs
  refine ⟨by simp only; rw [map_peers]; exact h₁.1, fun e he' => ?_⟩
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp he'
  split
  · exact ⟨List.nodup_dedup _, (h.2 _ he).2⟩
  · exact h₁.2 x hx

omit [Fintype Validator] [LinearOrder BlockId] in
theorem mem_extend
    {S : List (Validator × (BlockId × Block Validator BlockId Payload) × List BlockId)}
    {u w : Validator} {t t' : BlockId × Block Validator BlockId Payload} {asked A' : List BlockId}
    (h : (w, t', A') ∈ S.map fun x => if x.1 = u then (u, t, asked) else x) :
    (w = u ∧ t' = t ∧ A' = asked) ∨ (w ≠ u ∧ (w, t', A') ∈ S) := by
  obtain ⟨x, hx, hxe⟩ := List.mem_map.mp h
  split at hxe
  · simp only [Prod.mk.injEq] at hxe
    exact Or.inl ⟨hxe.1.symm, hxe.2.1.symm, hxe.2.2.symm⟩
  · rename_i hne
    subst hxe
    exact Or.inr ⟨hne, hx⟩

/-- **The syncs keep their shape.** -/
theorem SyncsOn.step {s : State Validator BlockId Payload} (h : SyncsOn s)
    (inp : Input Validator BlockId Payload) : SyncsOn (Node.step cfg s inp).1 := by
  rcases step_form (cfg := cfg) h inp with hp | ⟨u, id, b, rfl, -, hc, -, -, ht, -, -⟩ |
      ⟨u, L, t, A, rfl, he, -, ht, -, -⟩
  · exact h.sublist hp.thins.sub
  · exact (h.fresh hc).sublist ht.sub
  · exact (h.extend (Thins.takeIn s _ _).sub he).sublist ht.sub

/-- **Only evidence convicts an author.** -/
theorem EvidenceOn.step {s : State Validator BlockId Payload} (hs : SyncsOn s)
    (h : EvidenceOn cfg s) (inp : Input Validator BlockId Payload) :
    EvidenceOn cfg (Node.step cfg s inp).1 := by
  rcases step_form (cfg := cfg) hs inp with hp | ⟨u, id, b, rfl, -, -, -, -, ht, -, -⟩ |
      ⟨u, L, t, A, rfl, -, -, ht, -, -⟩
  · exact hp.thins.twins h
  · exact ht.twins h
  · exact ht.twins ((Thins.takeIn s _ _).twins h)

/-- **A step keeps `Kept`** under a faithful payload source. -/
theorem Kept.step (hf : cfg.Faithful) {s : State Validator BlockId Payload} (hs : SyncsOn s)
    (h : Kept cfg s) (inp : Input Validator BlockId Payload) :
    Kept cfg (Node.step cfg s inp).1 := by
  rcases step_form (cfg := cfg) hs inp with hp | ⟨u, id, b, rfl, -, -, -, -, ht, -, -⟩ |
      ⟨u, L, t, A, rfl, -, -, ht, -, -⟩
  · exact hp.thins.holds hf h
  · exact ht.holds hf (h.of_eq rfl rfl)
  · exact ht.holds hf (((Thins.takeIn s _ _).holds hf h).of_eq rfl rfl)

/-- **A sync is kept by a step** unless its block is then held, its peer
detected, or the step delivers from its peer a block above its block. -/
theorem step_keeps {s : State Validator BlockId Payload} (hs : SyncsOn s) {w : Validator}
    {t : BlockId × Block Validator BlockId Payload} {A : List BlockId} (he : (w, t, A) ∈ s.syncs)
    (inp : Input Validator BlockId Payload) :
    t.1 ∈ (Node.step cfg s inp).1.disk.ids ∨ w ∈ (Node.step cfg s inp).1.detected ∨
      (∃ id b, inp = .deliver w id b ∧ id = cfg.idOf b ∧ b.creator = w ∧ t.2.round < b.round) ∨
      ∃ A', (w, t, A') ∈ (Node.step cfg s inp).1.syncs := by
  rcases step_form (cfg := cfg) hs inp with hp | ⟨u, id, b, rfl, hid, hc, -, hr, ht, -, -⟩ |
      ⟨u, L, t₀, A₀, rfl, he₀, hin, ht, -, -⟩
  · rcases hp.thins.kept _ he with h | h | h
    · exact Or.inr (Or.inr (Or.inr ⟨A, h⟩))
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · by_cases hwu : w = u
    · subst hwu
      exact Or.inr (Or.inr (Or.inl ⟨id, b, rfl, hid, hc, hr _ he rfl⟩))
    · have h₁ : (w, t, A) ∈ (u, (id, b), ([] : List BlockId)) ::
          (s.syncs.filter fun e => decide (e.1 ≠ u)) :=
        List.mem_cons_of_mem _ (List.mem_filter.mpr ⟨he, by simpa using hwu⟩)
      rcases ht.kept _ h₁ with h | h | h
      · exact Or.inr (Or.inr (Or.inr ⟨A, h⟩))
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
  · have h₁ := Thins.takeIn (cfg := cfg) s t₀ (inHistory cfg t₀ L)
    rcases h₁.kept _ he with h | h | h
    · by_cases hwu : w = u
      · subst hwu
        obtain ⟨-, rfl, -⟩ := Prod.mk.inj (hs.eq he he₀ rfl)
        rcases ht.kept _ (List.mem_map.mpr ⟨_, hin, if_pos rfl⟩) with h | h | h
        · exact Or.inr (Or.inr (Or.inr ⟨_, h⟩))
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
      · rcases ht.kept _ (List.mem_map.mpr ⟨_, h, if_neg hwu⟩) with h | h | h
        · exact Or.inr (Or.inr (Or.inr ⟨A, h⟩))
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
    · exact Or.inl (ht.grows.1 h)
    · exact Or.inr (Or.inl (ht.det h))

/-- **A sync after a step was asked for there, or was there before.** -/
theorem step_origin {s : State Validator BlockId Payload} (hs : SyncsOn s) {w : Validator}
    {t : BlockId × Block Validator BlockId Payload} {A' : List BlockId}
    {inp : Input Validator BlockId Payload} (he : (w, t, A') ∈ (Node.step cfg s inp).1.syncs) :
    (∃ fr ids, Output.sync w t.1 fr ids ∈ (Node.step cfg s inp).2) ∨ ∃ A, (w, t, A) ∈ s.syncs := by
  rcases step_form (cfg := cfg) hs inp with hp | ⟨u, id, b, rfl, -, -, -, -, ht, -, hreq⟩ |
      ⟨u, L, t₀, A₀, rfl, he₀, -, ht, -, -⟩
  · exact Or.inr ⟨A', hp.thins.sub.subset he⟩
  · rcases List.mem_cons.mp (ht.sub.subset he) with h | h
    · simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, -⟩ := h
      obtain ⟨fr, hfr⟩ := hreq
      exact Or.inl ⟨fr, [], hfr⟩
    · exact Or.inr ⟨A', List.mem_of_mem_filter h⟩
  · rcases mem_extend (ht.sub.subset he) with ⟨rfl, rfl, -⟩ | ⟨-, h⟩
    · exact Or.inr ⟨A₀, he₀⟩
    · exact Or.inr ⟨A', (Thins.takeIn s _ _).sub.subset h⟩

/-- **A request for a sync asks for its names after the step.** -/
theorem step_ask {s : State Validator BlockId Payload} (hs : SyncsOn s) {w : Validator}
    {t : BlockId × Block Validator BlockId Payload} {A' : List BlockId}
    {inp : Input Validator BlockId Payload} (he : (w, t, A') ∈ (Node.step cfg s inp).1.syncs)
    {fr : Validator → ℕ} {ids : List BlockId}
    (ho : Output.sync w t.1 fr ids ∈ (Node.step cfg s inp).2) : A' = ids := by
  rcases step_form (cfg := cfg) hs inp with hp | ⟨u, id, b, rfl, -, hc, -, -, ht, hask, -⟩ |
      ⟨u, L, t₀, A₀, rfl, he₀, hin, ht, hask, -⟩
  · obtain ⟨e, he₁, h₁, -, h₃⟩ := hp.asks _ _ _ _ ho
    rw [← h₃, hs.eq he₁ (hp.thins.sub.subset he) h₁]
  · obtain ⟨rfl, -, rfl⟩ := hask _ _ _ _ ho
    have := (hs.fresh (id := id) hc).eq (ht.sub.subset he) List.mem_cons_self rfl
    simp only [Prod.mk.injEq] at this
    exact this.2.2
  · obtain ⟨rfl, -, rfl⟩ := hask _ _ _ _ ho
    have hs₂ := hs.extend (s₁ := takeIn cfg s t₀ (inHistory cfg t₀ L))
      (M := missingIn (takeIn cfg s t₀ (inHistory cfg t₀ L)) (t₀ :: inHistory cfg t₀ L))
      (Thins.takeIn (cfg := cfg) s _ _).sub he₀
    have := hs₂.eq (ht.sub.subset he) (List.mem_map.mpr ⟨_, hin, if_pos rfl⟩) rfl
    simp only [Prod.mk.injEq] at this
    exact this.2.2

/-- **A sync's names after a step with no request for it are old ones.** -/
theorem step_same {s : State Validator BlockId Payload} (hs : SyncsOn s) {w : Validator}
    {t : BlockId × Block Validator BlockId Payload} {A A' : List BlockId}
    {inp : Input Validator BlockId Payload} (he : (w, t, A) ∈ s.syncs)
    (he' : (w, t, A') ∈ (Node.step cfg s inp).1.syncs)
    (hno : ∀ fr ids, Output.sync w t.1 fr ids ∉ (Node.step cfg s inp).2) : ∀ x ∈ A', x ∈ A := by
  rcases step_form (cfg := cfg) hs inp with hp | ⟨u, id, b, rfl, -, -, -, -, ht, -, -⟩ |
      ⟨u, L, t₀, A₀, rfl, he₀, -, ht, -, hmv⟩
  · have := hs.eq (hp.thins.sub.subset he') he rfl
    simp only [Prod.mk.injEq] at this
    rw [this.2.2]; exact fun x hx => hx
  · rcases List.mem_cons.mp (ht.sub.subset he') with h | h
    · simp only [Prod.mk.injEq] at h
      rw [h.2.2]; exact fun x hx => absurd hx List.not_mem_nil
    · have := hs.eq (List.mem_of_mem_filter h) he rfl
      simp only [Prod.mk.injEq] at this
      rw [this.2.2]; exact fun x hx => hx
  · rcases mem_extend (ht.sub.subset he') with ⟨rfl, rfl, rfl⟩ | ⟨-, h⟩
    · obtain ⟨-, -, rfl⟩ := Prod.mk.inj (Prod.mk.inj (hs.eq he he₀ rfl)).2
      have hlen := (hmv hno).2
      intro x hx
      rcases List.mem_append.mp (List.mem_dedup.mp hx) with hx | hx
      · exact hx
      · exact mem_of_dedup_length (hs.2 _ he).1 hlen hx
    · have := hs.eq ((Thins.takeIn s _ _).sub.subset h) he rfl
      simp only [Prod.mk.injEq] at this
      rw [this.2.2]; exact fun x hx => hx

/-- **A stream piece that leads to no request for its sync**, which keeps
it, is not taken in, and each reference of the sync's block or of the
piece's part in its history that neither the disk nor that part holds was
asked for by name. -/
theorem step_stream_stuck {s : State Validator BlockId Payload} (hs : SyncsOn s) {u : Validator}
    {t : BlockId × Block Validator BlockId Payload} {A : List BlockId} (he : (u, t, A) ∈ s.syncs)
    {L : List (BlockId × Block Validator BlockId Payload)}
    (hno : ∀ fr ids, Output.sync u t.1 fr ids ∉ (Node.step cfg s (.stream u L)).2)
    (hheld : t.1 ∉ (Node.step cfg s (.stream u L)).1.disk.ids)
    (hdet : u ∉ (Node.step cfg s (.stream u L)).1.detected) :
    t.1 ∉ (absorb cfg s (inHistory cfg t L)).disk.ids ∧
      ∀ x ∈ t :: inHistory cfg t L, ∀ y ∈ x.2.refs, y ∉ s.disk.ids →
        y ∉ (t :: inHistory cfg t L).map Prod.fst → y ∈ A := by
  have h₁ := Thins.takeIn (cfg := cfg) s t (inHistory cfg t L)
  rcases step_stream_cases (cfg := cfg) hs he L with ⟨hnin, h⟩ | ⟨hin, h⟩
  · rw [h] at hheld hdet
    rcases h₁.kept _ he with h' | h' | h'
    · exact absurd h' hnin
    · exact absurd ((Thins.settle _).grows.1 h') hheld
    · exact absurd ((Thins.settle _).det h') hdet
  · have hadm : t.1 ∉ (absorb cfg s (inHistory cfg t L)).disk.ids := by
      intro hc
      unfold takeIn at hin
      rw [if_pos hc] at hin
      have := (List.mem_filter.mp hin).2
      simp only [decide_eq_true_eq] at this
      exact this.1 hc
    have hs₁ : takeIn cfg s t (inHistory cfg t L) = s := by unfold takeIn; rw [if_neg hadm]
    rw [h, hs₁] at hno
    have hnm : (A ++ missingIn s (t :: inHistory cfg t L)).dedup.length = A.length := by
      by_contra hm
      exact hno _ _ (List.mem_append_left _
        (List.mem_ite_nil_right.mpr ⟨Or.inr hm, List.mem_singleton_self _⟩))
    refine ⟨hadm, fun x hx y hy hyn hyL => mem_of_dedup_length (hs.2 _ he).1 hnm ?_⟩
    unfold missingIn
    refine List.mem_dedup.mpr (List.mem_filter.mpr ⟨List.mem_flatMap.mpr
      ⟨x, hx, (Finset.mem_sort _).mpr hy⟩, ?_⟩)
    simpa [hyn] using hyL

/-- **No sync is with the node itself.** -/
theorem step_peer_ne {s : State Validator BlockId Payload} (hs : SyncsOn s)
    (hm : ∀ e ∈ s.syncs, e.1 ≠ cfg.me) (inp : Input Validator BlockId Payload) :
    ∀ e ∈ (Node.step cfg s inp).1.syncs, e.1 ≠ cfg.me := by
  rcases step_form (cfg := cfg) hs inp with hp | ⟨u, id, b, rfl, -, -, hme, -, ht, -, -⟩ |
      ⟨u, L, t, A, rfl, he, -, ht, -, -⟩
  · exact fun e he => hm e (hp.thins.sub.subset he)
  · intro e he
    rcases List.mem_cons.mp (ht.sub.subset he) with rfl | h
    · exact hme
    · exact hm e (List.mem_of_mem_filter h)
  · intro e he'
    obtain ⟨w, t', A'⟩ := e
    rcases mem_extend (ht.sub.subset he') with ⟨rfl, -, -⟩ | ⟨-, h⟩
    · exact hm (w, t, A) he
    · exact hm _ ((Thins.takeIn s _ _).sub.subset h)

/-- **A run keeps the syncs' shape, none with the node itself.** -/
theorem syncsOn_run : ∀ (is : List (Input Validator BlockId Payload))
    (s : State Validator BlockId Payload), SyncsOn s → (∀ e ∈ s.syncs, e.1 ≠ cfg.me) →
    SyncsOn (Node.run cfg s is).1 ∧ ∀ e ∈ (Node.run cfg s is).1.syncs, e.1 ≠ cfg.me
  | [], _, hs, hm => ⟨hs, hm⟩
  | i :: is, _, hs, hm => syncsOn_run is _ (hs.step i) (step_peer_ne hs hm i)

/-- **Syncs with distinct peers, none the node itself, number at most
`n − 1`.** -/
theorem syncs_length_le {s : State Validator BlockId Payload} (hs : SyncsOn s)
    (hm : ∀ e ∈ s.syncs, e.1 ≠ cfg.me) : s.syncs.length ≤ Fintype.card Validator - 1 := by
  have hsub : (s.syncs.map (·.1)).toFinset ⊆ Finset.univ.erase cfg.me := fun a ha => by
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
    exact Finset.mem_erase.mpr ⟨hm e he, Finset.mem_univ _⟩
  have := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup hs.1, List.length_map,
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ] at this
  exact this

end Node

end LeanDag
