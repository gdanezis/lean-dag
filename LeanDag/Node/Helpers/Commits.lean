import LeanDag.Node.Helpers.Grow
import LeanDag.Scheme.Loop.Proof
/-!
# A node's decisions are one call of the loop

On a record `U` the node's stores agree with (`Agrees`), the decisions a
node output so far are nothing, or `tryDecide` from slot `0` on a view
inside its store, scanned no further than its store allows
(`CommitInv`). A decision step appends `tryDecide` from the next slot on
the store's view, which `Resume` folds into one call; building and
collecting at a fixed horizon change nothing it reads.
-/

namespace LeanDag

namespace Node

open Scheme

variable {Validator BlockId Payload : Type} [Fintype Validator] [DecidableEq Validator]
variable [LinearOrder BlockId]
variable {cfg : Config Validator BlockId Payload}
variable {P : Validity Validator BlockId Payload} {H : Finset Validator}

/-- **A store agrees with a record**: its blocks are the record's, read
alike. -/
def Agrees (U : BlockRecord Validator BlockId Payload P H) (st : Store Validator BlockId Payload) :
    Prop :=
  st.ids ⊆ U.ids ∧ ∀ j ∈ st.ids, st.blk j = U.block j

omit [Fintype Validator] [DecidableEq Validator] in
theorem Agrees.of_grows {U : BlockRecord Validator BlockId Payload P H}
    {st st' : Store Validator BlockId Payload} (hg : Grows st st') (hb : st'.base = st.base)
    (h : Agrees U st') : Agrees U st :=
  ⟨((hg.2 hb).1).trans h.1, fun j hj => by rw [← hg.blk hb hj]; exact h.2 j ((hg.2 hb).1 hj)⟩

/-- The view a store agreeing with a record gives of it. -/
def Agrees.view {U : BlockRecord Validator BlockId Payload P H}
    {st : Store Validator BlockId Payload} (h : Agrees U st) : U.View where
  ids := st.ids
  subset_ids := h.1
  complete := fun i hi j hj => by rw [← h.2 i hi] at hj; exact st.complete i hi j hj

omit [Fintype Validator] [DecidableEq Validator] in
theorem topRound_mono {U : BlockRecord Validator BlockId Payload P H}
    {st st' : Store Validator BlockId Payload} (h : Agrees U st) (h' : Agrees U st')
    (hs : st.ids ⊆ st'.ids) : st.topRound ≤ st'.topRound := by
  unfold Store.topRound
  refine Finset.sup_le fun i hi => ?_
  rw [h.2 i hi, ← h'.2 i (hs hi)]
  exact Finset.le_sup (f := fun i => (st'.blk i).round) (hs hi)

omit [Fintype Validator] in
theorem decidable_mono {R R' : ℕ} (h : R ≤ R') : decidable cfg R ≤ decidable cfg R' := by
  unfold decidable
  split <;> split
  · exact le_rfl
  · exact Nat.zero_le _
  · omega
  · exact Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.div_le_div_right (by omega)) 1)

omit [Fintype Validator] [DecidableEq Validator] [LinearOrder BlockId] in
theorem commitsOf_append (a b : List (Output Validator BlockId Payload)) :
    commitsOf (a ++ b) = commitsOf a ++ commitsOf b :=
  List.filterMap_append

omit [Fintype Validator] in
theorem commitsOf_built (bs : List (BlockId × Block Validator BlockId Payload)) :
    commitsOf (built cfg bs) = [] := by
  induction bs with
  | nil => rfl
  | cons e bs ih =>
    simp only [built, List.flatMap_cons] at ih ⊢
    rw [commitsOf_append, ih]
    rfl

omit [Fintype Validator] [DecidableEq Validator] [LinearOrder BlockId] in
theorem commitsOf_map (ds : List (ℕ × Option BlockId)) :
    commitsOf (ds.map fun e => (Output.commit e.1 e.2 : Output Validator BlockId Payload)) =
      ds := by
  induction ds with
  | nil => rfl
  | cons e ds ih => simp only [List.map_cons, commitsOf, List.filterMap_cons] at ih ⊢; rw [ih]

variable [P.Mechanised]

variable (cfg) in
/-- **The decisions so far are one call of the loop**: nothing, or
`tryDecide` from slot `0` on a view inside the store, scanned no further
than the store allows; and the next slot is the one after them. -/
def CommitInv (U : BlockRecord Validator BlockId Payload P H) (s : State Validator BlockId Payload)
    (cs : List (ℕ × Option BlockId)) : Prop :=
  s.lo = cs.length ∧ (cs = [] ∨ ∃ (V : U.View) (N : ℕ), V.ids ⊆ s.store.ids ∧
    N + 1 ≤ decidable cfg s.store.topRound ∧
    cs = tryDecide (S := cfg.slots) cfg.p boundedSel U V 0 N)

variable {q f : ℕ} [P.Quorate q] {U : BlockRecord Validator BlockId Payload P H}

omit [Fintype Validator] in
/-- The invariant survives a change that grows the store at a fixed
horizon and keeps the next slot. -/
theorem CommitInv.grow {s s' : State Validator BlockId Payload} {cs : List (ℕ × Option BlockId)}
    (h : CommitInv cfg U s cs) (hlo : s'.lo = s.lo) (hg : Grows s.store s'.store)
    (hb : s'.store.base = s.store.base) (ha : Agrees U s.store) (ha' : Agrees U s'.store) :
    CommitInv cfg U s' cs := by
  refine ⟨hlo.trans h.1, ?_⟩
  rcases h.2 with h0 | ⟨V, N, hV, hN, hcs⟩
  · exact Or.inl h0
  · exact Or.inr ⟨V, N, hV.trans (hg.2 hb).1,
      hN.trans (decidable_mono (topRound_mono ha ha' (hg.2 hb).1)), hcs⟩

/-- **A decision step keeps the invariant.** -/
theorem CommitInv.decideStep (hσ : cfg.σ = boundedSel) (ht : cfg.p.Tolerates H f q)
    {s : State Validator BlockId Payload} {cs : List (ℕ × Option BlockId)}
    (h : CommitInv cfg U s cs) (ha : Agrees U s.store) :
    CommitInv cfg U (Node.decideStep cfg s).1 (cs ++ commitsOf (Node.decideStep cfg s).2) := by
  letI := cfg.slots
  have hw : 2 ≤ cfg.p.waveLength := by
    rcases ht.2.2 with ⟨-, hw, -⟩ | ⟨-, hw, -⟩ | ⟨-, hw, -⟩ | ⟨-, hw, -⟩ <;> omega
  have hT : ∀ lo N, tryDecide cfg.p cfg.σ s.store.toRecord s.store.view lo N =
      tryDecide cfg.p boundedSel U ha.view lo N := fun lo N => by
    rw [hσ]
    exact (ViewsAbove.of_boundedSel (R := 0) (U₁ := s.store.toRecord) (V₁ := s.store.view)
      (V₂ := ha.view) (fun _ hi _ => hi) (fun _ hi _ => ⟨hi, Nat.zero_le _⟩)
      (fun i hi _ => (congrArg Block.round (ha.2 i hi)).symm)
      (fun i hi _ => (congrArg Block.creator (ha.2 i hi)).symm)
      (fun i hi _ => (congrArg Block.refs (ha.2 i hi)).symm)).tryDecide_eq cfg.p hw N (Nat.zero_le _)
  unfold Node.decideStep
  dsimp only
  split
  · rename_i hlt
    rw [commitsOf_map, hT]
    dsimp only
    refine ⟨?_, Or.inr ?_⟩
    · change s.lo + _ = _
      rw [List.length_append, h.1]
    rcases h.2 with h0 | ⟨V, N, hV, hN, hcs⟩
    · subst h0
      have hlo : s.lo = 0 := h.1
      refine ⟨ha.view, decidable cfg s.store.topRound - 1, subset_rfl,
        by change _ ≤ decidable cfg s.store.topRound; omega, ?_⟩
      rw [List.nil_append, hlo]
    · refine ⟨ha.view, decidable cfg s.store.topRound - 1, subset_rfl,
        by change _ ≤ decidable cfg s.store.topRound; omega, ?_⟩
      rw [h.1, hcs]
      have := Loop.resume _ _ _ P q H f cfg.p boundedSel U V ha.view 0 N
        (decidable cfg s.store.topRound - 1) ht hV (by omega)
      rw [Nat.zero_add] at this
      exact this
  · simpa [commitsOf] using h

omit [Fintype Validator] [P.Quorate q] in
/-- The invariant reads only the store and the next slot. -/
theorem CommitInv.congr {s s' : State Validator BlockId Payload} {cs : List (ℕ × Option BlockId)}
    (h : CommitInv cfg U s cs) (hlo : s'.lo = s.lo) (hst : s'.store = s.store) :
    CommitInv cfg U s' cs := by
  unfold CommitInv at h ⊢
  rw [hlo, hst]
  exact h

omit [Fintype Validator] in
/-- Building outputs only built blocks. -/
theorem progress_built : ∀ (fuel : ℕ) (s : State Validator BlockId Payload),
    ∃ bs, (Node.progress cfg fuel s).2 = built cfg bs
  | 0, _ => ⟨[], rfl⟩
  | fuel + 1, s => by
    unfold Node.progress
    split
    · rename_i s₁ out h
      obtain ⟨r, id, b, -, -, -, -, -, -, -, -, -, -, -, -, -, hout⟩ := tryBuild_some h
      obtain ⟨bs, hbs⟩ := progress_built fuel s₁
      exact ⟨(id, b) :: bs, by simp only [hout, hbs, built, List.flatMap_cons,
        List.flatMap_nil, List.append_nil]⟩
    · exact ⟨[], rfl⟩

/-- **Settling keeps the invariant**, at a fixed horizon. -/
theorem CommitInv.settle (hσ : cfg.σ = boundedSel) (ht : cfg.p.Tolerates H f q)
    {s : State Validator BlockId Payload} {cs : List (ℕ × Option BlockId)}
    (h : CommitInv cfg U s cs) (ha : Agrees U (Node.settle cfg s).1.store)
    (hb : (Node.settle cfg s).1.store.base = s.store.base) :
    CommitInv cfg U (Node.settle cfg s).1 (cs ++ commitsOf (Node.settle cfg s).2) := by
  obtain ⟨hg₁, hlo₁⟩ := Grows.progress (cfg := cfg) (s.store.topRound + 2) s
  obtain ⟨bs, hbs⟩ := progress_built (cfg := cfg) (s.store.topRound + 2) s
  simp only [Node.settle] at ha hb ⊢
  generalize Node.progress cfg (s.store.topRound + 2) s = r at hg₁ hlo₁ hbs ha hb ⊢
  have hd := decideStep_store (cfg := cfg) r.1
  generalize hgdef : Node.collect cfg (Node.decideStep cfg r.1).1 = g at ha hb ⊢
  have hgf := Grows.flush (cfg := cfg) (g.1.pending.length + 1) g.1.store g.1.pending
  have hc := collect_cases (cfg := cfg) (Node.decideStep cfg r.1).1
  rw [hgdef, hd] at hc
  rcases hc with hc | ⟨hcs, hcl, hco⟩
  · have := hg₁.1
    have := hgf.1
    change (flush cfg (g.1.pending.length + 1) g.1.store g.1.pending).1.base = s.store.base at hb
    omega
  · change (flush cfg (g.1.pending.length + 1) g.1.store g.1.pending).1.base = s.store.base at hb
    change Agrees U (flush cfg (g.1.pending.length + 1) g.1.store g.1.pending).1 at ha
    have hgr : Grows r.1.store (flush cfg (g.1.pending.length + 1) g.1.store g.1.pending).1 := by
      rw [← hcs]; exact hgf
    have hbr : r.1.store.base = s.store.base := by
      have := hg₁.1; have := hgr.1; omega
    have hfb := hb.trans hbr.symm
    have har : Agrees U r.1.store := Agrees.of_grows hgr hfb ha
    have ha₀ : Agrees U s.store := Agrees.of_grows hg₁ hbr har
    have h₁ : CommitInv cfg U r.1 cs := h.grow hlo₁ hg₁ hbr ha₀ har
    have h₂ := h₁.decideStep hσ ht (hd ▸ har)
    have hc : commitsOf (built cfg bs ++ (Node.decideStep cfg r.1).2 ++ g.2) =
        commitsOf (Node.decideStep cfg r.1).2 := by
      rw [hco, List.append_nil, commitsOf_append, commitsOf_built, List.nil_append]
    rw [hbs, hc]
    exact h₂.grow (hcl.trans rfl) (hd ▸ hgr) (by rw [hd]; exact hfb) (hd ▸ har) ha

/-- **A step keeps the invariant**, at a fixed horizon. -/
theorem CommitInv.step (hσ : cfg.σ = boundedSel) (ht : cfg.p.Tolerates H f q)
    {s : State Validator BlockId Payload} {cs : List (ℕ × Option BlockId)}
    (i : Input Validator BlockId Payload) (h : CommitInv cfg U s cs)
    (ha : Agrees U (Node.step cfg s i).1.store)
    (hb : (Node.step cfg s i).1.store.base = s.store.base) :
    CommitInv cfg U (Node.step cfg s i).1 (cs ++ commitsOf (Node.step cfg s i).2) := by
  have hgs := Grows.step (cfg := cfg) s i
  have ha₀ : Agrees U s.store := Agrees.of_grows hgs hb ha
  -- a step that settles a state `s₀` grown from `s`, after outputs without decisions
  have hset : ∀ (s₀ : State Validator BlockId Payload) (pre : List (Output Validator BlockId Payload)),
      s₀.lo = s.lo → Grows s.store s₀.store → s₀.store.base = s.store.base → commitsOf pre = [] →
      Node.step cfg s i = ((Node.settle cfg s₀).1, pre ++ (Node.settle cfg s₀).2) →
      CommitInv cfg U (Node.step cfg s i).1 (cs ++ commitsOf (Node.step cfg s i).2) := by
    intro s₀ pre hlo hg hb₀ hpre he
    rw [he] at ha hb ⊢
    have hge := Grows.settle_of (cfg := cfg) s₀ rfl
    have hbe : (Node.settle cfg s₀).1.store.base = s₀.store.base := hb.trans hb₀.symm
    have ha₁ : Agrees U s₀.store := Agrees.of_grows hge hbe ha
    have h₀ : CommitInv cfg U s₀ cs := h.grow hlo hg hb₀ ha₀ ha₁
    rw [commitsOf_append, hpre, List.nil_append]
    exact h₀.settle hσ ht ha hbe
  have hsame : Node.step cfg s i = (s, []) →
      CommitInv cfg U (Node.step cfg s i).1 (cs ++ commitsOf (Node.step cfg s i).2) := by
    intro he; rw [he]; simpa [commitsOf] using h
  cases i with
  | start =>
    by_cases h₁ : s.top = none ∧ cfg.Admissible
    · by_cases h₂ : cfg.idOf cfg.genesis ∉ s.store.ids ∧ s.store.base ≤ cfg.genesis.round ∧
          rowValid cfg.q (Function.update s.store.blk (cfg.idOf cfg.genesis) cfg.genesis)
            cfg.genesis
      · let st := s.store.insert _ _ h₂.1 h₂.2.1 (fun _ => Finset.empty_subset _)
          (fun _ j hj => absurd hj (Finset.notMem_empty j))
        refine hset { s with store := st, top := some 0, own := some (cfg.idOf cfg.genesis) }
          (built cfg [(cfg.idOf cfg.genesis, cfg.genesis)]) rfl (show Grows s.store st from Grows.insert _) rfl
          (commitsOf_built _) ?_
        simp only [Node.step, dif_pos h₂, if_pos h₁]
        rfl
      · exact hsame (by simp only [Node.step, dif_neg h₂, if_pos h₁])
    · exact hsame (by simp only [Node.step, if_neg h₁])
  | deliver id b =>
    by_cases hc : id = cfg.idOf b ∧ b.creator ≠ cfg.me ∧ s.store.base ≤ b.round ∧
        id ∉ s.store.ids ∧ id ∉ s.pending.map Prod.fst
    · let fl := flush cfg (s.pending.length + 1) s.store ((id, b) :: s.pending)
      let s₁ : State Validator BlockId Payload := { s with store := fl.1, pending := fl.2 }
      let miss := missing s₁ id b
      have hgf := Grows.flush (cfg := cfg) (s.pending.length + 1) s.store ((id, b) :: s.pending)
      refine hset { s₁ with requested := s₁.requested ++ miss.map fun x => (x.1, id, x.2) }
        (if miss.isEmpty then [] else [.fetch (miss.map Prod.fst)]) rfl hgf ?_ ?_ ?_
      · have hstep : (Node.step cfg s (.deliver id b)).1.store = (Node.settle cfg
            { s₁ with requested := s₁.requested ++ miss.map fun x => (x.1, id, x.2) }).1.store := by
          simp only [Node.step, if_pos hc]; rfl
        rw [hstep] at hb
        have h₁ := (Grows.settle_of (cfg := cfg)
          { s₁ with requested := s₁.requested ++ miss.map fun x => (x.1, id, x.2) } rfl).1
        rw [hb] at h₁
        exact le_antisymm h₁ hgf.1
      · split <;> rfl
      · simp only [Node.step, if_pos hc]; rfl
    · exact hsame (by simp only [Node.step, if_neg hc])
  | timer r =>
    exact hset { s with fired := insert r s.fired } [] rfl (Grows.refl _) rfl rfl
      (by simp only [Node.step]; rfl)
  | fetchRequest peer ids =>
    rw [show Node.step cfg s (.fetchRequest peer ids) = (s, answer s peer ids) from rfl]
    have : commitsOf (answer s peer ids) = [] := by
      unfold answer commitsOf
      rw [List.filterMap_map]
      exact List.filterMap_eq_nil_iff.mpr fun _ _ => rfl
    rw [this, List.append_nil]
    exact h
  | jump => exact hsame rfl
  | restart => exact hsame rfl
  | baseOffer => exact hsame rfl
  | baseRequest => exact hsame rfl

/-- **A run keeps the invariant**, while the horizon stays put. -/
theorem CommitInv.run (hσ : cfg.σ = boundedSel) (ht : cfg.p.Tolerates H f q) :
    ∀ (is : List (Input Validator BlockId Payload)) {s : State Validator BlockId Payload}
      {cs : List (ℕ × Option BlockId)}, CommitInv cfg U s cs →
      Agrees U (Node.run cfg s is).1.store → (Node.run cfg s is).1.store.base = s.store.base →
      CommitInv cfg U (Node.run cfg s is).1 (cs ++ commitsOf (Node.run cfg s is).2)
  | [], s, cs, h, _, _ => by simpa [Node.run, commitsOf] using h
  | i :: is, s, cs, h, ha, hb => by
    simp only [Node.run] at ha hb ⊢
    have hg₁ := Grows.step (cfg := cfg) s i
    have hg₂ := Grows.run (cfg := cfg) is (Node.step cfg s i).1
    have hb₁ : (Node.step cfg s i).1.store.base = s.store.base := by
      have := hg₁.1; have := hg₂.1; omega
    have hb₂ : (Node.run cfg (Node.step cfg s i).1 is).1.store.base =
        (Node.step cfg s i).1.store.base := hb.trans hb₁.symm
    have ha₁ := Agrees.of_grows hg₂ hb₂ ha
    have h₁ := h.step hσ ht i ha₁ hb₁
    have := CommitInv.run hσ ht is h₁ ha hb₂
    rw [commitsOf_append, ← List.append_assoc]
    exact this

end Node

end LeanDag
