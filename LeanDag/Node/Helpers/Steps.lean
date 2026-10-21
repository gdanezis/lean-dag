import LeanDag.Node.Helpers.Flush
/-!
# What one step does to pending, stored and requested blocks

On stores reading as a block map `g` at a horizon that does not rise, a
step keeps every block that fits pending or stored (`step_keeps`); a
block becomes pending only by being delivered (`pending_of_step`); a
request is recorded only on account of a block just delivered and not
dropped (`requested_of_step`); and a block of the node's own that the
step outputs is in the store after it (`step_persist`).
-/

namespace LeanDag

namespace Node

variable {Validator BlockId Payload : Type} [Fintype Validator] [DecidableEq Validator]
variable [LinearOrder BlockId]
variable {cfg : Config Validator BlockId Payload} {g : BlockId → Block Validator BlockId Payload}

omit [Fintype Validator] in
theorem tryBuild_pending {s s' : State Validator BlockId Payload}
    {out : List (Output Validator BlockId Payload)} (h : tryBuild cfg s = some (s', out)) :
    s'.pending = s.pending ∧ s'.requested = s.requested := by
  unfold tryBuild at h
  split at h
  · dsimp only at h
    split at h
    · split at h
      · rw [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        exact ⟨rfl, rfl⟩
      · exact absurd h (by simp)
    · exact absurd h (by simp)
  · exact absurd h (by simp)

omit [Fintype Validator] in
theorem progress_pending : ∀ (fuel : ℕ) (s : State Validator BlockId Payload),
    (Node.progress cfg fuel s).1.pending = s.pending ∧
      (Node.progress cfg fuel s).1.requested = s.requested
  | 0, _ => ⟨rfl, rfl⟩
  | fuel + 1, s => by
    unfold Node.progress
    split
    · rename_i s₁ out h
      have := tryBuild_pending h
      have ih := progress_pending fuel s₁
      exact ⟨ih.1.trans this.1, ih.2.trans this.2⟩
    · exact ⟨rfl, rfl⟩

omit [Fintype Validator] in
theorem decideStep_pending (s : State Validator BlockId Payload) :
    (Node.decideStep cfg s).1.pending = s.pending ∧
      (Node.decideStep cfg s).1.requested = s.requested := by
  unfold Node.decideStep
  dsimp only
  split
  all_goals
    obtain ⟨-, hpd, -, -, -, -, hrq, -⟩ := proposeAt_keeps (cfg := cfg) _
    exact ⟨hpd, hrq⟩

omit [Fintype Validator] in
/-- **Collecting at a horizon that does not rise changes nothing.** -/
theorem collect_eq (s : State Validator BlockId Payload)
    (h : (Node.collect cfg s).1.store.base = s.store.base) : Node.collect cfg s = (s, []) := by
  rcases hs : s.top with _ | t
  · simp only [Node.collect, hs]
  · by_cases hG : s.store.base < min (cfg.per * (min s.lo s.certHeight / cfg.m)) t - cfg.lag
    · exfalso
      simp only [Node.collect, hs, dif_pos hG] at h
      change min (cfg.per * (min s.lo s.certHeight / cfg.m)) t - cfg.lag = s.store.base at h
      omega
    · simp only [Node.collect, hs, dif_neg hG]

omit [Fintype Validator] in
theorem advance_keeps {s : State Validator BlockId Payload}
    (hR : ReadsAs g (Node.advance cfg s).1.store)
    (hb : (Node.advance cfg s).1.store.base = s.store.base)
    (hp : ∀ e ∈ s.pending, g e.1 = atBase 0 e.2) {y : BlockId × Block Validator BlockId Payload}
    (hf : Fits cfg g y) (hy : y ∈ s.pending ∨ y.1 ∈ s.store.ids) :
    y ∈ (Node.advance cfg s).1.pending ∨ y.1 ∈ (Node.advance cfg s).1.store.ids := by
  have hg₁ := (Grows.progress (cfg := cfg) (s.store.topRound + 2) s).1
  have hp₁ := (progress_pending (cfg := cfg) (s.store.topRound + 2) s).1
  simp only [Node.advance] at hR hb ⊢
  generalize Node.progress cfg (s.store.topRound + 2) s = r at hg₁ hp₁ hR hb ⊢
  have hd := decideStep_store (cfg := cfg) r.1
  have hdp := (decideStep_pending (cfg := cfg) r.1).1
  generalize Node.decideStep cfg r.1 = d at hd hdp hR hb ⊢
  have hgc := Grows.collect (cfg := cfg) d.1
  have hgf := Grows.flush (cfg := cfg) ((Node.collect cfg d.1).1.pending.length + 1)
    (Node.collect cfg d.1).1.store (Node.collect cfg d.1).1.pending
  change ReadsAs g (flush cfg ((Node.collect cfg d.1).1.pending.length + 1)
    (Node.collect cfg d.1).1.store (Node.collect cfg d.1).1.pending).1 at hR
  change (flush cfg ((Node.collect cfg d.1).1.pending.length + 1)
    (Node.collect cfg d.1).1.store (Node.collect cfg d.1).1.pending).1.base = s.store.base at hb
  have hdb : d.1.store.base = r.1.store.base := by rw [hd]
  have h1 := hg₁.1
  have h2 := hgc.1
  have h3 := hgf.1
  have hcb : (Node.collect cfg d.1).1.store.base = d.1.store.base := by omega
  have hbr : r.1.store.base = s.store.base := by omega
  have hce := collect_eq d.1 hcb
  have hfb : (flush cfg ((Node.collect cfg d.1).1.pending.length + 1)
      (Node.collect cfg d.1).1.store (Node.collect cfg d.1).1.pending).1.base =
      (Node.collect cfg d.1).1.store.base := by omega
  rw [hce] at hR hgf hfb ⊢
  dsimp only at hR hgf hfb ⊢
  have hbd := hfb
  have hRd : ReadsAs g d.1.store := ⟨by rw [← hbd]; exact hR.1, fun j hj => by
    rw [← hgf.blk hbd hj]; exact hR.2 j ((hgf.2 hbd).1 hj)⟩
  have hpd : ∀ e ∈ d.1.pending, g e.1 = atBase 0 e.2 := by rw [hdp, hp₁]; exact hp
  have hy' : y ∈ d.1.pending ∨ y.1 ∈ d.1.store.ids := by
    rw [hdp, hp₁, hd]
    rcases hy with hy | hy
    · exact Or.inl hy
    · exact Or.inr ((hg₁.2 hbr).1 hy)
  rcases hy' with hy' | hy'
  · exact flush_keeps _ hRd hpd hf hy'
  · exact Or.inr ((hgf.2 hbd).1 hy')

omit [Fintype Validator] in
/-- **A resume keeps the store, the pending blocks and the requests.** -/
theorem tryResume_keeps {s s₁ : State Validator BlockId Payload} (h : tryResume cfg s = some s₁) :
    s₁.store = s.store ∧ s₁.pending = s.pending ∧ s₁.requested = s.requested := by
  obtain ⟨-, -, -, -, -, -, hst, hpd, -, -, -, hrq, -⟩ := tryResume_some h
  exact ⟨hst, hpd, hrq⟩

omit [Fintype Validator] in
theorem flush_pending_sub : ∀ (fuel : ℕ) (st : Store Validator BlockId Payload)
    (pend : List (BlockId × Block Validator BlockId Payload)),
    ∀ e ∈ (Node.flush cfg fuel st pend).2, e ∈ pend
  | 0, _, _, _, he => he
  | fuel + 1, st, pend, e, he => by
    unfold Node.flush at he
    dsimp only at he
    split at he
    · exact he
    · rw [List.partition_eq_filter_filter] at he
      exact (List.mem_filter.mp (flush_pending_sub fuel _ _ e he)).1

omit [Fintype Validator] in
theorem collect_sub (s : State Validator BlockId Payload) :
    (∀ e ∈ (Node.collect cfg s).1.pending, e ∈ s.pending) ∧
      ∀ e ∈ (Node.collect cfg s).1.requested, e ∈ s.requested := by
  unfold Node.collect
  split
  · dsimp only
    split
    · exact ⟨fun e he => (List.mem_filter.mp he).1, fun e he => (List.mem_filter.mp he).1⟩
    · exact ⟨fun _ h => h, fun _ h => h⟩
  · exact ⟨fun _ h => h, fun _ h => h⟩

omit [Fintype Validator] in
theorem advance_sub (s : State Validator BlockId Payload) :
    (∀ e ∈ (Node.advance cfg s).1.pending, e ∈ s.pending) ∧
      ∀ e ∈ (Node.advance cfg s).1.requested, e ∈ s.requested := by
  have hp := progress_pending (cfg := cfg) (s.store.topRound + 2) s
  have hd := decideStep_pending (cfg := cfg) (Node.progress cfg (s.store.topRound + 2) s).1
  have hc := collect_sub (cfg := cfg)
    (Node.decideStep cfg (Node.progress cfg (s.store.topRound + 2) s).1).1
  refine ⟨fun e he => ?_, fun e he => ?_⟩
  · have := flush_pending_sub (cfg := cfg) _ _ _ e he
    have := hc.1 e this
    rwa [hd.1, hp.1] at this
  · have := hc.2 e he
    rwa [hd.2, hp.2] at this

omit [Fintype Validator] [DecidableEq Validator] in
/-- A store that grows at the same horizon into one reading as `g` reads
as `g`. -/
theorem ReadsAs.of_grows {st st' : Store Validator BlockId Payload} (h : ReadsAs g st')
    (hg : Grows st st') (hb : st'.base = st.base) : ReadsAs g st := by
  obtain ⟨hsub, hjk, hmap⟩ := hg.2 hb
  refine ⟨hb ▸ h.1, fun j hj => ?_⟩
  rw [← h.2 j (hsub hj)]
  simp only [Store.blk, lookup, hb, hmap j hj]

omit [Fintype Validator] in
/-- **A block that fits stays pending or stored across the passes**, at a
horizon that does not rise. -/
theorem quiesce_keeps : ∀ (n : ℕ) {s : State Validator BlockId Payload},
    ReadsAs g (quiesce cfg n s).1.store → (quiesce cfg n s).1.store.base = s.store.base →
    (∀ e ∈ s.pending, g e.1 = atBase 0 e.2) → ∀ {y : BlockId × Block Validator BlockId Payload},
    Fits cfg g y → (y ∈ s.pending ∨ y.1 ∈ s.store.ids) →
    y ∈ (quiesce cfg n s).1.pending ∨ y.1 ∈ (quiesce cfg n s).1.store.ids
  | 0, s, _, _, _, _, _, hy => hy
  | n + 1, s, hR, hb, hp, y, hf, hy => by
    rcases quiesce_succ_cases (cfg := cfg) n s with he | he <;> rw [he] at hR hb ⊢
    · exact advance_keeps hR hb hp hf hy
    · set a := (Node.advance cfg s).1
      have hga := Grows.quiesce (cfg := cfg) n a
      have hba : a.store.base = s.store.base :=
        le_antisymm (hb ▸ hga.1) (Grows.advance (cfg := cfg) s).1
      have hRa : ReadsAs g a.store := hR.of_grows hga (hb.trans hba.symm)
      exact quiesce_keeps n hR (hb.trans hba.symm)
        (fun e he => hp e ((advance_sub (cfg := cfg) s).1 e he)) hf
        (advance_keeps hRa hba hp hf hy)

omit [Fintype Validator] in
/-- **A block that fits stays pending or stored across a settle**, at a
horizon that does not rise. -/
theorem settle_keeps {s : State Validator BlockId Payload}
    (hR : ReadsAs g (Node.settle cfg s).1.store)
    (hb : (Node.settle cfg s).1.store.base = s.store.base)
    (hp : ∀ e ∈ s.pending, g e.1 = atBase 0 e.2) {y : BlockId × Block Validator BlockId Payload}
    (hf : Fits cfg g y) (hy : y ∈ s.pending ∨ y.1 ∈ s.store.ids) :
    y ∈ (Node.settle cfg s).1.pending ∨ y.1 ∈ (Node.settle cfg s).1.store.ids := by
  rcases settle_cases (cfg := cfg) s with h | ⟨s₁, hj, h⟩ <;> rw [h] at hR hb ⊢
  · exact quiesce_keeps _ hR hb hp hf hy
  · obtain ⟨hst, hpd, -⟩ := tryResume_keeps hj
    refine quiesce_keeps _ hR (by rw [hb, hst]) (by rw [hpd]; exact hp) hf ?_
    rw [hpd, hst]
    exact hy

omit [Fintype Validator] in
theorem quiesce_sub (n : ℕ) (s : State Validator BlockId Payload) :
    (∀ e ∈ (quiesce cfg n s).1.pending, e ∈ s.pending) ∧
      ∀ e ∈ (quiesce cfg n s).1.requested, e ∈ s.requested :=
  (quiesce_rel (P := fun _ => True)
    (R := fun a _ b => (∀ e ∈ b.pending, e ∈ a.pending) ∧ ∀ e ∈ b.requested, e ∈ a.requested)
    (fun _ => ⟨fun _ h => h, fun _ h => h⟩)
    (fun _ _ _ _ _ h₁ h₂ => ⟨fun e he => h₁.1 e (h₂.1 e he), fun e he => h₁.2 e (h₂.2 e he)⟩)
    (fun s _ => ⟨advance_sub s, trivial⟩) n s trivial).1

omit [Fintype Validator] in
/-- **A settle adds no pending block and records no request.** -/
theorem settle_sub (s : State Validator BlockId Payload) :
    (∀ e ∈ (Node.settle cfg s).1.pending, e ∈ s.pending) ∧
      ∀ e ∈ (Node.settle cfg s).1.requested, e ∈ s.requested := by
  rcases settle_cases (cfg := cfg) s with h | ⟨s₁, hj, h⟩ <;> rw [h]
  · exact quiesce_sub _ s
  · obtain ⟨-, hpd, hrq⟩ := tryResume_keeps hj
    have := quiesce_sub (cfg := cfg) (passes cfg s₁) s₁
    exact ⟨fun e he => hpd ▸ this.1 e he, fun e he => hrq ▸ this.2 e he⟩

variable (cfg) in
/-- **A delivery the node acts on**: identified by its hash, not the
node's own, at or above the horizon, new, and kept by the rate limiter. -/
def Admits (s : State Validator BlockId Payload) (id : BlockId)
    (b : Block Validator BlockId Payload) : Prop :=
  id = cfg.idOf b ∧ b.creator ≠ cfg.me ∧ s.store.base ≤ b.round ∧ id ∉ s.store.ids ∧
    id ∉ s.pending.map Prod.fst ∧ kept cfg s id b

/-- The state a delivery the node acts on settles: the store and pending
blocks after flushing, the slot the delivery is charged to, and its
author exposed if the node holds a twin of the block. -/
def afterFlush (s : State Validator BlockId Payload) (id : BlockId)
    (b : Block Validator BlockId Payload) : State Validator BlockId Payload :=
  let fl := flush cfg (s.pending.length + 1) s.store ((id, b) :: s.pending)
  let X := if twinned s b then insert b.creator s.exposed else s.exposed
  let s₀ := { s with store := fl.1, pending := fl.2, owner := charged cfg s id b ++ s.owner }
  { s₀ with exposed := X }

/-- The round a delivery leaves the node's last request for the bases on. -/
def askedAfter (s : State Validator BlockId Payload) (b : Block Validator BlockId Payload) : ℕ :=
  if s.recovering = true ∧ s.asked + cfg.lag + 2 ≤ b.round then b.round else s.asked

/-- The request for the bases a delivery sends, if any. -/
def askOut (s : State Validator BlockId Payload) (b : Block Validator BlockId Payload) :
    List (Output Validator BlockId Payload) :=
  if s.recovering = true ∧ s.asked + cfg.lag + 2 ≤ b.round then [.requestBase] else []

omit [Fintype Validator] in
theorem askOut_isQuiet {s : State Validator BlockId Payload} {b : Block Validator BlockId Payload} :
    ∀ o ∈ askOut (cfg := cfg) s b, o.isQuiet := by
  unfold askOut; split <;> simp [Output.isQuiet]

theorem step_deliver {s : State Validator BlockId Payload} {id : BlockId}
    {b : Block Validator BlockId Payload} (h : Admits cfg s id b) :
    let s₁ := afterFlush (cfg := cfg) s id b
    let miss := missing s₁ id b
    let s₂ := { s₁ with requested := s₁.requested ++ miss.map fun (x : BlockId × ℕ) => (x.1, id, x.2) }
    Node.step cfg s (.deliver id b) =
      ((Node.settle cfg { s₂ with asked := askedAfter (cfg := cfg) s b }).1,
        evidence s id b ++
          (if miss.isEmpty then [] else [.fetch b.creator s.store.base (miss.map Prod.fst)]) ++
          askOut (cfg := cfg) s b ++
          (Node.settle cfg { s₂ with asked := askedAfter (cfg := cfg) s b }).2) := by
  have h' : id = cfg.idOf b ∧ b.creator ≠ cfg.me ∧ s.store.base ≤ b.round ∧ id ∉ s.store.ids ∧
      id ∉ s.pending.map Prod.fst ∧ kept cfg s id b := h
  simp only [Node.step]
  rw [if_pos h']
  rfl

/-- The state with a peer's base offer recorded, in place of its last. -/
def withOffer (s : State Validator BlockId Payload) (p : Validator) (G : ℕ)
    (bs : List (BlockId × Block Validator BlockId Payload)) : State Validator BlockId Payload :=
  { s with offers := (p, G, bs) :: s.offers.filter fun o => o.1 ≠ p }

theorem step_offer {s : State Validator BlockId Payload} {p : Validator} {G : ℕ}
    {bs : List (BlockId × Block Validator BlockId Payload)} :
    Node.step cfg s (.baseOffer p G bs) =
      if s.recovering ∧ p ≠ cfg.me then bootFrom cfg (withOffer s p G bs) else (s, []) := rfl

/-- The state with a peer's certificate recorded. -/
def withCert (s : State Validator BlockId Payload) (c : Cert Validator BlockId)
    (ds : List (ℕ × Option BlockId)) : State Validator BlockId Payload :=
  { s with certs := (c, ds) :: s.certs }

theorem step_certOffer {s : State Validator BlockId Payload} {p : Validator}
    {c : Cert Validator BlockId} {ds : List (ℕ × Option BlockId)} :
    Node.step cfg s (.certOffer p c ds) =
      if s.recovering ∧ p ≠ cfg.me then bootFrom cfg (withCert s c ds)
      else if p ≠ cfg.me ∧ adoptable cfg s c (ds.filter fun e => s.lo ≤ e.1) then
        adopt cfg s c (ds.filter fun e => s.lo ≤ e.1)
      else if p ≠ cfg.me ∧ confirms cfg s c then confirm cfg s c
      else (s, []) := rfl

/-- **The cases of a certificate offer**: a recovering node records it and
tries to bootstrap; otherwise the node adopts decisions from a sublist of
those served, confirms the certificate, or does nothing. -/
theorem certOffer_cases (s : State Validator BlockId Payload) (p : Validator)
    (c : Cert Validator BlockId) (ds : List (ℕ × Option BlockId)) :
    (s.recovering ∧ p ≠ cfg.me ∧
      Node.step cfg s (.certOffer p c ds) = bootFrom cfg (withCert s c ds)) ∨
    (¬ (s.recovering ∧ p ≠ cfg.me) ∧ ∃ ds', ds'.Sublist ds ∧ p ≠ cfg.me ∧
      adoptable cfg s c ds' = true ∧ Node.step cfg s (.certOffer p c ds) = adopt cfg s c ds') ∨
    (¬ (s.recovering ∧ p ≠ cfg.me) ∧ p ≠ cfg.me ∧ confirms cfg s c = true ∧
      Node.step cfg s (.certOffer p c ds) = confirm cfg s c) ∨
    (¬ (s.recovering ∧ p ≠ cfg.me) ∧ Node.step cfg s (.certOffer p c ds) = (s, [])) := by
  rw [step_certOffer]
  by_cases h₁ : s.recovering ∧ p ≠ cfg.me
  · exact Or.inl ⟨h₁.1, h₁.2, if_pos h₁⟩
  rw [if_neg h₁]
  by_cases h₂ : p ≠ cfg.me ∧ adoptable cfg s c (ds.filter fun e => s.lo ≤ e.1) = true
  · exact Or.inr (Or.inl ⟨h₁, _, List.filter_sublist, h₂.1, h₂.2, if_pos h₂⟩)
  rw [if_neg h₂]
  by_cases h₃ : p ≠ cfg.me ∧ confirms cfg s c = true
  · exact Or.inr (Or.inr (Or.inl ⟨h₁, h₃.1, h₃.2, if_pos h₃⟩))
  exact Or.inr (Or.inr (Or.inr ⟨h₁, if_neg h₃⟩))

theorem step_announced {s : State Validator BlockId Payload} {p : Validator}
    {c : Cert Validator BlockId} :
    Node.step cfg s (.announced p c) =
      if s.recovering ∨ p = cfg.me then (s, [])
      else if confirms cfg s c then confirm cfg s c
      else if cfg.q ≤ c.signers.length ∧ s.lo < c.height then (s, [.requestDecisions p s.lo])
      else (s, []) := rfl

/-- **The cases of an announced certificate**: the node confirms it, asks
the sender for decisions, or does nothing; it confirms only when not
recovering. -/
theorem announced_cases (s : State Validator BlockId Payload) (p : Validator)
    (c : Cert Validator BlockId) :
    (s.recovering = false ∧ confirms cfg s c = true ∧
      Node.step cfg s (.announced p c) = confirm cfg s c) ∨
    Node.step cfg s (.announced p c) = (s, [.requestDecisions p s.lo]) ∨
    Node.step cfg s (.announced p c) = (s, []) := by
  rw [step_announced]
  split
  · exact Or.inr (Or.inr rfl)
  · rename_i h
    split
    · rename_i hc
      refine Or.inl ⟨?_, hc, rfl⟩
      cases hr : s.recovering
      · rfl
      · exact absurd (Or.inl hr) h
    · split
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)

theorem step_proposal {s : State Validator BlockId Payload} {p : Validator} {k : ℕ}
    {kh : BlockId} :
    Node.step cfg s (.proposal p k kh) =
      if p ≠ cfg.me then
        ((Node.settle cfg (seek cfg (record cfg s p k kh) k kh).1).1,
          (seek cfg (record cfg s p k kh) k kh).2 ++
            (Node.settle cfg (seek cfg (record cfg s p k kh) k kh).1).2)
      else (s, []) := rfl

theorem step_decisionRequest {s : State Validator BlockId Payload} {p : Validator} {lo : ℕ} :
    Node.step cfg s (.decisionRequest p lo) =
      (s, if p ≠ cfg.me then serveFrom s p lo else []) := rfl

/-- **An offer**: a base or a certificate. -/
def Input.isOffer : Input Validator BlockId Payload → Prop
  | .baseOffer .. => True
  | .certOffer .. => True
  | _ => False

omit [Fintype Validator] in
/-- **Trying to bootstrap** leaves the state alone, or bootstraps and
advances. -/
theorem bootFrom_cases (s : State Validator BlockId Payload) :
    bootFrom cfg s = (s, []) ∨ ∃ s₂ ads, tryBoot cfg s = some (s₂, ads) ∧
      bootFrom cfg s =
        ((advance cfg s₂).1, ads.map (fun e => .commit e.1 e.2) ++ (advance cfg s₂).2) := by
  unfold Node.bootFrom
  split
  · rename_i s₂ ads h; exact Or.inr ⟨s₂, ads, h, rfl⟩
  · exact Or.inl rfl

omit [Fintype Validator] in
/-- **A bootstrap raises the horizon**, past what advancing keeps: trying
to bootstrap at a horizon that does not rise leaves the state alone. -/
theorem bootFrom_of_base {s : State Validator BlockId Payload}
    (h : (bootFrom cfg s).1.store.base = s.store.base) : bootFrom cfg s = (s, []) := by
  rcases bootFrom_cases (cfg := cfg) s with he | ⟨s₂, ads, hb, he⟩
  · exact he
  · rw [he] at h
    have h₁ := boot_base hb
    have h₂ := (Grows.advance (cfg := cfg) s₂).1
    change (advance cfg s₂).1.store.base = s.store.base at h
    omega

/-- **Across a step a fitting block stays pending or stored**, on stores
reading as `g` at a horizon that does not rise. -/
theorem step_keeps {s : State Validator BlockId Payload} {inp : Input Validator BlockId Payload}
    (hR : ReadsAs g (Node.step cfg s inp).1.store)
    (hb : (Node.step cfg s inp).1.store.base = s.store.base)
    (hp : ∀ e ∈ s.pending, g e.1 = atBase 0 e.2)
    (hd : ∀ id b, inp = .deliver id b → id = cfg.idOf b → g id = atBase 0 b)
    (hr : inp ≠ .restart)
    {y : BlockId × Block Validator BlockId Payload} (hf : Fits cfg g y)
    (hy : y ∈ s.pending ∨ y.1 ∈ s.store.ids) :
    y ∈ (Node.step cfg s inp).1.pending ∨ y.1 ∈ (Node.step cfg s inp).1.store.ids := by
  have hgs := Grows.step (cfg := cfg) s inp
  have hRs : ReadsAs g s.store := ⟨by rw [← hb]; exact hR.1, fun j hj => by
    rw [← hgs.blk hb hj]; exact hR.2 j ((hgs.2 hb).1 hj)⟩
  -- a step that settles `s₀`, whose pending blocks read as `g` and which keeps `y`
  have hset : ∀ s₀ : State Validator BlockId Payload,
      Node.step cfg s inp = ((Node.settle cfg s₀).1, (Node.step cfg s inp).2) →
      Grows s.store s₀.store → s₀.store.base = s.store.base →
      (∀ e ∈ s₀.pending, g e.1 = atBase 0 e.2) → (y ∈ s₀.pending ∨ y.1 ∈ s₀.store.ids) →
      y ∈ (Node.step cfg s inp).1.pending ∨ y.1 ∈ (Node.step cfg s inp).1.store.ids := by
    intro s₀ he hg₀ hb₀ hp₀ hy₀
    rw [he] at hR hb ⊢
    exact settle_keeps hR (hb.trans hb₀.symm) hp₀ hf hy₀
  cases inp with
  | start =>
    by_cases h₁ : s.top = none ∧ cfg.Admissible
    · by_cases h₂ : cfg.idOf cfg.genesis ∉ s.store.ids ∧ s.store.base ≤ cfg.genesis.round ∧
          rowValid cfg.q (Function.update s.store.blk (cfg.idOf cfg.genesis) cfg.genesis)
            cfg.genesis
      · let st := s.store.insert _ _ h₂.1 h₂.2.1 (fun _ => Finset.empty_subset _)
          (fun _ j hj => absurd hj (Finset.notMem_empty j))
        let s₀ := { s with store := st, top := some 0, own := some (cfg.idOf cfg.genesis) }
        let s₀ := { s₀ with owner := slotted cfg [(cfg.idOf cfg.genesis, cfg.genesis)] ++ s.owner }
        refine hset { s₀ with recovering := false }
          ?_ (show Grows s.store st from Grows.insert _) rfl hp ?_
        · simp only [Node.step, dif_pos h₂, if_pos h₁]
          try rfl
        · rcases hy with hy | hy
          · exact Or.inl hy
          · exact Or.inr (Finset.mem_insert_of_mem hy)
      · simp only [Node.step, dif_neg h₂, if_pos h₁]; exact hy
    · simp only [Node.step, if_neg h₁]; exact hy
  | deliver id b =>
    by_cases hc : Admits cfg s id b
    · have hstep := step_deliver (cfg := cfg) hc
      let s₁ := afterFlush (cfg := cfg) s id b
      have hpb : ∀ e ∈ (id, b) :: s.pending, g e.1 = atBase 0 e.2 := by
        intro e he
        rcases List.mem_cons.mp he with rfl | he
        · exact hd _ _ rfl hc.1
        · exact hp e he
      have hfl := ReadsAs.flush (cfg := cfg) (s.pending.length + 1) hRs hpb
      let req := s₁.requested ++ (missing s₁ id b).map fun x => (x.1, id, x.2)
      refine hset { s₁ with requested := req, asked := askedAfter (cfg := cfg) s b } (by rw [hstep])
        (Grows.flush _ _ _) ?_ hfl.2 ?_
      · exact hfl.1.1.trans hRs.1.symm
      · rcases hy with hy | hy
        · exact flush_keeps _ hRs hpb hf (List.mem_cons_of_mem _ hy)
        · have hg := Grows.flush (cfg := cfg) (s.pending.length + 1) s.store ((id, b) :: s.pending)
          exact Or.inr ((hg.2 (hfl.1.1.trans hRs.1.symm)).1 hy)
    · have h' : ¬ (id = cfg.idOf b ∧ b.creator ≠ cfg.me ∧ s.store.base ≤ b.round ∧
          id ∉ s.store.ids ∧ id ∉ s.pending.map Prod.fst ∧ kept cfg s id b) := hc
      simp only [Node.step, if_neg h']; exact hy
  | timer r =>
    exact hset { s with fired := insert r s.fired } (by simp only [Node.step]) (Grows.refl _) rfl
      hp hy
  | fetchRequest peer G ids => exact hy
  | restart => exact absurd rfl hr
  | baseOffer p G bs =>
    rw [step_offer] at hR hb ⊢
    by_cases hc : s.recovering ∧ p ≠ cfg.me
    · rw [if_pos hc] at hb ⊢
      rw [bootFrom_of_base (s := withOffer s p G bs) hb]; exact hy
    · rw [if_neg hc]; exact hy
  | certOffer p c ds =>
    rcases certOffer_cases (cfg := cfg) s p c ds with ⟨-, -, he⟩ | ⟨-, ds', -, -, -, he⟩ |
      ⟨-, -, -, he⟩ | ⟨-, he⟩
    · rw [he] at hb ⊢
      rw [bootFrom_of_base (s := withCert s c ds) hb]; exact hy
    · exact hset (adopted s c ds') (by rw [he, adopt_eq]) (Grows.refl _) rfl hp hy
    · exact hset { s with cert := some c, props := above (some c) s.props } (by rw [he]; rfl)
        (Grows.refl _) rfl hp hy
    · rw [he]; exact hy
  | announced p c =>
    rcases announced_cases (cfg := cfg) s p c with ⟨-, -, he⟩ | he | he
    · exact hset { s with cert := some c, props := above (some c) s.props } (by rw [he]; rfl)
        (Grows.refl _) rfl hp hy
    · rw [he]; exact hy
    · rw [he]; exact hy
  | proposal p k kh =>
    by_cases hpm : p ≠ cfg.me
    · obtain ⟨n, hn⟩ := seek_eq (cfg := cfg) (record cfg s p k kh) k kh
      exact hset (seek cfg (record cfg s p k kh) k kh).1 (by rw [step_proposal, if_pos hpm])
        (by rw [hn]; exact Grows.refl _) (by rw [hn]; rfl) (by rw [hn]; exact hp)
        (by rw [hn]; exact hy)
    · rw [step_proposal, if_neg hpm]; exact hy
  | baseRequest => exact hy
  | decisionRequest => exact hy

omit [Fintype Validator] in
/-- **Trying to bootstrap adds pending blocks only from the offers**, and
records no request. -/
theorem bootFrom_sub (s₁ : State Validator BlockId Payload) {s : State Validator BlockId Payload}
    {inp : Input Validator BlockId Payload}
    (hs : s₁.pending = s.pending ∧ s₁.requested = s.requested)
    (hi : inp.isOffer) :
    (∀ e ∈ (bootFrom cfg s₁).1.pending, e ∈ s.pending ∨
      (inp = .deliver e.1 e.2 ∧ Admits cfg s e.1 e.2) ∨ inp.isOffer) ∧
    ∀ e ∈ (bootFrom cfg s₁).1.requested, e ∈ s.requested ∨
      ∃ b, inp = .deliver e.2.1 b ∧ Admits cfg s e.2.1 b := by
  rcases bootFrom_cases (cfg := cfg) s₁ with he | ⟨s₂, ads, hbt, he⟩ <;> rw [he]
  · exact ⟨fun e h => Or.inl (hs.1 ▸ h), fun e h => Or.inl (hs.2 ▸ h)⟩
  · obtain ⟨t, G, c, ds, hb, -, -, -, -, -, -, -, -, -, -, -, hrq, -⟩ := tryBoot_some hbt
    have ha := advance_sub (cfg := cfg) s₂
    refine ⟨fun e _ => Or.inr (Or.inr hi), fun e h => Or.inl ?_⟩
    have he₂ := ha.2 e h
    rw [hrq] at he₂
    exact hs.2 ▸ (List.mem_filter.mp he₂).1

/-- **A block becomes pending only by being delivered**, and only when the
node acts on the delivery; a request is recorded only on account of such
a delivery. -/
theorem step_sub (s : State Validator BlockId Payload) (inp : Input Validator BlockId Payload) :
    (∀ e ∈ (Node.step cfg s inp).1.pending, e ∈ s.pending ∨
      (inp = .deliver e.1 e.2 ∧ Admits cfg s e.1 e.2) ∨ inp.isOffer) ∧
    ∀ e ∈ (Node.step cfg s inp).1.requested, e ∈ s.requested ∨
      ∃ b, inp = .deliver e.2.1 b ∧ Admits cfg s e.2.1 b := by
  cases inp with
  | start =>
    by_cases h₁ : s.top = none ∧ cfg.Admissible
    · by_cases h₂ : cfg.idOf cfg.genesis ∉ s.store.ids ∧ s.store.base ≤ cfg.genesis.round ∧
          rowValid cfg.q (Function.update s.store.blk (cfg.idOf cfg.genesis) cfg.genesis)
            cfg.genesis
      · simp only [Node.step, dif_pos h₂, if_pos h₁]
        let st := s.store.insert _ _ h₂.1 h₂.2.1 (fun _ => Finset.empty_subset _)
          (fun _ j hj => absurd hj (Finset.notMem_empty j))
        let s₀ : State Validator BlockId Payload :=
          { s with store := st, top := some 0, own := some (cfg.idOf cfg.genesis) }
        let s₀ := { s₀ with owner := slotted cfg [(cfg.idOf cfg.genesis, cfg.genesis)] ++ s.owner }
        have := settle_sub (cfg := cfg) { s₀ with recovering := false }
        exact ⟨fun e he => Or.inl (this.1 e he), fun e he => Or.inl (this.2 e he)⟩
      · simp only [Node.step, dif_neg h₂, if_pos h₁]
        exact ⟨fun e he => Or.inl he, fun e he => Or.inl he⟩
    · simp only [Node.step, if_neg h₁]
      exact ⟨fun e he => Or.inl he, fun e he => Or.inl he⟩
  | deliver id b =>
    by_cases hc : Admits cfg s id b
    · rw [step_deliver hc]
      dsimp only
      let s₁ := afterFlush (cfg := cfg) s id b
      let req := s₁.requested ++ (missing s₁ id b).map fun x => (x.1, id, x.2)
      have := settle_sub (cfg := cfg) { s₁ with requested := req, asked := askedAfter (cfg := cfg) s b }
      refine ⟨fun e he => ?_, fun e he => ?_⟩
      · have hm := flush_pending_sub (cfg := cfg) _ _ _ e (this.1 e he)
        rcases List.mem_cons.mp hm with rfl | hm
        · exact Or.inr (Or.inl ⟨rfl, hc⟩)
        · exact Or.inl hm
      · rcases List.mem_append.mp (this.2 e he) with he | he
        · exact Or.inl he
        · obtain ⟨x, -, rfl⟩ := List.mem_map.mp he
          exact Or.inr ⟨b, rfl, hc⟩
    · have h' : ¬ (id = cfg.idOf b ∧ b.creator ≠ cfg.me ∧ s.store.base ≤ b.round ∧
          id ∉ s.store.ids ∧ id ∉ s.pending.map Prod.fst ∧ kept cfg s id b) := hc
      simp only [Node.step, if_neg h']
      exact ⟨fun e he => Or.inl he, fun e he => Or.inl he⟩
  | timer r =>
    have := settle_sub (cfg := cfg) { s with fired := insert r s.fired }
    exact ⟨fun e he => Or.inl (this.1 e he), fun e he => Or.inl (this.2 e he)⟩
  | restart =>
    have := settle_sub (cfg := cfg) s.recover
    exact ⟨fun e he => absurd (this.1 e he) (by simp [State.recover]),
      fun e he => absurd (this.2 e he) (by simp [State.recover])⟩
  | baseOffer p G bs =>
    rw [step_offer]
    by_cases hc : s.recovering ∧ p ≠ cfg.me
    · rw [if_pos hc]
      exact bootFrom_sub (s := s) (withOffer s p G bs) ⟨rfl, rfl⟩ trivial
    · rw [if_neg hc]; exact ⟨fun e he => Or.inl he, fun e he => Or.inl he⟩
  | certOffer p c ds =>
    rcases certOffer_cases (cfg := cfg) s p c ds with ⟨-, -, he⟩ | ⟨-, ds', -, -, -, he⟩ |
      ⟨-, -, -, he⟩ | ⟨-, he⟩ <;> rw [he]
    · exact bootFrom_sub (s := s) (withCert s c ds) ⟨rfl, rfl⟩ trivial
    · rw [adopt_eq]
      have := settle_sub (cfg := cfg) (adopted s c ds')
      exact ⟨fun e he => Or.inl (this.1 e he), fun e he => Or.inl (this.2 e he)⟩
    · have := settle_sub (cfg := cfg) { s with cert := some c, props := above (some c) s.props }
      exact ⟨fun e he => Or.inl (this.1 e he), fun e he => Or.inl (this.2 e he)⟩
    · exact ⟨fun e he => Or.inl he, fun e he => Or.inl he⟩
  | announced p c =>
    rcases announced_cases (cfg := cfg) s p c with ⟨-, -, he⟩ | he | he <;> rw [he]
    · have := settle_sub (cfg := cfg) { s with cert := some c, props := above (some c) s.props }
      exact ⟨fun e he => Or.inl (this.1 e he), fun e he => Or.inl (this.2 e he)⟩
    · exact ⟨fun e he => Or.inl he, fun e he => Or.inl he⟩
    · exact ⟨fun e he => Or.inl he, fun e he => Or.inl he⟩
  | proposal p k kh =>
    rw [step_proposal]
    split
    · obtain ⟨n, hn⟩ := seek_eq (cfg := cfg) (record cfg s p k kh) k kh
      rw [hn]
      have := settle_sub (cfg := cfg) { record cfg s p k kh with sought := n }
      exact ⟨fun e he => Or.inl (this.1 e he), fun e he => Or.inl (this.2 e he)⟩
    · exact ⟨fun e he => Or.inl he, fun e he => Or.inl he⟩
  | _ => exact ⟨fun e he => Or.inl he, fun e he => Or.inl he⟩

omit [Fintype Validator] in
theorem progress_base : ∀ (fuel : ℕ) (s : State Validator BlockId Payload),
    (Node.progress cfg fuel s).1.store.base = s.store.base
  | 0, _ => rfl
  | fuel + 1, s => by
    unfold Node.progress
    split
    · rename_i s₁ out h
      obtain ⟨_, _, _, _, _, _, _, -, -, -, -, -, hst, -, -, -, -⟩ := tryBuild_some h
      rw [progress_base fuel s₁, hst]
      rfl
    · rfl

omit [Fintype Validator] in
/-- **What building persists it stores.** -/
theorem progress_persist : ∀ (fuel : ℕ) (s : State Validator BlockId Payload),
    ∀ e ∈ persists (Node.progress cfg fuel s).2, e.1 ∈ (Node.progress cfg fuel s).1.store.ids ∧
      (Node.progress cfg fuel s).1.store.map.getD e.1 (Node.progress cfg fuel s).1.store.junk = e.2
  | 0, _, e, he => by simp [Node.progress, persists] at he
  | fuel + 1, s, e, he => by
    rcases hb : tryBuild cfg s with _ | ⟨s₁, out⟩
    · simp [Node.progress, hb, persists] at he
    · simp only [Node.progress, hb] at he ⊢
      obtain ⟨r, id, b, hnew, hab, hrefs, hpred, -, -, -, -, -, hst, -, -, -, hout⟩ :=
        tryBuild_some hb
      have hg := (Grows.progress (cfg := cfg) fuel s₁).1
      have hbs : (Node.progress cfg fuel s₁).1.store.base = s₁.store.base := progress_base fuel s₁
      rw [hout] at he
      simp only [built, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.cons_append,
        List.nil_append, persists, List.filterMap_cons] at he
      rcases List.mem_cons.mp he with rfl | he
      · have hin : id ∈ s₁.store.ids := by rw [hst]; exact Finset.mem_insert_self _ _
        refine ⟨(hg.2 hbs).1 hin, ?_⟩
        rw [(hg.2 hbs).2.2 _ hin, hst]
        exact Std.TreeMap.getD_insert_self
      · exact progress_persist fuel s₁ e he

omit [Fintype Validator] [DecidableEq Validator] [LinearOrder BlockId] in
theorem persists_commits (ds : List (ℕ × Option BlockId)) :
    persists (ds.map fun e => (Output.commit e.1 e.2 : Output Validator BlockId Payload)) =
      [] := by
  induction ds with
  | nil => rfl
  | cons e ds ih => simp [persists]

omit [Fintype Validator] in
theorem decideStep_persist (s : State Validator BlockId Payload) :
    persists (Node.decideStep cfg s).2 = [] := by
  unfold Node.decideStep
  dsimp only
  split
  · exact ((out_quiet (quiet_commits _)).append (out_quiet (proposeAt_quiet _))).1
  · exact (out_quiet (proposeAt_quiet _)).1

omit [Fintype Validator] in
/-- **Collecting outputs** a prune and the announced certificate. -/
theorem collect_out (s : State Validator BlockId Payload) :
    ∀ o ∈ (Node.collect cfg s).2, (∃ G, o = .prune G) ∨ ∃ c, o = .announce c := by
  unfold Node.collect
  split
  · dsimp only
    split
    · intro o ho
      rcases List.mem_cons.mp ho with rfl | ho
      · exact Or.inl ⟨_, rfl⟩
      · obtain ⟨c, -, rfl⟩ := List.mem_map.mp ho; exact Or.inr ⟨c, rfl⟩
    · simp
  · simp

omit [Fintype Validator] in
theorem collect_persist (s : State Validator BlockId Payload) :
    persists (Node.collect cfg s).2 = [] :=
  List.filterMap_eq_nil_iff.mpr fun o ho => by
    rcases collect_out s o ho with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> rfl

omit [Fintype Validator] in
theorem advance_persist (s : State Validator BlockId Payload)
    (hb : (Node.advance cfg s).1.store.base = s.store.base) :
    ∀ e ∈ persists (Node.advance cfg s).2, e.1 ∈ (Node.advance cfg s).1.store.ids ∧
      (Node.advance cfg s).1.store.map.getD e.1 (Node.advance cfg s).1.store.junk = e.2 := by
  intro e he
  have hpb := progress_base (cfg := cfg) (s.store.topRound + 2) s
  have hp := progress_persist (cfg := cfg) (s.store.topRound + 2) s
  simp only [Node.advance] at he hb ⊢
  generalize Node.progress cfg (s.store.topRound + 2) s = r at hpb hp he hb ⊢
  rw [persists_append, persists_append, decideStep_persist, collect_persist, List.append_nil,
    List.append_nil] at he
  obtain ⟨hin, hval⟩ := hp e he
  have hd := decideStep_store (cfg := cfg) r.1
  have hgc := Grows.collect (cfg := cfg) (Node.decideStep cfg r.1).1
  rw [hd] at hgc
  generalize Node.collect cfg (Node.decideStep cfg r.1).1 = c at hgc hb ⊢
  have hgf := Grows.flush (cfg := cfg) (c.1.pending.length + 1) c.1.store c.1.pending
  have hg := hgc.trans hgf
  have hbe : (flush cfg (c.1.pending.length + 1) c.1.store c.1.pending).1.base =
      r.1.store.base := by
    change _ = s.store.base at hb; rw [hb, hpb]
  exact ⟨(hg.2 hbe).1 hin, by rw [(hg.2 hbe).2.2 _ hin]; exact hval⟩

omit [Fintype Validator] in
/-- **What the passes persist they store**, at a horizon that does not
rise. -/
theorem quiesce_persist : ∀ (n : ℕ) (s : State Validator BlockId Payload),
    (quiesce cfg n s).1.store.base = s.store.base →
    ∀ e ∈ persists (quiesce cfg n s).2, e.1 ∈ (quiesce cfg n s).1.store.ids ∧
      (quiesce cfg n s).1.store.map.getD e.1 (quiesce cfg n s).1.store.junk = e.2
  | 0, s, _ => by intro e he; simp [Node.quiesce, persists] at he
  | n + 1, s, hb => by
    rcases quiesce_succ_cases (cfg := cfg) n s with he | he <;> rw [he] at hb ⊢
    · exact advance_persist s hb
    · set a := (Node.advance cfg s).1
      have hga := Grows.quiesce (cfg := cfg) n a
      have hba : a.store.base = s.store.base :=
        le_antisymm (hb ▸ hga.1) (Grows.advance (cfg := cfg) s).1
      intro e he
      rw [persists_append] at he
      rcases List.mem_append.mp he with he | he
      · obtain ⟨hin, hval⟩ := advance_persist s hba e he
        obtain ⟨hsub, hjk, hmap⟩ := hga.2 (hb.trans hba.symm)
        exact ⟨hsub hin, by rw [hmap _ hin]; exact hval⟩
      · exact quiesce_persist n a (hb.trans hba.symm) e he

omit [Fintype Validator] in
/-- **What a settle persists it stores**, at a horizon that does not
rise. -/
theorem settle_persist (s : State Validator BlockId Payload)
    (hb : (Node.settle cfg s).1.store.base = s.store.base) :
    ∀ e ∈ persists (Node.settle cfg s).2, e.1 ∈ (Node.settle cfg s).1.store.ids ∧
      (Node.settle cfg s).1.store.map.getD e.1 (Node.settle cfg s).1.store.junk = e.2 := by
  rcases settle_cases (cfg := cfg) s with h | ⟨s₁, hj, h⟩ <;> rw [h] at hb ⊢
  · exact quiesce_persist _ s hb
  · exact quiesce_persist _ s₁ (by rw [hb, (tryResume_keeps hj).1])

omit [Fintype Validator] in
theorem settle_persist_of {s₀ : State Validator BlockId Payload}
    {pre : List (Output Validator BlockId Payload)}
    (hpre : persists pre = [] ∨ ∃ e₀, persists pre = [e₀] ∧ e₀.1 ∈ s₀.store.ids ∧
      s₀.store.map.getD e₀.1 s₀.store.junk = e₀.2)
    (hb : (Node.settle cfg s₀).1.store.base = s₀.store.base) :
    ∀ e ∈ persists (pre ++ (Node.settle cfg s₀).2), e.1 ∈ (Node.settle cfg s₀).1.store.ids ∧
      (Node.settle cfg s₀).1.store.map.getD e.1 (Node.settle cfg s₀).1.store.junk = e.2 := by
  intro e he
  rw [persists_append] at he
  rcases List.mem_append.mp he with he | he
  · rcases hpre with hpre | ⟨e₀, hpre, hin, hval⟩
    · rw [hpre] at he; exact absurd he (List.not_mem_nil)
    · rw [hpre, List.mem_singleton] at he
      subst he
      have hg := Grows.settle (cfg := cfg) s₀
      exact ⟨(hg.2 hb).1 hin, by rw [(hg.2 hb).2.2 _ hin]; exact hval⟩
  · exact settle_persist s₀ hb e he

/-- **What a step persists it stores**, at a horizon that does not rise. -/
theorem step_persist {s : State Validator BlockId Payload} {inp : Input Validator BlockId Payload}
    (hb : (Node.step cfg s inp).1.store.base = s.store.base) :
    ∀ e ∈ persists (Node.step cfg s inp).2, e.1 ∈ (Node.step cfg s inp).1.store.ids ∧
      (Node.step cfg s inp).1.store.map.getD e.1 (Node.step cfg s inp).1.store.junk = e.2 := by
  cases inp with
  | start =>
    by_cases h₁ : s.top = none ∧ cfg.Admissible
    · by_cases h₂ : cfg.idOf cfg.genesis ∉ s.store.ids ∧ s.store.base ≤ cfg.genesis.round ∧
          rowValid cfg.q (Function.update s.store.blk (cfg.idOf cfg.genesis) cfg.genesis)
            cfg.genesis
      · let st := s.store.insert _ _ h₂.1 h₂.2.1 (fun _ => Finset.empty_subset _)
          (fun _ j hj => absurd hj (Finset.notMem_empty j))
        let s₁ : State Validator BlockId Payload :=
          { s with store := st, top := some 0, own := some (cfg.idOf cfg.genesis) }
        let s₁ := { s₁ with owner := slotted cfg [(cfg.idOf cfg.genesis, cfg.genesis)] ++ s.owner }
        let s₀ : State Validator BlockId Payload := { s₁ with recovering := false }
        have he : Node.step cfg s .start =
            ((Node.settle cfg s₀).1, built cfg [(cfg.idOf cfg.genesis, cfg.genesis)] ++
              (Node.settle cfg s₀).2) := by
          simp only [Node.step, dif_pos h₂, if_pos h₁]; rfl
        rw [he] at hb ⊢
        refine settle_persist_of (Or.inr ⟨(cfg.idOf cfg.genesis, cfg.genesis), by
          simp [built, persists], Finset.mem_insert_self _ _, Std.TreeMap.getD_insert_self⟩) ?_
        exact hb.trans rfl
      · simp only [Node.step, dif_neg h₂, if_pos h₁]; simp [persists]
    · simp only [Node.step, if_neg h₁]; simp [persists]
  | deliver id b =>
    by_cases hc : Admits cfg s id b
    · rw [step_deliver hc] at hb ⊢
      dsimp only at hb ⊢
      refine settle_persist_of (Or.inl ?_) (hb.trans (flush_base _ _ _).symm)
      refine (out_quiet fun o ho => ?_).1
      rcases List.mem_append.mp ho with ho | ho
      · rcases List.mem_append.mp ho with ho | ho
        · exact evidence_isQuiet s id b o ho
        · split at ho
          · simp at ho
          · rw [List.mem_singleton] at ho; subst ho; rfl
      · exact askOut_isQuiet o ho
    · have h' : ¬ (id = cfg.idOf b ∧ b.creator ≠ cfg.me ∧ s.store.base ≤ b.round ∧
          id ∉ s.store.ids ∧ id ∉ s.pending.map Prod.fst ∧ kept cfg s id b) := hc
      simp only [Node.step, if_neg h']; simp [persists]
  | timer r =>
    exact settle_persist_of (s₀ := { s with fired := insert r s.fired }) (pre := []) (Or.inl rfl) hb
  | fetchRequest peer G ids =>
    intro e he
    change e ∈ persists (answer s peer G ids) at he
    unfold answer persists at he
    rw [List.filterMap_map] at he
    simp at he
  | restart => exact settle_persist_of (s₀ := s.recover) (pre := []) (Or.inl rfl) hb
  | baseOffer p G bs =>
    rw [step_offer] at hb ⊢
    by_cases hc : s.recovering ∧ p ≠ cfg.me
    · rw [if_pos hc] at hb ⊢
      rw [bootFrom_of_base (s := withOffer s p G bs) hb]; intro e he; simp [persists] at he
    · rw [if_neg hc]; intro e he; simp [persists] at he
  | certOffer p c ds =>
    rcases certOffer_cases (cfg := cfg) s p c ds with ⟨-, -, he⟩ | ⟨-, ds', -, -, -, he⟩ |
      ⟨-, -, -, he⟩ | ⟨-, he⟩ <;> rw [he] at hb ⊢
    · rw [bootFrom_of_base (s := withCert s c ds) hb]; intro e he; simp [persists] at he
    · rw [adopt_eq] at hb ⊢
      exact settle_persist_of (s₀ := adopted s c ds') (Or.inl (persists_commits ds')) hb
    · unfold confirm at hb ⊢
      simpa using settle_persist_of (pre := [])
        (s₀ := { s with cert := some c, props := above (some c) s.props }) (Or.inl rfl) hb
    · intro e he; simp [persists] at he
  | announced p c =>
    rcases announced_cases (cfg := cfg) s p c with ⟨-, -, he⟩ | he | he <;> rw [he] at hb ⊢
    · unfold confirm at hb ⊢
      simpa using settle_persist_of (pre := [])
        (s₀ := { s with cert := some c, props := above (some c) s.props }) (Or.inl rfl) hb
    · intro e he; simp [persists] at he
    · intro e he; simp [persists] at he
  | proposal p k kh =>
    by_cases hpm : p ≠ cfg.me
    · rw [step_proposal, if_pos hpm] at hb ⊢
      have hq := (out_quiet (xs := (seek cfg (record cfg s p k kh) k kh).2) fun o ho => by
        obtain ⟨_, _, rfl⟩ := seek_out (cfg := cfg) _ k kh o ho; rfl).1
      obtain ⟨n, hn⟩ := seek_eq (cfg := cfg) (record cfg s p k kh) k kh
      exact settle_persist_of (Or.inl hq) (by rw [hb, hn]; rfl)
    · rw [step_proposal, if_neg hpm]; intro e he; simp [persists] at he
  | decisionRequest p lo =>
    intro e he
    rw [step_decisionRequest] at he
    have hq := (out_quiet (xs := if p ≠ cfg.me then serveFrom s p lo else []) fun o ho => by
      split at ho
      · obtain ⟨_, _, rfl⟩ := serveFrom_out s p lo o ho; rfl
      · simp at ho).1
    rw [hq] at he; exact absurd he List.not_mem_nil
  | _ => intro e he; simp [Node.step, persists] at he

variable (cfg) in
/-- No pending block is ready. -/
def NoReady (s : State Validator BlockId Payload) : Prop :=
  ∀ e ∈ s.pending, ready cfg s.store e = false

omit [Fintype Validator] in
theorem noReady_quiesce : ∀ (n : ℕ) (s : State Validator BlockId Payload),
    NoReady cfg (quiesce cfg (n + 1) s).1
  | n, s => by
    rcases quiesce_succ_cases (cfg := cfg) n s with he | he <;> rw [he]
    · exact flush_no_ready _ _ _ (Nat.lt_succ_self _)
    · cases n with
      | zero => exact flush_no_ready _ _ _ (Nat.lt_succ_self _)
      | succ n => exact noReady_quiesce n _

omit [Fintype Validator] in
theorem noReady_settle (s : State Validator BlockId Payload) :
    NoReady cfg (Node.settle cfg s).1 := by
  rcases settle_cases (cfg := cfg) s with h | ⟨s₁, -, h⟩ <;> rw [h] <;> exact noReady_quiesce _ _

omit [Fintype Validator] in
theorem noReady_bootFrom {s s₁ : State Validator BlockId Payload} (h : NoReady cfg s)
    (hs : s₁.store = s.store ∧ s₁.pending = s.pending := by exact ⟨rfl, rfl⟩) :
    NoReady cfg (bootFrom cfg s₁).1 := by
  rcases bootFrom_cases (cfg := cfg) s₁ with he | ⟨s₂, ads, -, he⟩ <;> rw [he]
  · intro e he'; rw [hs.2] at he'; rw [hs.1]; exact h e he'
  · exact flush_no_ready _ _ _ (Nat.lt_succ_self _)

/-- **After every step no pending block is ready.** -/
theorem noReady_step {s : State Validator BlockId Payload} (h : NoReady cfg s)
    (inp : Input Validator BlockId Payload) : NoReady cfg (Node.step cfg s inp).1 := by
  cases inp with
  | start =>
    simp only [Node.step]
    split
    · split
      · exact noReady_settle _
      · exact h
    · exact h
  | deliver id b =>
    by_cases hc : Admits cfg s id b
    · rw [step_deliver hc]; exact noReady_settle _
    · have h' : ¬ (id = cfg.idOf b ∧ b.creator ≠ cfg.me ∧ s.store.base ≤ b.round ∧
          id ∉ s.store.ids ∧ id ∉ s.pending.map Prod.fst ∧ kept cfg s id b) := hc
      simp only [Node.step, if_neg h']; exact h
  | timer r => exact noReady_settle _
  | restart => exact noReady_settle _
  | baseOffer p G bs =>
    rw [step_offer]
    split
    · exact noReady_bootFrom h
    · exact h
  | certOffer p c ds =>
    rcases certOffer_cases (cfg := cfg) s p c ds with ⟨-, -, he⟩ | ⟨-, ds', -, -, -, he⟩ |
      ⟨-, -, -, he⟩ | ⟨-, he⟩ <;> rw [he]
    · exact noReady_bootFrom h
    · rw [adopt_eq]; exact noReady_settle _
    · exact noReady_settle _
    · exact h
  | announced p c =>
    rcases announced_cases (cfg := cfg) s p c with ⟨-, -, he⟩ | he | he <;> rw [he]
    · exact noReady_settle _
    · exact h
    · exact h
  | proposal p k kh =>
    rw [step_proposal]
    split
    · exact noReady_settle _
    · exact h
  | _ => exact h

/-- **A delivery the node acts on keeps a fitting block it delivers**
pending or stored. -/
theorem admit_keeps {s : State Validator BlockId Payload} {id : BlockId}
    {b : Block Validator BlockId Payload} (hc : Admits cfg s id b)
    (hR : ReadsAs g (Node.step cfg s (.deliver id b)).1.store)
    (hb : (Node.step cfg s (.deliver id b)).1.store.base = s.store.base)
    (hp : ∀ e ∈ s.pending, g e.1 = atBase 0 e.2) (hgb : g id = atBase 0 b)
    (hf : Fits cfg g (id, b)) :
    (id, b) ∈ (Node.step cfg s (.deliver id b)).1.pending ∨
      id ∈ (Node.step cfg s (.deliver id b)).1.store.ids := by
  have hgs := Grows.step (cfg := cfg) s (.deliver id b)
  have hRs : ReadsAs g s.store := ⟨by rw [← hb]; exact hR.1, fun j hj => by
    rw [← hgs.blk hb hj]; exact hR.2 j ((hgs.2 hb).1 hj)⟩
  have hstep := step_deliver (cfg := cfg) hc
  have hpb : ∀ e ∈ (id, b) :: s.pending, g e.1 = atBase 0 e.2 := by
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · exact hgb
    · exact hp e he
  have hfl := ReadsAs.flush (cfg := cfg) (s.pending.length + 1) hRs hpb
  have hk := flush_keeps (cfg := cfg) (s.pending.length + 1) hRs hpb hf List.mem_cons_self
  rw [hstep] at hR hb ⊢
  exact settle_keeps hR (hb.trans (flush_base _ _ _).symm) hfl.2 hf hk

end Node

end LeanDag
