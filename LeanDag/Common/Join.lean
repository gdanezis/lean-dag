import LeanDag.Common.Exclusion
/-!
# Joins of twins, certificates, and exposure in rounds

`docs/dos-bounds.md` §5, R1 to R3. A block `w` *joins* two blocks when both
lie in its history and in the history of no single reference of `w`
(`JoinsFrom`).

* **R1. Twins in one history are joined in it** (`exists_joinsFrom`): two
  blocks in a history are joined by a block of that history, above their round
  when they are distinct blocks of one round (`JoinsFrom.round_lt`).
* **R2. A certificate has `q − f` correct signers** (`card_signers_inter_le`).
  `CertifiedOn` asks a block that joins two twins for at least `q` signers and
  for their author among the authors it names.
* **R3. Exposure one round above a join** (`exposed_of_twins`): if each correct
  signer's block of the join's round exposes the named authors
  (`SignersExposeOn`), every block from one round above the join exposes the
  twins' author, since each block references `q` authors, one a correct signer
  when `n + f < 2q` (`correctBelow_of_card`). Under the DoS condition no block
  from that round on references the author (`not_mem_creators_refs_of_twins`).
-/

namespace LeanDag

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {blk : BlockId → Block Validator BlockId Payload} {ids : Finset BlockId}

/-- **`w` joins `x` and `y`**: both lie in its history, and in the history of no
single reference of `w`. -/
def JoinsFrom (blk : BlockId → Block Validator BlockId Payload) (w x y : BlockId) : Prop :=
  x ∈ historyFrom blk w ∧ y ∈ historyFrom blk w ∧
    ∀ j ∈ (blk w).refs, ¬ (x ∈ historyFrom blk j ∧ y ∈ historyFrom blk j)

omit [Fintype Validator] [DecidableEq Validator] in
/-- **R1. Two blocks in a history are joined in it.** -/
theorem exists_joinsFrom (C : CausalStructure blk ids) {x y : BlockId} :
    ∀ n, ∀ b ∈ ids, (blk b).round ≤ n → x ∈ historyFrom blk b → y ∈ historyFrom blk b →
      ∃ w ∈ historyFrom blk b, JoinsFrom blk w x y := by
  intro n
  induction n with
  | zero =>
      intro b hb hr hx hy
      refine ⟨b, mem_historyFrom_self, hx, hy, fun j hj _ => ?_⟩
      have := C.refs_round b hb j hj
      omega
  | succ n ih =>
      intro b hb hr hx hy
      by_cases h : ∃ j ∈ (blk b).refs, x ∈ historyFrom blk j ∧ y ∈ historyFrom blk j
      · obtain ⟨j, hj, hxj, hyj⟩ := h
        have hjr := C.refs_round b hb j hj
        obtain ⟨w, hw, hjw⟩ := ih j (C.complete b hb j hj) (by omega) hxj hyj
        exact ⟨w, C.history_subset_of_reaches hb (ReachesFrom.single hj) hw, hjw⟩
      · exact ⟨b, mem_historyFrom_self, hx, hy, fun j hj hxy => h ⟨j, hj, hxy⟩⟩

omit [Fintype Validator] [DecidableEq Validator] in
/-- A block that joins two distinct blocks of one round lies above them. -/
theorem JoinsFrom.round_lt (C : CausalStructure blk ids) {w x y : BlockId} (hw : w ∈ ids)
    (h : JoinsFrom blk w x y) (hxy : x ≠ y) (hr : (blk x).round = (blk y).round) :
    (blk x).round < (blk w).round := by
  have hx := C.round_le_of_mem_history hw h.1
  refine lt_of_le_of_ne hx fun he => hxy ?_
  rw [C.eq_of_mem_history_of_round_eq hw h.1 he,
    C.eq_of_mem_history_of_round_eq hw h.2.1 (hr ▸ he)]

/-- **A certified record**: a block that joins two twins has at least `q`
signers, `sig w`, and names their author among `named w`. -/
def CertifiedOn (blk : BlockId → Block Validator BlockId Payload) (ids : Finset BlockId)
    (q : ℕ) (sig named : BlockId → Finset Validator) : Prop :=
  ∀ w ∈ ids, ∀ x y, x ≠ y → (blk x).creator = (blk y).creator →
    (blk x).round = (blk y).round → JoinsFrom blk w x y →
      q ≤ (sig w).card ∧ (blk x).creator ∈ named w

/-- **Signers expose**: a block of a signer of `w` in `T`, at the round of `w`,
exposes every author `w` names. -/
def SignersExposeOn (blk : BlockId → Block Validator BlockId Payload) (ids : Finset BlockId)
    (T : Finset Validator) (sig named : BlockId → Finset Validator)
    (Exp : BlockId → Validator → Prop) : Prop :=
  ∀ w ∈ ids, ∀ c ∈ ids, (blk c).creator ∈ sig w ∩ T → (blk c).round = (blk w).round →
    ∀ X ∈ named w, Exp c X

omit [DecidableEq BlockId] in
/-- **R2. A certificate has `q − f` signers in `T`**, when at most `f` nodes lie
outside `T`. -/
theorem card_signers_inter_le {S T : Finset Validator} {q f : ℕ} (hS : q ≤ S.card)
    (hT : Tᶜ.card ≤ f) : q - f ≤ (S ∩ T).card := by
  have h := Finset.card_sdiff_add_card_inter S T
  have : (S \ T).card ≤ Tᶜ.card :=
    Finset.card_le_card fun v hv => Finset.mem_compl.mpr (Finset.mem_sdiff.mp hv).2
  omega

omit [DecidableEq BlockId] in
/-- **A block of `T` one round below every block**, when every block above round
`0` references `q` authors and `n < q + |T|`. -/
theorem correctBelow_of_card (C : CausalStructure blk ids) {q : ℕ}
    (hq : ∀ b ∈ ids, 0 < (blk b).round → q ≤ (creatorsOf blk (blk b).refs).card)
    {T : Finset Validator} (hT : Fintype.card Validator < q + T.card) :
    CorrectBelow blk ids T := by
  intro b hb hr
  obtain ⟨v, hv⟩ : (creatorsOf blk (blk b).refs ∩ T).Nonempty := by
    rw [← Finset.not_disjoint_iff_nonempty_inter]
    intro hd
    have := Finset.card_union_of_disjoint hd
    have := Finset.card_le_univ (creatorsOf blk (blk b).refs ∪ T)
    have := hq b hb hr
    omega
  obtain ⟨hvA, hvT⟩ := Finset.mem_inter.mp hv
  obtain ⟨i, hi, rfl⟩ := mem_creatorsOf.mp hvA
  exact ⟨i, hi, C.complete b hb i hi, hvT, C.refs_round b hb i hi⟩

/-- **R3. Exposure one round above a join.** Two twins in the history of `b` are
joined by a block `w` of that history above their round, and every block from
round `round w + 1` on exposes their author. -/
theorem exposed_of_twins (C : CausalStructure blk ids) {q f : ℕ}
    (hq : ∀ b ∈ ids, 0 < (blk b).round → q ≤ (creatorsOf blk (blk b).refs).card)
    {sig named : BlockId → Finset Validator} {T : Finset Validator}
    {Exp : BlockId → Validator → Prop} (hcert : CertifiedOn blk ids q sig named)
    (hsig : SignersExposeOn blk ids T sig named Exp) (hup : InheritedOn blk ids Exp)
    (hT : Tᶜ.card ≤ f) (hn : Fintype.card Validator + f < 2 * q)
    {b x y : BlockId} (hb : b ∈ ids) (hx : x ∈ historyFrom blk b) (hy : y ∈ historyFrom blk b)
    (hxy : x ≠ y) (hc : (blk x).creator = (blk y).creator)
    (hr : (blk x).round = (blk y).round) :
    ∃ w ∈ historyFrom blk b, (blk x).round < (blk w).round ∧
      ∀ c ∈ ids, (blk w).round + 1 ≤ (blk c).round → Exp c (blk x).creator := by
  obtain ⟨w, hw, hj⟩ := exists_joinsFrom C _ b hb le_rfl hx hy
  have hwi := C.history_subset_ids hb hw
  have hlt := hj.round_lt C hwi hxy hr
  obtain ⟨hS, hX⟩ := hcert w hwi x y hxy hc hr hj
  have hST := card_signers_inter_le hS hT
  have hbelow := correctBelow_of_card C hq (T := sig w ∩ T) (by omega)
  refine ⟨w, hw, hlt, fun c hc' hcr => ?_⟩
  have hexp : ∀ c ∈ ids, (blk c).round = ((blk w).round - 1) + 1 →
      (blk c).creator ∈ sig w ∩ T → Exp c (blk x).creator :=
    fun c hc hcr hcT => hsig w hwi c hc hcT (by omega) _ hX
  exact exposed_of_correct_exposed hbelow hup hexp ((blk c).round - (blk w).round - 1) c hc'
    (by omega)

/-- **No reference to a twin's author from one round above its join**, under the
DoS condition. -/
theorem not_mem_creators_refs_of_twins (C : CausalStructure blk ids) {q f : ℕ}
    (hq : ∀ b ∈ ids, 0 < (blk b).round → q ≤ (creatorsOf blk (blk b).refs).card)
    {sig named : BlockId → Finset Validator} {T : Finset Validator}
    {Exp : BlockId → Validator → Prop} (hcert : CertifiedOn blk ids q sig named)
    (hsig : SignersExposeOn blk ids T sig named Exp) (hup : InheritedOn blk ids Exp)
    (hdos : DoSValidOn blk ids Exp) (hT : Tᶜ.card ≤ f) (hn : Fintype.card Validator + f < 2 * q)
    {b x y : BlockId} (hb : b ∈ ids) (hx : x ∈ historyFrom blk b) (hy : y ∈ historyFrom blk b)
    (hxy : x ≠ y) (hc : (blk x).creator = (blk y).creator)
    (hr : (blk x).round = (blk y).round) :
    ∃ w ∈ historyFrom blk b, (blk x).round < (blk w).round ∧
      ∀ c ∈ ids, (blk w).round + 1 ≤ (blk c).round →
        (blk x).creator ∉ creatorsOf blk (blk c).refs := by
  obtain ⟨w, hw, hlt, hexp⟩ := exposed_of_twins C hq hcert hsig hup hT hn hb hx hy hxy hc hr
  refine ⟨w, hw, hlt, fun c hc' hcr hX => ?_⟩
  obtain ⟨i, hi, hiX⟩ := mem_creatorsOf.mp hX
  exact hdos c hc' i hi (hiX ▸ hexp c hc' hcr)

end LeanDag
