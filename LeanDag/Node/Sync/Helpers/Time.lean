import LeanDag.Node.Sync.Model.Time
import LeanDag.Node.Sync.Helpers.Net
import LeanDag.Node.Sync.Helpers.Exposure
/-!
# Sync by causal streams — detection in time

A node never forgets a detection (`step_detected`, `detected_mono`), a
report of twins detects their author (`report_detects`), and an author
detected before an event was detected at an earlier one
(`exists_detectsAt`). Under reports within `Δ`, an author an honest node
detects at time `t` is detected by every honest node at every event
after `t + Δ` (`detected_after`), and every block an honest node builds
then exposes it (`exposes_after`). A disk holds the references of its
blocks (`run_closed`), so it holds their histories (`historyFrom_subset`).
-/

namespace LeanDag

namespace Node

namespace Sync

variable {Validator BlockId Payload : Type} [DecidableEq Validator] [LinearOrder BlockId]
variable {blk : BlockId → Block Validator BlockId Payload}
variable {ev : Payload → Finset (BlockId × BlockId)} [Fintype Validator] {f : ℕ}

/-- **A step keeps the detected authors.** -/
theorem step_detected {me : Validator} (s : State Validator BlockId)
    (inp : Input Validator BlockId) : s.detected ⊆ (step blk ev f me s inp).detected := by
  cases inp with
  | announce u t => simp only [step]; split_ifs <;> exact Finset.Subset.rfl
  | chunk u L =>
    simp only [step, settle]
    exact Finset.subset_union_left.trans Finset.subset_union_left
  | build x =>
    simp only [step]; split_ifs
    · exact Finset.subset_union_left
    · exact Finset.Subset.rfl
  | report i j =>
    simp only [step]; split_ifs
    · exact Finset.subset_insert _ _
    · exact Finset.Subset.rfl

/-- **One event keeps the detected authors.** -/
theorem detected_succ (tr : Trace Validator BlockId) (i : ℕ) (v : Validator) :
    (stateBefore blk ev f tr i v).detected ⊆ (stateBefore blk ev f tr (i + 1) v).detected := by
  rw [stateBefore_succ]
  split
  · split
    · exact step_detected _ _
    · exact Finset.Subset.rfl
  · exact Finset.Subset.rfl

/-- **Detection is permanent along a trace.** -/
theorem detected_mono (tr : Trace Validator BlockId) (v : Validator) {i j : ℕ} (hij : i ≤ j) :
    (stateBefore blk ev f tr i v).detected ⊆ (stateBefore blk ev f tr j v).detected := by
  induction j, hij using Nat.le_induction with
  | base => exact Finset.Subset.rfl
  | succ j _ ih => exact ih.trans (detected_succ tr j v)

/-- **A report of twins detects their author.** -/
theorem report_detects {tr : Trace Validator BlockId} {k : ℕ} {w : Validator} {a b : BlockId}
    (hk : tr[k]? = some (w, .report a b)) (hab : Twins blk a b) :
    (blk a).creator ∈ (stateBefore blk ev f tr (k + 1) w).detected := by
  rw [stateBefore_succ, hk]
  simp only [step, if_pos hab, settle]
  exact Finset.mem_insert_self _ _

/-- **A detection has a first event.** -/
theorem exists_detectsAt (tr : Trace Validator BlockId) (v X : Validator) :
    ∀ j, X ∈ (stateBefore blk ev f tr j v).detected → ∃ i < j, DetectsAt blk ev f tr i v X := by
  intro j
  induction j with
  | zero => intro h; simp [stateBefore_zero, State.init] at h
  | succ j ih =>
    intro h
    by_cases hj : X ∈ (stateBefore blk ev f tr j v).detected
    · obtain ⟨i, hi, hd⟩ := ih hj
      exact ⟨i, by omega, hd⟩
    · exact ⟨j, by omega, hj, h⟩

omit [Fintype Validator] in
/-- **A caught author has a pair the set shows.** -/
theorem exists_shownPairs_of_mem_caught {S : Finset BlockId} {X : Validator}
    (h : X ∈ caught blk ev S) :
    ∃ p ∈ shownPairs blk ev S, Twins blk p.1 p.2 ∧ (blk p.1).creator = X := by
  rcases Finset.mem_union.mp h with h | h
  · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp h
    obtain ⟨hiS, j, hjS, hij⟩ := Finset.mem_filter.mp hi
    exact ⟨(i, j), Finset.mem_union_left _ (Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨hiS, hjS⟩, hij⟩), hij, rfl⟩
  · obtain ⟨i, hiS, hi⟩ := Finset.mem_biUnion.mp h
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hi
    exact ⟨p, Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i, hiS, hp⟩),
      (Finset.mem_filter.mp hp).2, rfl⟩

omit [Fintype Validator] in
/-- **An exposed author has a pair the stream exposes.** -/
theorem exists_exposedPairs_of_mem_exposes {S : Finset BlockId} {L L' : List BlockId}
    {X : Validator} (hL : ∀ i ∈ L', i ∈ L) (h : X ∈ exposes blk S L') :
    ∃ p ∈ exposedPairs blk S L, Twins blk p.1 p.2 ∧ (blk p.1).creator = X := by
  unfold exposes at h
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp h)
  obtain ⟨hiL, hi'⟩ := List.mem_filter.mp hi
  simp only [decide_eq_true_eq] at hi'
  obtain ⟨hiS, j, hjS, hij⟩ := hi'
  exact ⟨(i, j), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
    ⟨List.mem_toFinset.mpr (hL i hiL), hjS⟩, hiS, hij⟩, hij, rfl⟩

/-- **A node reports each author it detects**: an author detected after a
step and not before has a pair of twins among the step's reports. -/
theorem exists_reports {me : Validator} {s : State Validator BlockId}
    {inp : Input Validator BlockId} {X : Validator} (hX : X ∉ s.detected)
    (hX' : X ∈ (step blk ev f me s inp).detected) :
    ∃ p ∈ reports blk ev f me s inp, (blk p.1).creator = X := by
  have key : ∀ {C : Finset (BlockId × BlockId)}, (∃ p ∈ C, Twins blk p.1 p.2 ∧
      (blk p.1).creator = X) →
      ∃ p ∈ C.filter (fun p => Twins blk p.1 p.2 ∧ (blk p.1).creator ∉ s.detected),
        (blk p.1).creator = X := fun ⟨p, hp, ht, hc⟩ =>
    ⟨p, Finset.mem_filter.mpr ⟨hp, ht, hc ▸ hX⟩, hc⟩
  cases inp with
  | announce u t =>
    simp only [step] at hX'
    split_ifs at hX' <;> exact absurd hX' hX
  | chunk u L =>
    apply key
    have hd := hX'
    simp only [step, settle] at hd
    rcases Finset.mem_union.mp hd with hd | hd
    · rcases Finset.mem_union.mp hd with hd | hd
      · exact absurd hd hX
      · obtain ⟨p, hp, h⟩ := exists_exposedPairs_of_mem_exposes
          (fun i hi => (List.mem_filter.mp hi).1) hd
        exact ⟨p, Finset.mem_union_left _ hp, h⟩
    · obtain ⟨p, hp, h⟩ := exists_shownPairs_of_mem_caught hd
      exact ⟨p, Finset.mem_union_right _ (by simpa [step, settle] using hp), h⟩
  | build x =>
    apply key
    by_cases hb : (blk x).creator = me ∧ Ready blk s.disk x ∧ Checks blk ev f x ∧
        ∀ X ∈ s.detected, Convicts blk ev x X
    · have hd := hX'
      simp only [step, if_pos hb, settle] at hd
      rcases Finset.mem_union.mp hd with hd | hd
      · exact absurd hd hX
      · obtain ⟨p, hp, h⟩ := exists_shownPairs_of_mem_caught hd
        exact ⟨p, by simpa [step, if_pos hb, settle] using hp, h⟩
    · simp only [step, if_neg hb] at hX'
      exact absurd hX' hX
  | report i j =>
    apply key
    by_cases hij : Twins blk i j
    · have hd := hX'
      simp only [step, if_pos hij, settle] at hd
      rcases Finset.mem_insert.mp hd with hd | hd
      · exact ⟨(i, j), Finset.mem_singleton_self _, hij, hd.symm⟩
      · exact absurd hd hX
    · simp only [step, if_neg hij] at hX'
      exact absurd hX' hX

/-- **A block built carries evidence** against every author its builder
has detected: the step puts it on the disk only then. -/
theorem convicts_of_builtAt {tr : Trace Validator BlockId} {i : ℕ} {v : Validator}
    {x : BlockId} (hb : BuiltAt blk ev f tr i v x) :
    ∀ X ∈ (stateBefore blk ev f tr i v).detected, Convicts blk ev x X := by
  obtain ⟨hi, hout, hin⟩ := hb
  rw [stateBefore_succ, hi] at hin
  dsimp only at hin
  rw [if_pos rfl] at hin
  by_cases h : (blk x).creator = v ∧ Ready blk (stateBefore blk ev f tr i v).disk x ∧
      Checks blk ev f x ∧ ∀ X ∈ (stateBefore blk ev f tr i v).detected, Convicts blk ev x X
  · exact h.2.2.2
  · simp only [step, if_neg h] at hin
    exact absurd hin hout

variable {H : Finset Validator} {tr : Trace Validator BlockId} {time : ℕ → ℕ} {Δ : ℕ}

/-- **Detection spreads within `Δ`**: an author an honest node detects at
event `i` is detected by every honest node at every event after
`time i + Δ`. -/
theorem detected_after (hrep : ReportsWithin blk ev f H tr time Δ) (hmono : TimeMono tr time)
    {i : ℕ} {v X : Validator} (hv : v ∈ H) (hd : DetectsAt blk ev f tr i v X)
    {w : Validator} (hw : w ∈ H) {j : ℕ} (ht : time i + Δ < time j) :
    X ∈ (stateBefore blk ev f tr j w).detected := by
  by_cases hwv : w = v
  · subst hwv
    refine detected_mono tr w ?_ hd.2
    by_contra h
    have := hmono j i (by omega) (by
      by_contra hl
      have h0 : stateBefore blk ev f tr (i + 1) w = stateBefore blk ev f tr i w := by
        rw [stateBefore_succ, List.getElem?_eq_none_iff.mpr (by omega)]
      exact hd.1 (h0 ▸ hd.2))
    omega
  obtain ⟨k, a, b, hk, hab, hX, htk⟩ := hrep i v X hv hd w hw hwv
  have hkj : k + 1 ≤ j := by
    by_contra h
    have := hmono j k (by omega) (List.getElem?_eq_some_iff.mp hk).1
    omega
  exact hX ▸ detected_mono tr w hkj (report_detects hk hab)

/-- **Honest blocks expose a detected author from `Δ` on**: a block an
honest node builds after `time i + Δ` exposes an author an honest node
detected at event `i`. -/
theorem exposes_after (hrep : ReportsWithin blk ev f H tr time Δ) (hmono : TimeMono tr time)
    {i : ℕ} {v X : Validator} (hv : v ∈ H)
    (hd : DetectsAt blk ev f tr i v X) {j : ℕ} {w : Validator} {x : BlockId}
    (hj : BuiltAt blk ev f tr j w x) (hw : w ∈ H) (ht : time i + Δ < time j) :
    Exposes blk ev x X :=
  ⟨x, mem_historyFrom_self, convicts_of_builtAt hj X
    (detected_after hrep hmono hv hd hw ht)⟩

omit [DecidableEq Validator] [Fintype Validator] in
/-- **A set holding the references of its blocks holds their histories.** -/
theorem historyUptoFrom_subset {S : Finset BlockId} (hS : ∀ i ∈ S, (blk i).refs ⊆ S) :
    ∀ (n : ℕ) {b : BlockId}, b ∈ S → historyUptoFrom blk n b ⊆ S
  | 0, b, hb => by simpa [historyUptoFrom] using hb
  | n + 1, b, hb => by
    intro i hi
    rcases mem_historyUptoFrom_succ.mp hi with rfl | ⟨j, hj, hij⟩
    · exact hb
    · exact historyUptoFrom_subset hS n (hS b hb hj) hij

omit [DecidableEq Validator] [Fintype Validator] in
theorem historyFrom_subset {S : Finset BlockId} (hS : ∀ i ∈ S, (blk i).refs ⊆ S) {b : BlockId}
    (hb : b ∈ S) : historyFrom blk b ⊆ S :=
  historyUptoFrom_subset hS _ hb

omit [DecidableEq Validator] in
/-- **Taking a stream in keeps the references held.** -/
theorem absorb_closed : ∀ {S : Finset BlockId} (L : List BlockId),
    (∀ i ∈ S, (blk i).refs ⊆ S) → ∀ i ∈ absorb blk S L, (blk i).refs ⊆ absorb blk S L
  | _, [], hS => hS
  | S, i :: L, hS => by
    refine absorb_closed L ?_
    split_ifs with hr
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hr.1.trans (Finset.subset_insert _ _)
      · exact (hS x hx).trans (Finset.subset_insert _ _)
    · exact hS

/-- **A step keeps the references of the disk's blocks on the disk.** -/
theorem step_closed {me : Validator} {s : State Validator BlockId}
    (hs : ∀ i ∈ s.disk, (blk i).refs ⊆ s.disk) (inp : Input Validator BlockId) :
    ∀ i ∈ (step blk ev f me s inp).disk, (blk i).refs ⊆ (step blk ev f me s inp).disk := by
  cases inp with
  | announce u t => simp only [step]; split_ifs <;> exact hs
  | chunk u L => exact absorb_closed _ hs
  | build x =>
    simp only [step]
    split_ifs with h
    · intro i hi
      simp only [settle] at hi ⊢
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact h.2.1.1.trans (Finset.subset_insert _ _)
      · exact (hs i hi).trans (Finset.subset_insert _ _)
    · exact hs
  | report i j => simp only [step]; split_ifs <;> exact hs

/-- **A run keeps the references of the disk's blocks on the disk.** -/
theorem run_closed {me : Validator} :
    ∀ (s : State Validator BlockId) (ins : List (Input Validator BlockId)),
      (∀ i ∈ s.disk, (blk i).refs ⊆ s.disk) →
      ∀ i ∈ (run blk ev f me s ins).disk, (blk i).refs ⊆ (run blk ev f me s ins).disk
  | _, [], hs => hs
  | s, inp :: ins, hs => run_closed (step blk ev f me s inp) ins (step_closed hs inp)

/-- **The final state** is the run over all the node's inputs. -/
theorem stateBefore_length (tr : Trace Validator BlockId) (v : Validator) :
    stateBefore blk ev f tr tr.length v = run blk ev f v State.init (inputsOf tr v) := by
  simp [stateBefore]

/-- **The premise of the exposure bound, in time.** Let the node `me`
detect every author it detects by `T`, and let every block an honest node
builds by `T + Δ` lie at round `m` or below. Then every honest block of
round `m + 1` exposes every author `me` detects. -/
theorem exposes_in_time (hrep : ReportsWithin blk ev f H tr time Δ) (hmono : TimeMono tr time)
    (hauth : Authentic blk ev f H tr) {me : Validator}
    (hme : me ∈ H) {T m : ℕ} (hT : ∀ i X, DetectsAt blk ev f tr i me X → time i ≤ T)
    (hm : ∀ j w x, BuiltAt blk ev f tr j w x → w ∈ H → time j ≤ T + Δ → (blk x).round ≤ m)
    {c : BlockId} (hc : (blk c).round = m + 1) (hcH : (blk c).creator ∈ H) :
    ∀ X ∈ (run blk ev f me State.init (inputsOf tr me)).detected, Exposes blk ev c X := by
  intro X hX
  rw [← stateBefore_length] at hX
  obtain ⟨i, -, hd⟩ := exists_detectsAt tr me X _ hX
  obtain ⟨j, hj⟩ := hauth c hcH
  have htj : T + Δ < time j := by
    by_contra h
    have := hm j _ c hj hcH (by omega)
    omega
  exact exposes_after hrep hmono hme hd hj hcH (by have := hT i X hd; omega)

/-- **The history bound in time**: the history of every block on `me`'s
disk holds at most `|V| + |D|` blocks of each round from `m + 1` on. -/
theorem card_history_round_le {H : Finset Validator} (hHc : Hᶜ.card ≤ f)
    (hmin : 2 * f < Fintype.card Validator) {me : Validator} (hme : me ∈ H)
    (hhon : ∀ i j, Twins blk i j → (blk i).creator ∉ H) {ins : List (Input Validator BlockId)}
    {n k : ℕ}
    (hexp : ∀ c, Admits blk ev f c → (blk c).round = n + 1 → (blk c).creator ∈ H →
      ∀ X ∈ (run blk ev f me State.init ins).detected, Exposes blk ev c X)
    (hk : n + 1 ≤ k) {x : BlockId} (hx : x ∈ (run blk ev f me State.init ins).disk) :
    ((historyFrom blk x).filter fun i => (blk i).round = k).card ≤
      Fintype.card Validator + (run blk ev f me State.init ins).detected.card :=
  (Finset.card_le_card (Finset.filter_subset_filter _
    (historyFrom_subset (run_closed _ ins (by simp [State.init])) hx))).trans
    (card_round_le hHc hmin hme hhon hexp hk)

/-- **Delivered reports give reports within `Δ`**: the event at which an
honest node detects an author is its own, and reports a pair of twins of
the author, which reaches every other honest node within `Δ`. -/
theorem reportsWithin_of_delivered (hdel : ReportsDelivered blk ev f H tr time Δ) :
    ReportsWithin blk ev f H tr time Δ := by
  intro i v X hv hd w hw hwv
  obtain ⟨hd1, hd2⟩ := hd
  have hstep : ∃ inp, tr[i]? = some (v, inp) ∧
      (stateBefore blk ev f tr (i + 1) v) = step blk ev f v (stateBefore blk ev f tr i v) inp := by
    rw [stateBefore_succ] at hd2 ⊢
    rcases hi : tr[i]? with _ | ⟨u, inp⟩
    · rw [hi] at hd2; exact absurd hd2 hd1
    · rw [hi] at hd2
      by_cases huv : u = v
      · subst huv; exact ⟨inp, rfl, by simp⟩
      · simp only [if_neg huv] at hd2; exact absurd hd2 hd1
  obtain ⟨inp, hi, hs⟩ := hstep
  obtain ⟨p, hp, hpX⟩ := exists_reports hd1 (hs ▸ hd2)
  obtain ⟨k, hk, htk⟩ := hdel i v inp hi hv p hp w hw hwv
  have hpt := (Finset.mem_filter.mp hp).2.1
  exact ⟨k, p.1, p.2, hk, hpt, hpX, htk⟩

end Sync

end Node

end LeanDag
