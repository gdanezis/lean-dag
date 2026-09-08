import LeanDag.Mysticeti.Quantitative
import LeanDag.Mysticeti.Properties
import LeanDag.Common.History
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# A build schedule that can be stuck

`built` is a partial function: `top v` is the highest round `v`
reached, and `built v n` is read only at `n ≤ top v`, so a validator
that cannot yet build a round simply has not reached it — **stuck** is
expressible as `top v = n`, with no deadline to compensate for. What
the schedule needs instead is the pacemaker's own progress rule,
`advances`: a validator holding a quorum of round-`n` authors at any
time is past round `n`, conditional on the quorum so it asserts no
production by itself.

```
genesis + converges + advances   ──▶  PopulatedOn, at every round
converges + catch-up + P7 + P9   ──▶  SynchronisedOn, at 2Δ + proc
```
-/

namespace LeanDag

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {U : BlockUniverse Validator BlockId Payload}
variable {T : Finset Validator} {N : ℕ}

/-- Drift over a build schedule alone: `T`-validators are never more than
`D` apart in real time at the same round, from `R` on. -/
def DriftOn (built : Validator → ℕ → ℕ) (T : Finset Validator)
    (R D N : ℕ) : Prop :=
  ∀ v ∈ T, ∀ w ∈ T, ∀ n, R ≤ n → n ≤ N → built w n ≤ built v n + D

/-! ## Factoring the bound

`converges` is partial synchrony in its usual two-part shape:
qualitatively, whatever one correct validator holds, every correct
validator holds some time later; quantitatively, from `gst` on that
lag is uniformly at most `delay`. `convergesWithin_iff_bounded` factors
convergence-with-a-bound into eventual convergence plus a uniform
post-`gst` lag bound — the bound is not decoration, since only a
bounded lag can be compared against a timeout to yield reference
coverage. -/

section Factoring

variable {holds : Validator → ℕ → Finset BlockId} {gst bound : ℕ}

/-- **The qualitative half.** Holdings converge: whatever `w` holds at `t`,
`v` holds at some later time. No bound and no GST. -/
def ConvergesEventually (holds : Validator → ℕ → Finset BlockId)
    (T : Finset Validator) : Prop :=
  ∀ v ∈ T, ∀ w ∈ T, ∀ t, ∃ d, holds w t ⊆ holds v (t + d)

/-- **The quantitative half.** From `gst` on, that lag is at most `bound` —
and uniformly so, in the validators and in the time. This is exactly the
`converges` field of `ViewPace`. -/
def ConvergesWithin (holds : Validator → ℕ → Finset BlockId)
    (T : Finset Validator) (gst bound : ℕ) : Prop :=
  ∀ v ∈ T, ∀ w ∈ T, ∀ t, gst ≤ t → holds w t ⊆ holds v (t + bound)

/-- A bounded lag is a lag: the timed form implies the untimed one, even
before `gst`, since holdings only grow. -/
theorem convergesEventually_of_within
    (hmono : ∀ v, ∀ s t, s ≤ t → holds v s ⊆ holds v t)
    (h : ConvergesWithin holds T gst bound) :
    ConvergesEventually holds T := by
  intro v hv w hw t
  refine ⟨(gst - t) + bound, ?_⟩
  refine le_trans (hmono w t (max t gst) (le_max_left _ _)) ?_
  refine le_trans (h v hv w hw (max t gst) (le_max_right _ _)) ?_
  exact hmono v _ _ (by omega)

/-- And conversely: eventual convergence whose lag is uniformly bounded
after `gst` *is* convergence within that bound. The two together are
`converges`, and neither half alone is. -/
theorem convergesWithin_of_bounded
    (hmono : ∀ v, ∀ s t, s ≤ t → holds v s ⊆ holds v t)
    (h : ∀ v ∈ T, ∀ w ∈ T, ∀ t, gst ≤ t →
      ∃ d ≤ bound, holds w t ⊆ holds v (t + d)) :
    ConvergesWithin holds T gst bound := by
  intro v hv w hw t ht
  obtain ⟨d, hd, hsub⟩ := h v hv w hw t ht
  exact le_trans hsub (hmono v _ _ (by omega))

/-- **The factoring.** Under monotone holdings, convergence within a bound
and bounded eventual convergence are the same condition. -/
theorem convergesWithin_iff_bounded
    (hmono : ∀ v, ∀ s t, s ≤ t → holds v s ⊆ holds v t) :
    ConvergesWithin holds T gst bound ↔
      (∀ v ∈ T, ∀ w ∈ T, ∀ t, gst ≤ t →
        ∃ d ≤ bound, holds w t ⊆ holds v (t + d)) :=
  ⟨fun h v hv w hw t ht => ⟨bound, le_refl _, h v hv w hw t ht⟩,
   convergesWithin_of_bounded hmono⟩

end Factoring

/-- **The shared trunk of every pacing discipline**, over a partial
build schedule. `top v` is the highest round `v` reached: `v`'s blocks
are exactly the rounds `0` through `top v`. The trunk carries the
schedule data, the views, `converges`, and the pacemaker's two rules —
`advances` and `catchup` — everything production and drift consume;
`ViewPace` extends it with the full-timeout floor (P9) and global
referencing (P7), the reactive schedule with the deadline and vote
clauses instead. -/
structure PaceCore (U : BlockUniverse Validator BlockId Payload)
    (T : Finset Validator) (N : ℕ) where
  /-- The highest round `v` reached. Rounds above it were never built. -/
  top : Validator → ℕ
  /-- When `v` built its round-`n` block — read only at `n ≤ top v`. -/
  built : Validator → ℕ → ℕ
  timeout : ℕ → ℕ
  gst : ℕ
  delay : ℕ
  rounds_le : ∀ b ∈ U.ids, (U.block b).round ≤ N
  /-- **Every round `v` reached, it built in.** At `n = 0` this is
  genesis — a validator produces its genesis block alone, so this
  much needs no network at all. Above `0` it is the reading of `top`: the
  validator got there, which is to say it built there. -/
  built_of_le_top : ∀ v ∈ T, ∀ n ≤ top v,
    ∃ b ∈ U.ids, (U.block b).creator = v ∧ (U.block b).round = n
  /-- **And no round above it.** Together with the previous clause, `v`'s
  blocks are exactly rounds `0` through `top v`. -/
  le_top_of_built : ∀ v ∈ T, ∀ b ∈ U.ids,
    (U.block b).creator = v → (U.block b).round ≤ top v
  timeout_pos : ∀ n, 1 ≤ timeout n
  /-- An upper bound on when round `n` was built, over `T`. Only an upper
  bound is ever needed: production reads it for the common time at which
  `converges` assembles the quorum, and nothing else consults it. -/
  latest : ℕ → ℕ
  built_le_latest : ∀ v ∈ T, ∀ n ≤ N, built v n ≤ latest n
  holds : Validator → ℕ → Finset BlockId
  /-- **S3.** A validator holds only blocks that exist. Nothing else ties
  `holds` to the universe: the liveness development never needs it, and the
  clause is stated here only so that a validator's holdings generate a
  `View` (`viewAt`), which is what connects the pacing line to the
  view-relative decision rules. -/
  holds_sub : ∀ v, ∀ t, holds v t ⊆ U.ids
  /-- **S4.** Holdings are causally closed: a validator that holds a block
  holds everything it references — P4 as a store property, and what
  makes `viewAt` a validator's own view rather than the closure of its
  fragments. -/
  holds_closed : ∀ v ∈ T, ∀ t, ∀ b ∈ holds v t,
    ∀ j ∈ (U.block b).refs, j ∈ holds v t
  /-- **S5.** A validator's block references only what it held when it
  built --- the converse of P7, and like it implementable and observable.
  It sits on the trunk rather than in a timeout discipline because it is
  discipline-independent: a reactive builder omits what it holds, but no
  builder can cite what it never held. -/
  refs_held : ∀ v ∈ T, ∀ n, ∀ b ∈ U.ids,
    (U.block b).creator = v → (U.block b).round = n + 1 →
    (U.block b).refs ⊆ holds v (built v (n + 1))
  /-- A validator holds every block it authored, from the time it built it. -/
  holds_own : ∀ v ∈ T, ∀ n ≤ N, ∀ b ∈ U.ids,
    (U.block b).creator = v → (U.block b).round = n → b ∈ holds v (built v n)
  holds_mono : ∀ v, ∀ s t, s ≤ t → holds v s ⊆ holds v t
  /-- **N2, as view convergence** (network). -/
  converges : ∀ v ∈ T, ∀ w ∈ T, ∀ t, gst ≤ t → holds w t ⊆ holds v (t + delay)
  /-- **P8, as the pacemaker's progress rule** (protocol). A validator
  that holds a quorum of distinct round-`n` authors at any time gets
  past round `n`. Conditional on the quorum, so it asserts no
  production until one is in hand. -/
  advances : ∀ v ∈ T, ∀ n < N, ∀ t,
    quorumCard Validator ≤ (authorsIn U (holds v t) n).card → n < top v
  /-- The processing bound: how long round entry may lag evidence. -/
  proc : ℕ
  /-- **Catch-up** (protocol). Seeing a round is entering it: any
  `T`-authored block of round `n` in hand at a post-GST time `t` means
  the holder reached round `n` and built its own block there by
  `t + proc`. Asserted only from `gst`, like `converges`, since before
  it the clamped floor may delay a validator past what this clause
  would claim. Makes drift a derived quantity (`drift_collapse`), with
  no start-spread hypothesis surviving into the headline statements. -/
  catchup : ∀ v ∈ T, ∀ n ≤ N, ∀ b ∈ U.ids,
    (U.block b).creator ∈ T → (U.block b).round = n →
    ∀ t, gst ≤ t → b ∈ holds v t → n ≤ top v ∧ built v n ≤ t + proc

namespace PaceCore

variable (pc : PaceCore U T N)

omit [DecidableEq BlockId] in
/-- **Every reliable validator reaches every round below the horizon** —
with `T` a quorum, nobody in `T` is stuck: `holds_mono` carries each
`w ∈ T`'s round-`n` block to a common time, `converges` puts a quorum
of them in `v`'s hands, and `advances` fires. Proved on the trunk, with
no floor, ceiling or timeout mentioned. -/
theorem reached (hcard : quorumCard Validator ≤ T.card) :
    ∀ n ≤ N, ∀ v ∈ T, n ≤ pc.top v := by
  intro n
  induction n with
  | zero => intro _ v _; omega
  | succ n ih =>
      intro hn v hv
      refine Nat.succ_le_of_lt (pc.advances v hv n (by omega)
        (max (pc.latest n) pc.gst + pc.delay) (le_trans hcard (Finset.card_le_card ?_)))
      intro w hw
      obtain ⟨b, hb, hbc, hbr⟩ := pc.built_of_le_top w hw n (ih (by omega) w hw)
      refine mem_authorsIn.mpr ⟨b, ?_, hbr, hbc⟩
      have hown := pc.holds_own w hw n (by omega) b hb hbc hbr
      have hle : pc.built w n ≤ max (pc.latest n) pc.gst :=
        le_trans (pc.built_le_latest w hw n (by omega)) (le_max_left _ _)
      exact pc.converges v hv w hw _ (le_max_right _ _) (pc.holds_mono w _ _ hle hown)

omit [DecidableEq BlockId] in
/-- **Production, once for every discipline**: a round a validator got to
is a round it built in. -/
theorem populatedOn (pc : PaceCore U T N)
    (hcard : quorumCard Validator ≤ T.card) :
    ∀ n ≤ N, PopulatedOn U T n :=
  fun n hn v hv => pc.built_of_le_top v hv n (pc.reached hcard n hn v hv)

/-- **The view a validator's holdings generate.** The causal closure of
what `v` holds at `t` — a legitimate `View`, closure discharged by
transitivity of `Reaches`. The bridge between the pacing line's
time-indexed `holds` and the commit rules' `View`, letting liveness be
stated about a validator's own view rather than the full universe. -/
def viewAt (pc : PaceCore U T N) (v : Validator) (t : ℕ) :
    View Validator BlockId Payload U where
  ids := (pc.holds v t).biUnion (history U)
  subset_ids := by
    intro i hi
    obtain ⟨a, ha, hia⟩ := Finset.mem_biUnion.mp hi
    exact history_subset_ids (pc.holds_sub v t ha) hia
  complete := by
    intro i hi j hj
    obtain ⟨a, ha, hia⟩ := Finset.mem_biUnion.mp hi
    have ha_ids : a ∈ U.ids := pc.holds_sub v t ha
    refine Finset.mem_biUnion.mpr ⟨a, ha, ?_⟩
    exact (mem_history_iff ha_ids).mpr
      (((mem_history_iff ha_ids).mp hia).trans (Reaches.single hj))

/-- **Closure, iterated**: a held block's whole causal cone is held. The
step is `holds_closed`; the induction runs along the reachability chain. -/
theorem history_subset_holds (pc : PaceCore U T N) {v : Validator} (hv : v ∈ T)
    {t : ℕ} {b : BlockId} (hb : b ∈ pc.holds v t) :
    history U b ⊆ pc.holds v t := by
  intro i hi
  have hr := (mem_history_iff (pc.holds_sub v t hb)).mp hi
  clear hi
  induction hr with
  | refl => exact hb
  | tail _ hstep ih => exact pc.holds_closed v hv t _ ih _ hstep

/-- What a validator holds is in the view it generates. -/
theorem mem_viewAt (pc : PaceCore U T N) {v : Validator} {t : ℕ} {b : BlockId}
    (hb : b ∈ pc.holds v t) : b ∈ (pc.viewAt v t).ids :=
  Finset.mem_biUnion.mpr ⟨b, hb, mem_history_self⟩

/-- **The view a validator holds is exactly what it holds.** Under
closure `viewAt` adds nothing: a reliable validator's view is its
holdings, and the local liveness statement is about blocks it actually
has. -/
theorem viewAt_ids (pc : PaceCore U T N) {v : Validator} (hv : v ∈ T) (t : ℕ) :
    (pc.viewAt v t).ids = pc.holds v t := by
  refine Finset.Subset.antisymm (fun i hi => ?_) (fun b hb => pc.mem_viewAt hb)
  obtain ⟨a, ha, hia⟩ := Finset.mem_biUnion.mp hi
  exact pc.history_subset_holds hv ha hia

omit [DecidableEq BlockId] in
/-- **Delivery, in the form the local argument consumes.** Past GST, every
reliable validator holds every `T`-authored round-`n` block by
`latest n + delay`: its author holds it when built, `latest` is a common
time for the whole round, and convergence carries it across. -/
theorem holds_roundBlocks (pc : PaceCore U T N) {n : ℕ} (hn : n ≤ N)
    (hg : ∀ u ∈ T, pc.gst ≤ pc.built u n) :
    ∀ v ∈ T, ∀ b ∈ U.ids, (U.block b).creator ∈ T → (U.block b).round = n →
      b ∈ pc.holds v (pc.latest n + pc.delay) := by
  intro v hv b hb hbT hbr
  have hown := pc.holds_own _ hbT n hn b hb rfl hbr
  have hle : pc.built ((U.block b).creator) n ≤ pc.latest n :=
    pc.built_le_latest _ hbT n hn
  exact pc.converges v hv _ hbT (pc.latest n)
    (le_trans (hg _ hbT) hle) (pc.holds_mono _ _ _ hle hown)

/-- **The local commit argument, stated once.** Given a leader block, a
quorum-sized `T` whose decision-round blocks all certify it, and
post-GST builds, every reliable validator decides the slot on its own
view: the counting of `directCommit_of_certifiesAt` run inside
`viewAt v t` rather than the universe. -/
theorem decided_local_of_certifiesAt [S : Slots Validator] {k : ℕ} {L : BlockId}
    (pc : PaceCore U T N) (hcard : quorumCard Validator ≤ T.card)
    (hN : S.slotRound k + 2 ≤ N)
    (hg : ∀ u ∈ T, pc.gst ≤ pc.built u (S.slotRound k + 2))
    (hL : IsLeaderBlock U k L) (hcert : CertifiesAt U T (S.slotRound k) L) :
    ∀ v ∈ T,
      Decided U (pc.viewAt v (pc.latest (S.slotRound k + 2) + pc.delay)) k (some L) := by
  have hpop2 := pc.populatedOn hcard (S.slotRound k + 2) hN
  intro v hv
  refine Decided.directCommit hL (le_trans hcard (Finset.card_le_card ?_))
  intro u hu
  obtain ⟨c, hc, hcc, hcr⟩ := hpop2 u hu
  refine mem_heldAuthors.mpr ⟨c, mem_certificatesAt.mpr ⟨hc, hcr, hcert u hu c hc hcc hcr⟩, ?_, hcc⟩
  exact pc.mem_viewAt (pc.holds_roundBlocks hN hg v hv c hc (hcc ▸ hu) hcr)

omit [DecidableEq BlockId] in
/-- **Drift collapses, from any starting value.** At any round whose
builds all lie past GST, the spread is at most `delay + proc`,
whatever it was before: the earliest builder's block reaches the
laggard within `delay`, and catch-up converts the sighting into entry
within `proc`. -/
theorem drift_collapse {n : ℕ} (hn : n ≤ N)
    (htop : ∀ u ∈ T, n ≤ pc.top u)
    (hg : ∀ u ∈ T, pc.gst ≤ pc.built u n) :
    ∀ v ∈ T, ∀ w ∈ T, pc.built v n ≤ pc.built w n + (pc.delay + pc.proc) := by
  intro v hv w hw
  obtain ⟨b, hb, hbc, hbr⟩ := pc.built_of_le_top w hw n (htop w hw)
  have hown := pc.holds_own w hw n hn b hb hbc hbr
  have hconv := pc.converges v hv w hw _ (hg w hw) hown
  have := (pc.catchup v hv n hn b hb (hbc ▸ hw) hbr _
    (le_trans (hg w hw) (Nat.le_add_right _ _)) hconv).2
  omega

omit [DecidableEq BlockId] in
/-- The collapsed spread, in the form the coverage argument consumes —
with no base hypothesis anywhere. `hle` is the discipline's `le_built`
(rounds advance real time), which each extension proves from its own
schedule clauses; everything else is the trunk's. -/
theorem driftOn_of_catchup {R : ℕ}
    (hcard : quorumCard Validator ≤ T.card) (hgst : pc.gst ≤ R)
    (hle : ∀ u ∈ T, ∀ n ≤ pc.top u, n ≤ pc.built u n) :
    DriftOn pc.built T R (pc.delay + pc.proc) N := by
  intro v hv w hw n hRn hnN
  have htop := fun u hu => pc.reached hcard n hnN u hu
  refine pc.drift_collapse hnN htop (fun u hu => ?_) w hw v hv
  exact le_trans (le_trans hgst hRn) (hle u hu n (htop u hu))

end PaceCore

/-- The full-timeout discipline: `PaceCore` with P9 (the waiting floor)
and the global referencing clause P7. The structure the coverage
derivation and quantitative results run on. No promptness ceiling or
attainment clause appears, since drift is derived from the trunk's
catch-up rule alone. -/
structure ViewPace (U : BlockUniverse Validator BlockId Payload)
    (T : Finset Validator) (N : ℕ) extends PaceCore U T N where
  /-- **P9, the waiting rule** (protocol), over the rounds `v` reached. -/
  waits : ∀ v ∈ T, ∀ n < top v, built v n + timeout n ≤ built v (n + 1)
  /-- **P7, referencing** (protocol), over any block the validator authors. -/
  references : ∀ v ∈ T, ∀ n < N, ∀ c ∈ U.ids,
    (U.block c).creator = v → (U.block c).round = n + 1 →
    ∀ a ∈ holds v (built v (n + 1)), (U.block a).round = n →
    a ∈ (U.block c).refs

namespace ViewPace

variable (vp : ViewPace U T N)

/-- The `converges` field *is* the bounded form of the factoring above. -/
theorem convergesWithin (vp : ViewPace U T N) :
    ConvergesWithin vp.holds T vp.gst vp.delay := vp.converges

/-- Every `ViewPace` converges in the qualitative sense too — the bound is
extra information, not a different phenomenon. -/
theorem convergesEventually (vp : ViewPace U T N) :
    ConvergesEventually vp.holds T :=
  convergesEventually_of_within vp.holds_mono vp.converges

omit [DecidableEq BlockId] in
/-- **The separation** — V1's content over the partial schedule: a
`T`-block built after GST and early enough is referenced, derivable
from `converges` and `references` alone — the block is in its author's
hands when built, reaches the builder within `delay`, and is still
there when the builder acts. No counting, drift or waiting rule enters
until the arrival-time hypothesis itself must be discharged. -/
theorem covers_of_converges {n : ℕ} (hn : n < N)
    {c : BlockId} (hc : c ∈ U.ids) (hcT : (U.block c).creator ∈ T)
    (hcr : (U.block c).round = n + 1)
    {a : BlockId} (ha : a ∈ U.ids) (haT : (U.block a).creator ∈ T)
    (har : (U.block a).round = n)
    (hgst : vp.gst ≤ vp.built ((U.block a).creator) n)
    (hearly : vp.built ((U.block a).creator) n + vp.delay ≤
      vp.built ((U.block c).creator) (n + 1)) :
    a ∈ (U.block c).refs := by
  refine vp.references _ hcT n hn c hc rfl hcr a ?_ har
  refine vp.holds_mono _ _ _ hearly ?_
  exact vp.converges _ hcT _ haT _ hgst
    (vp.holds_own _ haT n (by omega) a ha rfl har)

omit [DecidableEq BlockId] in
/-- Rounds advance real time, over the rounds a validator reached. -/
theorem le_built {v : Validator} (hv : v ∈ T) : ∀ n ≤ vp.top v, n ≤ vp.built v n := by
  intro n
  induction n with
  | zero => intro _; omega
  | succ n ih =>
      intro hn
      have hw := vp.waits v hv n (by omega)
      have := vp.timeout_pos n
      have := ih (by omega)
      omega

omit [DecidableEq BlockId] in
/-- **Production, with no deadline to beat.** Every round below the
horizon is populated, from genesis, view convergence and the progress
rule alone, with no drift, backoff, timeout or schedule side condition.
By induction: each `w ∈ T` holds its round-`n` block, `holds_mono`
carries it to a common time, `converges` puts a quorum of them in `v`'s
hands, and `advances` fires. -/
theorem reached (vp : ViewPace U T N)
    (hcard : quorumCard Validator ≤ T.card) :
    ∀ n ≤ N, ∀ v ∈ T, n ≤ vp.top v :=
  vp.toPaceCore.reached hcard

omit [DecidableEq BlockId] in
/-- **Production**, inherited from the trunk (`PaceCore.populatedOn`). -/
theorem populatedOn (vp : ViewPace U T N)
    (hcard : quorumCard Validator ≤ T.card) :
    ∀ n ≤ N, PopulatedOn U T n :=
  vp.toPaceCore.populatedOn hcard

omit [DecidableEq BlockId] in
/-- **Drift is derived**, from the trunk's catch-up rule: the collapsed
spread `delay + proc`, from any `R` past GST, with no hypothesis about
the start. The quorum bound enters through `reached`, which places
those builds past GST. -/
theorem driftOn_of_catchup (vp : ViewPace U T N) {R : ℕ}
    (hcard : quorumCard Validator ≤ T.card) (hgst : vp.gst ≤ R) :
    DriftOn vp.built T R (vp.delay + vp.proc) N :=
  vp.toPaceCore.driftOn_of_catchup hcard hgst (fun u hu => vp.le_built hu)

omit [DecidableEq BlockId] in
/-- **The coverage engine** — the race, run against an arbitrary drift
bound `D`. Needs neither production, the quorum bound, nor
`T ⊆ Correct`, since `references` and `holds_own` are stated over any
block a validator authored. Kept for reliable sets below the quorum,
where drift must be supplied from outside. -/
theorem synchronisedOn_of_driftOn {R D : ℕ}
    (hD : DriftOn vp.built T R D N) (hgst : vp.gst ≤ R)
    (hbackoff : ∀ n, R ≤ n → D + vp.delay ≤ vp.timeout n) :
    SynchronisedOn U T R := by
  intro n hn b hb hbr hbc a ha har hac
  have hnN : n < N := by have := vp.rounds_le b hb; omega
  have htopb : n + 1 ≤ vp.top ((U.block b).creator) :=
    hbr ▸ vp.le_top_of_built _ hbc b hb rfl
  have htopa : n ≤ vp.top ((U.block a).creator) :=
    har ▸ vp.le_top_of_built _ hac a ha rfl
  have hle := vp.le_built hac n htopa
  -- the race, won: drift, the wait and the backoff place the arrival first
  have hdrift := hD _ hbc _ hac n hn (by omega)
  have hwait := vp.waits _ hbc n (by omega)
  have hto := hbackoff n hn
  exact vp.covers_of_converges hnN hb hbc hbr ha hac har (by omega) (by omega)

omit [DecidableEq BlockId] in
/-- **Reference coverage, drift-free.** From any `R` past GST, once the
timeout clears `2Δ + proc`, every reliable round-`n+1` block references
every reliable round-`n` block, with no start-spread hypothesis: the
spread at `R` is whatever catch-up left, `delay + proc`. -/
theorem synchronisedOn_of_converges {R : ℕ}
    (hcard : quorumCard Validator ≤ T.card) (hgst : vp.gst ≤ R)
    (hbackoff : ∀ n, R ≤ n → 2 * vp.delay + vp.proc ≤ vp.timeout n) :
    SynchronisedOn U T R :=
  vp.synchronisedOn_of_driftOn (vp.driftOn_of_catchup hcard hgst) hgst
    (fun n hn => by have := hbackoff n hn; omega)

section Liveness

variable [S : Slots Validator]

/-- **The liveness spine** (V17): commits recur, with the seed at round
`0` genesis, and no schedule side condition. The network contributes
`converges` and `vp.gst ≤ R`; the protocol contributes genesis,
`advances`, `catchup`, `references` and `waits`; no drift appears,
since the backoff clears the collapsed spread. -/
theorem commits_recur_via_pace (hT : T ⊆ (Correct : Finset Validator))
    (hcard : quorumCard Validator ≤ T.card)
    (fair : FairScheduleOn T) (R k : ℕ) :
    ∃ k', k ≤ k' ∧ R ≤ S.slotRound k' ∧
      ∀ (U : BlockUniverse Validator BlockId Payload) (N : ℕ)
        (vp : ViewPace U T N),
        vp.gst ≤ R →
        (∀ n, R ≤ n → 2 * vp.delay + vp.proc ≤ vp.timeout n) →
        S.slotRound k' + 2 ≤ N →
        ∃ L, IsLeaderBlock U k' L ∧ Decided U (View.full U) k' (some L) := by
  obtain ⟨k', hk, hR, hcommit⟩ :=
    MysticetiProperties.commits_recur_on_of_properties (BlockId := BlockId)
      (Payload := Payload) hT hcard fair R k
  refine ⟨k', hk, hR, fun U N vp hgst hbackoff hN => ?_⟩
  exact hcommit U N
    (fun r _ hr => vp.populatedOn hcard r hr)
    (vp.synchronisedOn_of_converges hcard hgst hbackoff)
    hN

/-! ### Liveness, localised to a validator's own view

Every liveness statement above concludes on the full view, which no
deployed validator ever holds. The pacing structure says more: past
GST the delivery lemma puts every reliable decision-round block into
every reliable validator's own `viewAt`, by an explicit time. -/

/-- **Liveness is local** (V18): past GST, every reliable validator
decides the slot on its own view, by an explicit time — L4's counting
argument run inside `viewAt v t` rather than the universe. Strictly
strengthens the global statement, which `decided_full` recovers. -/
theorem decided_local (vp : ViewPace U T N)
    (hcard : quorumCard Validator ≤ T.card) (hgst : vp.gst ≤ R)
    (hbackoff : ∀ n, R ≤ n → 2 * vp.delay + vp.proc ≤ vp.timeout n)
    (hR : R ≤ S.slotRound k) (hN : S.slotRound k + 2 ≤ N)
    (hlead : S.leader k ∈ T) :
    ∃ L, IsLeaderBlock U k L ∧ ∀ v ∈ T,
      Decided U (vp.viewAt v (vp.latest (S.slotRound k + 2) + vp.delay)) k (some L) := by
  have hsync := vp.synchronisedOn_of_converges hcard hgst hbackoff
  -- the leader block, and the certificate blocks, from derived production
  obtain ⟨L, hLmem, hLc, hLr⟩ :=
    vp.populatedOn hcard (S.slotRound k) (by omega) (S.leader k) hlead
  have hL : IsLeaderBlock U k L := ⟨hLmem, hLr, hLc⟩
  have hcert : CertifiesAt U T (S.slotRound k) L :=
    certifiesAt_of_synchronisedOn hcard hsync hR
      (vp.populatedOn hcard (S.slotRound k + 1) (by omega)) hLmem hLr (hLc ▸ hlead)
  -- past GST every reliable validator is at or beyond the decision round
  have hg : ∀ u ∈ T, vp.gst ≤ vp.built u (S.slotRound k + 2) := by
    intro u hu
    have htop := vp.reached hcard (S.slotRound k + 2) hN u hu
    have := vp.le_built hu (S.slotRound k + 2) htop
    omega
  exact ⟨L, hL, vp.toPaceCore.decided_local_of_certifiesAt hcard hN hg hL hcert⟩

/-- **The liveness spine, localised** (V18): commits recur, and at the
recurring slot every reliable validator decides on its own view, the
slot fixed by the schedule and the round bound alone. `T ⊆ Correct` is
not needed, since production is the pacing structure's own over `T`. -/
theorem commits_recur_local (hcard : quorumCard Validator ≤ T.card)
    (fair : FairScheduleOn T) (R k : ℕ) :
    ∃ k', k ≤ k' ∧ R ≤ S.slotRound k' ∧
      ∀ (U : BlockUniverse Validator BlockId Payload) (N : ℕ) (vp : ViewPace U T N),
        vp.gst ≤ R → (∀ n, R ≤ n → 2 * vp.delay + vp.proc ≤ vp.timeout n) →
        S.slotRound k' + 2 ≤ N →
        ∃ L, IsLeaderBlock U k' L ∧ ∀ v ∈ T,
          Decided U (vp.viewAt v (vp.latest (S.slotRound k' + 2) + vp.delay))
            k' (some L) := by
  obtain ⟨k₀, hk₀⟩ := S.unbounded R
  obtain ⟨k', hk', hlead⟩ := fair (max k k₀)
  have hRk' : R ≤ S.slotRound k' :=
    le_trans hk₀ (S.mono (le_trans (le_max_right k k₀) hk'))
  refine ⟨k', le_trans (le_max_left _ _) hk', hRk', ?_⟩
  intro U N vp hgst hbackoff hN
  exact vp.decided_local hcard hgst hbackoff hRk' hN hlead

/-- **Liveness, execution first** (V18′). The same result with the
pacing structure fixed before the slot: in a given run, past GST with
the timeout clearing `2Δ + proc`, commits recur and every reliable
validator decides on its own view. -/
theorem commits_recur_local_of_pace (vp : ViewPace U T N)
    (hcard : quorumCard Validator ≤ T.card)
    (fair : FairScheduleOn T) (R : ℕ) (hgst : vp.gst ≤ R)
    (hbackoff : ∀ n, R ≤ n → 2 * vp.delay + vp.proc ≤ vp.timeout n) (k : ℕ) :
    ∃ k', k ≤ k' ∧ R ≤ S.slotRound k' ∧
      (S.slotRound k' + 2 ≤ N →
        ∃ L : BlockId, IsLeaderBlock U k' L ∧ ∀ v ∈ T,
          Decided U (vp.viewAt v (vp.latest (S.slotRound k' + 2) + vp.delay))
            k' (some L)) := by
  obtain ⟨k', hk, hR, hrest⟩ :=
    commits_recur_local (BlockId := BlockId) (Payload := Payload) (T := T) hcard fair R k
  exact ⟨k', hk, hR, fun hN => hrest U N vp hgst hbackoff hN⟩

/-- **The global statement is a corollary**, so V18 strictly strengthens the
main line: a reliable validator exists (the quorum bound is nonvacuous), it
decides locally, and view monotonicity lifts its verdict to the full
view — the band, not L3. `LeaderCommits` reaches the same conclusion
without ever naming a validator's own view; this route names one. -/
theorem decided_of_local (vp : ViewPace U T N)
    (hcard : quorumCard Validator ≤ T.card) (hgst : vp.gst ≤ R)
    (hbackoff : ∀ n, R ≤ n → 2 * vp.delay + vp.proc ≤ vp.timeout n)
    (hR : R ≤ S.slotRound k) (hN : S.slotRound k + 2 ≤ N)
    (hlead : S.leader k ∈ T) :
    ∃ L, IsLeaderBlock U k L ∧ Decided U (View.full U) k (some L) := by
  obtain ⟨L, hL, hloc⟩ := vp.decided_local hcard hgst hbackoff hR hN hlead
  exact ⟨L, hL, Properties.decided_mono_of_banded MysticetiProperties.banded (BlockRecord.View.subset_ids _)
    (hloc _ hlead)⟩

end Liveness

end ViewPace

/-! ## The rush bound

The pacemaker rules are stated over `T`, but a deployment runs the
author-blind strengthening of each clause, catching up on any valid
block whoever authored it. This cannot be rushed: a block of round
`n + 1` references a quorum of distinct round-`n` authors, which meets
any quorum-sized `T`, so every valid non-genesis block carries a
reliable parent that has paid the full timeout bill below it. -/

section RushBound

omit [DecidableEq BlockId] in
/-- **Every valid non-genesis block carries a reliable parent.** Its
reference quorum has at least `n − 2f ≥ f + 1` authors in any
quorum-sized `T`; one is exhibited. Nothing about pacing enters: this is
a fact about validity and cardinalities alone. -/
theorem exists_reliable_parent
    (hcard : quorumCard Validator ≤ T.card)
    {b : BlockId} (hb : b ∈ U.ids) (hr : 0 < (U.block b).round) :
    ∃ a ∈ (U.block b).refs, a ∈ U.ids ∧ (U.block a).creator ∈ T ∧
      (U.block a).round + 1 = (U.block b).round := by
  have hv := U.valid b hb
  have hq := hv.quorum hr
  have hcap : 0 < ((creators U.block (U.block b)) ∩ T).card := by
    have h1 := Finset.card_inter_add_card_union (creators U.block (U.block b)) T
    have h2 : ((creators U.block (U.block b)) ∪ T).card ≤ Fintype.card Validator :=
      Finset.card_le_univ _
    have h3 := F.card_validators
    omega
  obtain ⟨u, hu⟩ := Finset.card_pos.mp hcap
  rw [Finset.mem_inter] at hu
  obtain ⟨a, ha, hac⟩ := mem_creatorsOf.mp hu.1
  exact ⟨a, ha, U.complete b hb a ha, hac ▸ hu.2, hv.predecessor a ha⟩

omit [DecidableEq BlockId] in
/-- **No block outruns the reliable frontier by more than one round.**
Whatever a Byzantine validator publishes, some `T`-validator has reached
the round below it — the adversary's whole freedom is the single layer
it may build the instant a quorum forms beneath it. -/
theorem PaceCore.round_le_top_succ (pc : PaceCore U T N)
    (hcard : quorumCard Validator ≤ T.card)
    {b : BlockId} (hb : b ∈ U.ids) :
    ∃ u ∈ T, (U.block b).round ≤ pc.top u + 1 := by
  rcases Nat.eq_zero_or_pos (U.block b).round with h0 | hpos
  · have hT : 0 < T.card := by have := F.card_validators; omega
    obtain ⟨u, hu⟩ := Finset.card_pos.mp hT
    exact ⟨u, hu, by omega⟩
  · obtain ⟨a, _, ha, haT, har⟩ := exists_reliable_parent hcard hb hpos
    refine ⟨_, haT, ?_⟩
    have := pc.le_top_of_built _ haT a ha rfl
    omega

omit [DecidableEq BlockId] in
/-- The full-timeout discipline's floor, accumulated: a validator's
round-`n` entry lies at least the sum of all `n` timeouts past its
start. -/
theorem ViewPace.built_ge_sum (vp : ViewPace U T N) {u : Validator}
    (hu : u ∈ T) : ∀ n ≤ vp.top u,
    vp.built u 0 + (∑ i ∈ Finset.range n, vp.timeout i) ≤ vp.built u n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      intro hn
      have hw := vp.waits u hu n (by omega)
      have := ih (by omega)
      rw [Finset.sum_range_succ]
      omega

omit [DecidableEq BlockId] in
/-- **The honest floor** (CU5): a valid block of round `n + 1` certifies
that some reliable validator reached round `n` having genuinely waited
out all `n` timeouts, so the author-blind catch-up a deployment runs
never pulls a validator past where a reliable peer already is. -/
theorem ViewPace.exists_honest_floor (vp : ViewPace U T N)
    (hcard : quorumCard Validator ≤ T.card)
    {b : BlockId} (hb : b ∈ U.ids) {n : ℕ}
    (hbr : (U.block b).round = n + 1) :
    ∃ u ∈ T, n ≤ vp.top u ∧
      vp.built u 0 + (∑ i ∈ Finset.range n, vp.timeout i) ≤ vp.built u n := by
  obtain ⟨a, _, ha, haT, har⟩ := exists_reliable_parent hcard hb (by omega)
  have htop : n ≤ vp.top ((U.block a).creator) := by
    have := vp.le_top_of_built _ haT a ha rfl
    omega
  exact ⟨_, haT, htop, vp.built_ge_sum haT n htop⟩

end RushBound

namespace ViewPace

variable (vp : ViewPace U T N)

/-! ## The quantitative arc, on this route

Report §6.10's results, over the partial schedule. `Rated`, `FairWithin`
and `BoundedSpacing` carry over verbatim; the explicit coverage round
and wait bound are free of any start spread, the threshold everywhere
being the constant `2Δ + proc`. `reached` answers what a wait bound
means when a validator can be stuck: with `T` a quorum, none is. -/

section Quantitative

omit [DecidableEq BlockId] in
/-- **Q3 on this route** — coverage from an explicit round, under a rated
backoff: `R = max (2Δ + proc) gst`, each summand what it looks like. The
rated timeout clears the constant threshold from the round named by the
threshold itself, and no start spread or base round appears. -/
theorem synchronisedOn_of_rate (vp : ViewPace U T N)
    (hcard : quorumCard Validator ≤ T.card)
    (hrate : Rated vp.timeout) :
    SynchronisedOn U T (max (2 * vp.delay + vp.proc) vp.gst) :=
  vp.synchronisedOn_of_converges hcard (le_max_right _ _)
    (fun n hn =>
      backoff_ge_of_rate hrate _ n (le_trans (le_max_left _ _) hn))

variable [S : Slots Validator] {R k : ℕ}

/-- **The wait bound** (Q2 headline, report §6.10): a constant timeout
of `2Δ + proc` commits every reliable-led slot past GST, with no start
spread in any hypothesis, since catch-up collapses whatever spread the
deployment began with. -/
theorem directCommit_of_wait (vp : ViewPace U T N)
    (hcard : quorumCard Validator ≤ T.card)
    (hgst : vp.gst ≤ R)
    (hwait : ∀ n, R ≤ n → 2 * vp.delay + vp.proc ≤ vp.timeout n)
    (hR : R ≤ S.slotRound k) (hN : S.slotRound k + 2 ≤ N)
    (hlead : S.leader k ∈ T) :
    ∃ L, IsLeaderBlock U k L ∧ DirectCommit U L (S.slotRound k) :=
  directCommit_of_leader_mem hcard
    (vp.synchronisedOn_of_converges hcard hgst hwait) hR
    (vp.populatedOn hcard _ (by omega)) (vp.populatedOn hcard _ (by omega))
    (vp.populatedOn hcard _ (by omega)) hlead

/-- **The wait bound, as a decision.** -/
theorem decided_of_wait (vp : ViewPace U T N)
    (hcard : quorumCard Validator ≤ T.card)
    (hgst : vp.gst ≤ R)
    (hwait : ∀ n, R ≤ n → 2 * vp.delay + vp.proc ≤ vp.timeout n)
    (hR : R ≤ S.slotRound k) (hN : S.slotRound k + 2 ≤ N)
    (hlead : S.leader k ∈ T) :
    ∃ L, IsLeaderBlock U k L ∧ Decided U (View.full U) k (some L) := by
  obtain ⟨L, hLb, hdc⟩ := vp.directCommit_of_wait hcard hgst hwait hR hN hlead
  exact ⟨L, hLb, Decided.directCommit hLb (directCommitIn_full hdc)⟩

/-- **`Delay(Δ) = 2Δ`** — the threshold at instantaneous entry: when
`proc = 0`, the constant is twice the delivery bound, the timer deployed
implementations run. The general threshold degrades linearly in the
processing bound and in nothing else. -/
theorem directCommit_of_wait_two_delay (vp : ViewPace U T N)
    (hcard : quorumCard Validator ≤ T.card)
    (hproc : vp.proc = 0) (hgst : vp.gst ≤ R)
    (hwait : ∀ n, R ≤ n → 2 * vp.delay ≤ vp.timeout n)
    (hR : R ≤ S.slotRound k) (hN : S.slotRound k + 2 ≤ N)
    (hlead : S.leader k ∈ T) :
    ∃ L, IsLeaderBlock U k L ∧ DirectCommit U L (S.slotRound k) :=
  vp.directCommit_of_wait hcard hgst
    (fun n hn => by have := hwait n hn; omega) hR hN hlead

end Quantitative

end ViewPace

end LeanDag
