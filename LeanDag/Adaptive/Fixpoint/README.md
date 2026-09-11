# The fixpoint arc — slated for removal

These six modules are the adaptive-leaders arc as first built: a policy
that reads the run's whole verdict function, a schedule and verdicts that
solve each other simultaneously, and a two-epoch lag to make that fixed
point unique (AL1–AL10, report §13).

They are kept here only until `Integration/Joiner.lean` — **I5**, the
joiner across a garbage-collection cut — is restated over
`Adaptive.SegRun`. When that port lands, this directory goes.

**Why it goes.** `Run.closed` asks for `DecidedBelow` at
`W · (epochOf k + 2)`: every slot decided without reading the schedule
two epochs up. Before GST the run length is unbounded, so no epoch length
satisfies it, and on such an execution no `Run` exists at all. AL3 is a
true theorem with no instances there — **vacuous, not unsafe**; nothing
here admits a safety violation, and nothing here says what a validator
should do when the window fails.

The segmented arc (`Adaptive/Model/Segment.lean` and the directories
beside it) replaces it. Its run records what a validator has decided
rather than how far the derivation reached, so its safety carries no
window, no synchrony and no fairness — `adaptive-leaders.md` §7 to §9.

**What is not going.** `Properties.DecidedBelow`
(`Properties/Bounded.lean`) and `AnchoredRule.DecidedWithin`
(`Common/Anchored/Bounded.lean`) are core vocabulary, used by Mysticeti,
Odontoceti, Mahi-Mahi, Hydrozoan and the timed model. Neither belongs to
this arc.
