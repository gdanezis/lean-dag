# A slot's kind: how a rule with a varying wave uses it

`Slots.kind : ℕ → ℕ` is the fourth datum a schedule carries, beside a
slot's round and its leader. It is `0` unless the schedule says
otherwise, and every rule in the tree at the time of writing has one
wave and never reads it. This note is for the first rule that does. It
records what the kind is, where the common layer reads it, what a rule
whose wave varies has to write, and what it then has — each point
checked on the Steelhead rule (#21), which is the worked example
throughout (`docs/target-properties.md` §11.43 records the change to
the common layer itself).

## 1. What the kind is, and why it is the schedule's

A rule whose wave varies reads a different number of rounds above
different slots. `Banded` says a verdict survives any renumbering of
the rounds by an offset, on a band the two universes agree on; a wave
read from the *round* does not survive such a renumbering, since the
renumbered slot sits at a round of a different wave
(`LeanDagTest/Common/VaryingWave.lean`, `altRule_not_banded`). A wave
read from the slot's *kind* does: the kind is a fact about the slot, as
its leader is, and every mechanism that renumbers rounds carries a
slot's leader with it and now carries its kind the same way
(`Rebases.kind`). The mode of a slot — synchronous or asynchronous,
wave three or wave five — is common knowledge from the schedule, like
who leads it, and that is where it lives.

## 2. Where the common layer reads the kind

An anchored rule (`Common/Anchored.lean`) reads its wave at the kind in
four places, and a rule with a varying wave must read it at the kind in
all four:

* **eligibility** — `decisionRound k = S.slotRound k + R.waveAt (S.kind k)`,
  and `Eligible` with it; the rule's `waveAt : ℕ → ℕ` is a function of
  the kind;
* **the direct commit** — `Commit U V L r κ` is handed the slot's kind
  `κ` beside its round `r`, by `Decided.directCommit` as `S.kind k`;
* **the direct skip and the rungs** — `Skip U V S k` and `Link i U A L S k`
  already receive the schedule and the slot, and read `S.kind k`.

The support (`Properties/Support.lean`) reads it once more:
`Support.waveAt : ℕ → ℕ` is a function of the kind, `certifiesAt U T r κ L`
asks for certifiers at `r + waveAt κ`, and `Commits` and `live` read
`waveAt (S.kind k)`.

What carries it: `Rebases.kind` (so `Truncates`, `Sustains`, `Rebased`,
every `Stack`), `Slots.chop`, and the configuration's `rebases_chop`.
What asks its agreement: `Banded`'s two schedules on the band, the four
`BandLaws` at the slot each concerns, `LinkCongr` and `Laws.skip_congr`,
and the reassignment clauses of `DecidedBelow`, `Indirect` and
`exists_roundLocal`. What no longer asks anything of the wave:
`AnchoredRule.banded`, `certifiesAt_of_rebased`, `live_of_truncates`,
`live_of_rebased` and `Stack.safe_and_live`.

## 3. What a varying-wave rule writes

Steelhead writes it in six files under `LeanDag/Steelhead/` and its two
witnesses, and every edit is one of the following. `w : ℕ → ℕ` is the
rule's wavelength function, of the kind.

**The model** (`Steelhead/Model/Decision.lean`). Read `w` at the kind in
each of the four places of §2:

```lean
waveAt := fun κ => w κ - 1
Commit := fun U V L r κ => MahiMahi.DirectCommitIn U V (w κ) L r
Skip   := fun U V S k => MahiMahi.DirectSkipIn U V (w (S.kind k)) (S.leader k) (S.slotRound k)
Link   := fun _ U A L S k => MahiMahi.CertifiedIn U (w (S.kind k)) A L (S.slotRound k)
```

The `Decidable` instances take the kind as one more argument.

**The laws** (`Steelhead/Helpers/Decision.lean`). Every `w (S.slotRound k)`
becomes `w (S.kind k)`; every `R.Commit U V L (S.slotRound k)` becomes
`R.Commit U V L (S.slotRound k) (S.kind k)`. `skip_congr` receives the
kind agreement as a premise and rewrites with it; `link_congr` is
`linkCongr_of_round_kind`, which takes the link as a function of the
round and the kind. A claim that names a slot's mode — Steelhead's
SH5b, that at an asynchronous slot the direct predicates are the
chain's — asks that the slot carry the asynchronous kind,
`S.kind r = 1`, beside `S.slotRound r = r`.

**The properties** (`Steelhead/Properties.lean`). `CommitsDirect`'s
predicate takes the kind, `fun V L r κ => …`; `Indirect`'s eligibility
takes the schedule, `fun S i j => S.slotRound i + w (S.kind i) ≤ S.slotRound j`;
`Local` and `OfCoverage` take one more binder, the kind, in place of
reading the candidate's round; `Commits` takes one more `intro` for the
kinds the reassignment clause holds fixed. The extension laws are no
longer written at all: they are the band laws below, at offset zero.

**The statements** (`Steelhead/Safety/Statement.lean`). A claim about
the wave takes the kind beside the round rather than reading the wave
at the round, and a claim about a slot's direct commit hands it
`(S.kind k)`.

**The band, which is new.** The rule's band laws are the underlying
one-wave rule's, at the wave of the slot's kind, the band's kind
agreement rewriting the target's wave into the source's:

```lean
theorem steelheadBandLaws (hw : ∀ κ, 2 ≤ w κ) : (steelheadAnchored … w).BandLaws where
  commit_band := fun {S S' …} hab hkk hlk hkind hlo hhi hV hL hc => by
    have h := (mahiMahiBandLaws (hw (S.kind k))).commit_band (agreeBand_mm _ hab)
      hkk hlk hkind hlo hhi hV hL hc
    change MahiMahi.DirectCommitIn _ _ (w (S'.kind k')) _ _
    rw [← hkind]; exact h
  -- skip_band, link_band, link_novel: the same four lines each
```

and then, with no hypothesis on the wave beyond the `2 ≤ w κ` the laws
already ask:

```lean
theorem banded        (hw) : Banded (steelheadRule w)        := AnchoredRule.banded (steelheadBandLaws hw)
theorem localTruncate (hw) : LocalTruncate (steelheadRule w) := LocalTruncate.of_banded (banded hw)
theorem safety        (hw) : Properties.Safe (steelheadRule w) :=
  Properties.safety (banded hw) (agree hw) (commitsCandidate w)
```

These are the three claims the arc could not make while its wave was
read from the round. Every consumer of `Banded` — `Stack.safe_and_live`,
the `Record.lean` cells, the GC theorems, the joiner — applies to the
rule unchanged, and `Stack.safe_and_live`'s liveness clause carries the
support's precondition across any stack with no condition on the
wave.

**The witnesses** (`LeanDagTest/Steelhead/Model.lean`). A model whose
schedule leaves the kind at its default reads `w 0` at every slot. The
schedule says the kinds:

```lean
local instance shSlots : Slots (Fin 4) :=
  { Slots.uniformSingle 1 (by omega) (fun k => ⟨(k + 1) % 4, by omega⟩) with
    kind := fun k => periodicKind 4 k }
```

and each `sh.Commit sh8 V L r` gains the slot's kind as a last argument.
Every `decide` then settles as before.

## 4. How Steelhead spells the schedule's kind

**The kind is the mode**, and nothing else: `0` for a synchronous slot,
`1` for an asynchronous one. `Model/Wavelength.lean` names the two
halves of the paper's formula, `wavelength ws wa : ℕ → ℕ` for the wave
of a kind and `periodicKind p : ℕ → ℕ` for the kind of a round, keeps
`periodic ws wa p` as the paper's `w(r)`, and SH4 carries the identity
between them, `wavelength ws wa (periodicKind p r) = periodic ws wa p r`.
A schedule sets `kind k = periodicKind p (S.slotRound k)`, and `IsAsync
p r` becomes `S.kind r = 1`. Kind `0` is what `Slots.kind` assigns when
a schedule says nothing, so a schedule with no kinds reads `ws`
everywhere and the rule is Mahi-Mahi's at that wave.

Another varying-wave rule need not follow this. **The kind is the
round**, `kind := fun k => S.slotRound k` with `w := periodic ws wa p`
reading the round through it, works just as well and is the smaller
diff. A rebase by `G` carries the kinds either way, so a chopped
validator's slot `k` still reads `w` at the global round
`S.slotRound (d + k)`, as it should: a slot's mode is a fact about the
run, not about a validator's local numbering.

Nothing in the rule's proofs depends on periodicity: the laws hold at
any `w` with `2 ≤ w κ`, and a wave that is not periodic — an epoch's
worth of one mode, then another — is a schedule that says so.

## 5. What a kinded rule does not have

Barnacle's `ofAnchored R hw` keeps `hw : ∀ κ, R.waveAt κ = R.waveAt 0`.
A base rule has one wave length, `LiveRule.Descent` reads one gap at
every schedule its `indirect` clause quantifies over, and
`Descent.indirect` does not follow from the rule's own indirect law at
any other gap — its intermediates hypothesis quantifies over slots a
different gap does not reach. So a rule whose wave varies with the
kind is banded, truncation-local and safe, but is not a Barnacle base
rule until the descent laws take a gap per kind. Barnacle's own
schedules assign every slot kind `0`, so for a one-wave rule the guard
is `rfl`.
