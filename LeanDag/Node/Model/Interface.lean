import LeanDag.Scheme.Model.TryDecide
/-!
# An honest node — its interface

`docs/validator.md` §2. A node runs one row of the scheme as a pure
transition function from inputs to outputs. `Config` fixes the row, the
quorum, the node's identity, the schedule, the timeouts, the vote rule,
the identifier map and the payload source; `Input` and `Output` are the
events it consumes and produces.

The node checks the row's validity `rowValid q` on receipt, and decides
on a record of its own store at `stored`, references one round below,
and the honest set `∅`.

Definitions only.
-/

namespace LeanDag

namespace Node

variable {Validator BlockId Payload : Type} [DecidableEq Validator]

/-- **The node's validity**: references one round below from `q`
distinct authors, no author twice. Referencing the author's own previous
block is the honest build rule, not a validity clause (`docs/validator.md`
§11). -/
abbrev rowValid (q : ℕ) : Validity Validator BlockId Payload :=
  ValidAt q Clause.distinct

variable (Validator BlockId Payload) in
/-- **The validity a store's record carries**: references one round
below. -/
abbrev stored : Validity Validator BlockId Payload := ValidAt 0 Clause.none

variable (Validator BlockId Payload) [Fintype Validator] [LinearOrder BlockId]

/-- **A node's configuration.** The schedule is the scheme's,
`Slots.uniform per m elect`: `m` leaders every `per` rounds. -/
structure Config where
  /-- The row. -/
  p : Scheme.Params
  /-- The Byzantine bound. -/
  f : ℕ
  /-- The crash bound. -/
  c : ℕ
  /-- The quorum: authors a block references, and a round needs to advance. -/
  q : ℕ
  /-- The node itself. -/
  me : Validator
  /-- Rounds between slot rounds. -/
  per : ℕ
  /-- Leaders per slot round. -/
  m : ℕ
  per_pos : 0 < per
  m_pos : 0 < m
  /-- The leader of slot `k`. -/
  elect : ℕ → Validator
  /-- Distinct slots of one slot round have distinct leaders. -/
  elect_block : ∀ k₁ k₂, k₁ / m = k₂ / m → elect k₁ = elect k₂ → k₁ = k₂
  /-- The timeout of round `r`. -/
  timeout : ℕ → ℕ
  /-- The vote rule. -/
  σ : Scheme.VoteSel Validator BlockId Payload (stored Validator BlockId Payload) ∅
  /-- The identifier of a block: the environment's hash. -/
  idOf : Block Validator BlockId Payload → BlockId
  /-- The payload of the node's round-`r` block. -/
  payload : ℕ → Payload

variable {Validator BlockId Payload}

namespace Config

variable (cfg : Config Validator BlockId Payload)

/-- The schedule. -/
abbrev slots : Slots Validator :=
  Slots.uniform cfg.per cfg.m cfg.per_pos cfg.m_pos cfg.elect cfg.elect_block

/-- The slots proposed at round `r`. -/
def slotsAt (r : ℕ) : List ℕ :=
  if r % cfg.per = 0 then (List.range cfg.m).map (fun i => cfg.m * (r / cfg.per) + i) else []

/-- **An admissible configuration**: the row is covered at the
committee's size, the bound `f` and the quorum `q`, its certificates fit
the quorum, and its commit threshold is reachable by the validators
neither Byzantine nor crash-prone, which is what liveness reads; a row
whose skip threshold is unreachable skips by the indirect rule; a
quorum holds a node that is not Byzantine, which is what a checkpoint
certificate reads; and a direct skip needs a block, which is what a
bootstrap reads. -/
def Admissible : Prop :=
  cfg.p.Covered (Fintype.card Validator) cfg.f cfg.q ∧ cfg.p.CertFits cfg.q ∧
    cfg.p.commitThreshold ≤ Fintype.card Validator - cfg.f - cfg.c ∧ 0 < cfg.q ∧
    cfg.q ≤ Fintype.card Validator ∧ cfg.f < cfg.q ∧ 0 < cfg.p.skipThreshold

instance : Decidable cfg.Admissible := by
  unfold Admissible Scheme.Params.Covered Scheme.Params.CertFits
    Scheme.Params.TwoRound Scheme.Params.ThreeRound Scheme.Params.TwoRoundCrash
    Scheme.Params.ThreeRoundCrash
  infer_instance

end Config

variable (Validator BlockId Payload)

/-- **What a node consumes.** -/
inductive Input where
  /-- Start: build the genesis block. -/
  | start
  /-- A block, with its identifier. -/
  | deliver (id : BlockId) (b : Block Validator BlockId Payload)
  /-- The timer of round `r` fired. -/
  | timer (r : ℕ)
  /-- A peer asks for the blocks `ids` and their histories. -/
  | fetchRequest (peer : Validator) (ids : List BlockId)

/-- **What a node produces.** -/
inductive Output where
  /-- Write a block to storage; emitted before the block is broadcast. -/
  | persist (id : BlockId) (b : Block Validator BlockId Payload)
  /-- Send a block to every peer. -/
  | broadcast (id : BlockId) (b : Block Validator BlockId Payload)
  /-- Call back with `Input.timer r` after `after` ticks. -/
  | setTimer (r : ℕ) (after : ℕ)
  /-- Slot `k` is decided: committed to a block, or skipped. -/
  | commit (k : ℕ) (d : Option BlockId)
  /-- Ask the peer for the blocks `ids` and their histories. -/
  | fetch (peer : Validator) (ids : List BlockId)
  /-- Send a block to one peer. -/
  | send (peer : Validator) (id : BlockId) (b : Block Validator BlockId Payload)

end Node

end LeanDag
