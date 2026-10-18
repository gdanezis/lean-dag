import LeanDag.Scheme.Model.TryDecide
/-!
# An honest node — its interface

`docs/validator.md` §2. A node runs one row of the scheme as a pure
transition function from inputs to outputs. `Config` fixes the row, the
quorum, the node's identity, the schedule, the timeouts, the vote rule,
the identifier map and the mechanisms' constants; `Input` and `Output`
are the events it consumes and produces, with those of garbage
collection, Safe Skip and bootstrap included.

The node decides on a record of its own store, which checks no validity
and constrains no author (`anyValid`, the honest set `∅`): it checks
validity itself, on receipt, against `rowValid q`.

Definitions only.
-/

namespace LeanDag

namespace Node

variable (Validator BlockId Payload : Type)

/-- The validity a store's record carries: none, since the node checks
validity on receipt. -/
def anyValid : Validity Validator BlockId Payload := fun _ _ => True

variable {Validator BlockId Payload} [DecidableEq Validator]

/-- **The node's validity**: references one round below from `q`
distinct authors, no author twice, and the author's own previous block. -/
abbrev rowValid (q : ℕ) : Validity Validator BlockId Payload :=
  ValidAt q (Clause.distinct.and Clause.selfParent)

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
  σ : Scheme.VoteSel Validator BlockId Payload (anyValid Validator BlockId Payload) ∅
  /-- The identifier of a block: the environment's hash. -/
  idOf : Block Validator BlockId Payload → BlockId
  /-- The horizon's lag `Λ`. -/
  lag : ℕ
  /-- The novelty budget `τ`. -/
  budget : ℕ
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
committee's size, the bound `f` and the quorum `q`, its certificates fit,
and its thresholds are reachable by the non-faulty validators. -/
def Admissible : Prop :=
  cfg.p.Covered (Fintype.card Validator) cfg.f cfg.q ∧ cfg.p.CertFits cfg.q ∧
    cfg.p.Live (Fintype.card Validator) cfg.f cfg.c ∧ 0 < cfg.q ∧ cfg.q ≤ Fintype.card Validator

instance : Decidable cfg.Admissible := by
  unfold Admissible Scheme.Params.Covered Scheme.Params.CertFits Scheme.Params.Live
    Scheme.Params.TwoRound Scheme.Params.ThreeRound Scheme.Params.TwoRoundCrash
    Scheme.Params.ThreeRoundCrash
  infer_instance

end Config

variable (Validator BlockId Payload)

/-- **What a node persists** across a crash (`docs/validator.md` §5.1):
its accepted blocks above the horizon, the horizon, and the next
undecided slot. -/
structure Persisted where
  /-- The accepted blocks above the horizon, the node's own among them. -/
  window : List (BlockId × Block Validator BlockId Payload)
  /-- The horizon. -/
  horizon : ℕ
  /-- The next undecided slot. -/
  lo : ℕ

/-- **What a node consumes.** -/
inductive Input where
  /-- Start with nothing persisted: build the genesis block. -/
  | start
  /-- A block, with its identifier. -/
  | deliver (id : BlockId) (b : Block Validator BlockId Payload)
  /-- A jump message: `v1` resumes after its block `B1` along `v2`'s
  line through `B2`. -/
  | jump (v1 : Validator) (B1 : BlockId) (v2 : Validator) (B2 : BlockId)
  /-- The timer of round `r` fired. -/
  | timer (r : ℕ)
  /-- Restart from what was persisted. -/
  | restart (ps : Persisted Validator BlockId Payload)
  /-- A peer's base: its round-`G` blocks and its window above them. -/
  | baseOffer (peer : Validator) (G : ℕ) (blocks : List (BlockId × Block Validator BlockId Payload))
  /-- A peer asks for the base. -/
  | baseRequest (peer : Validator)

/-- **What a node produces.** -/
inductive Output where
  /-- Write a block to storage; emitted before the block is broadcast. -/
  | persist (id : BlockId) (b : Block Validator BlockId Payload)
  /-- Send a block to every peer. -/
  | broadcast (id : BlockId) (b : Block Validator BlockId Payload)
  /-- Send a jump message to every peer. -/
  | jump (v1 : Validator) (B1 : BlockId) (v2 : Validator) (B2 : BlockId)
  /-- Call back with `Input.timer r` after `after` ticks. -/
  | setTimer (r : ℕ) (after : ℕ)
  /-- Slot `k` is decided: committed to a block, or skipped. -/
  | commit (k : ℕ) (d : Option BlockId)
  /-- Blocks below round `G` may be discarded. -/
  | prune (G : ℕ)
  /-- Ask every peer for its base. -/
  | requestBase
  /-- Send the base and window to a peer. -/
  | serveBase (peer : Validator) (G : ℕ) (blocks : List (BlockId × Block Validator BlockId Payload))

end Node

end LeanDag
