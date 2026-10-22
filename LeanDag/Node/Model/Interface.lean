import LeanDag.Scheme.Model.TryDecide
/-!
# An honest node — its interface

`docs/validator.md` §2. A node runs one row of the scheme as a pure
transition function from inputs to outputs. `Config` fixes the row, the
quorum, the node's identity, the schedule, the timeouts, the vote rule,
the identifier map and the mechanisms' constants; `Input` and `Output`
are the events it consumes and produces, with those of garbage
collection, checkpoints and bootstrap included. A node's decisions are
chained by the environment's hash (`Config.headOf`), and a proposal signs
a height and the chain's head there. A checkpoint certificate (`Cert`)
carries a height, a head, and the validators whose signed proposals of
them it holds; the decisions themselves travel only with a certificate
served to a joiner.

The node checks the row's validity `rowValid q` on receipt, and decides
on a record of its own store at `stored`, references one round below,
which a store cut at a horizon also meets, and the honest set `∅`.

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
  /-- The horizon's lag `Λ`. -/
  lag : ℕ
  /-- The heights above its next undecided slot at which a node keeps
  every proposal of each signer. -/
  ahead : ℕ
  /-- The payload of the node's round-`r` block. -/
  payload : ℕ → Payload
  /-- The environment's hash of a chain's head extended by a decision. -/
  extend : BlockId → ℕ × Option BlockId → BlockId
  /-- The head of the empty chain. -/
  root : BlockId

variable {Validator BlockId Payload}

namespace Config

variable (cfg : Config Validator BlockId Payload)

/-- The schedule. -/
abbrev slots : Slots Validator :=
  Slots.uniform cfg.per cfg.m cfg.per_pos cfg.m_pos cfg.elect cfg.elect_block

/-- **The head of a chain of decisions.** -/
def headOf (ds : List (ℕ × Option BlockId)) : BlockId := ds.foldl cfg.extend cfg.root

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

/-- **A checkpoint certificate**: a height, the head of the chain of the
decisions of the slots below it, and the validators whose signed
proposals of this head at this height it carries. -/
structure Cert where
  /-- The number of slots certified. -/
  height : ℕ
  /-- The head of the chain of the decisions of slots `0 … height − 1`. -/
  head : BlockId
  /-- The signers. -/
  signers : List Validator

/-- **What a node persists** across a crash (`docs/validator.md` §5.1):
its accepted blocks, from the horizon up, the horizon, the next
undecided slot, its top round and its own block there, its decisions,
the height it last proposed and the chain's head there, and its
certificate. -/
structure Persisted where
  /-- The accepted blocks from the horizon up, the node's own among them. -/
  window : List (BlockId × Block Validator BlockId Payload)
  /-- The horizon. -/
  horizon : ℕ
  /-- The next undecided slot. -/
  lo : ℕ
  /-- The node's top round, once started. -/
  top : Option ℕ
  /-- The node's own block at its top round, if it built there. -/
  own : Option BlockId
  /-- The decisions the node output, the latest first. -/
  decided : List (ℕ × Option BlockId)
  /-- The height the node last proposed. -/
  lastProposed : ℕ
  /-- The head of the chain of its decisions below that height. -/
  chain : BlockId
  /-- The highest certificate the node holds. -/
  cert : Option (Cert Validator BlockId)

/-- **What a node consumes.** -/
inductive Input where
  /-- Start with nothing persisted: build the genesis block. -/
  | start
  /-- A block, with its identifier. -/
  | deliver (id : BlockId) (b : Block Validator BlockId Payload)
  /-- The timer of round `r` fired. -/
  | timer (r : ℕ)
  /-- A crash and restart: the node keeps only what it persisted. -/
  | restart
  /-- A peer's base: its horizon `G`. -/
  | baseOffer (peer : Validator) (G : ℕ)
  /-- A peer asks for the base. -/
  | baseRequest (peer : Validator)
  /-- A peer at horizon `G` asks for the blocks `ids` and their histories. -/
  | fetchRequest (peer : Validator) (G : ℕ) (ids : List BlockId)
  /-- A peer's signed proposal of the head `h` of the chain of the
  decisions of slots `0 … k − 1`. -/
  | proposal (peer : Validator) (k : ℕ) (h : BlockId)
  /-- A peer's certificate, with the decisions it certifies: all of them,
  served with its base, or those from a slot asked for. -/
  | certOffer (peer : Validator) (c : Cert Validator BlockId) (ds : List (ℕ × Option BlockId))
  /-- A peer asks for the decisions certified from slot `lo` up. -/
  | decisionRequest (peer : Validator) (lo : ℕ)
  /-- A peer's certificate, announced without decisions. -/
  | announced (peer : Validator) (c : Cert Validator BlockId)

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
  /-- Blocks below round `G` may be discarded. -/
  | prune (G : ℕ)
  /-- Ask every peer for its base. -/
  | requestBase
  /-- Send the horizon `G` to a peer as its base. -/
  | serveBase (peer : Validator) (G : ℕ)
  /-- Ask the peer for the blocks `ids` and their histories above the
  horizon `G`. -/
  | fetch (peer : Validator) (G : ℕ) (ids : List BlockId)
  /-- Send a block to one peer. -/
  | send (peer : Validator) (id : BlockId) (b : Block Validator BlockId Payload)
  /-- Sign and send every peer a proposal of the head `h` of the chain of
  the decisions of slots `0 … k − 1`. -/
  | propose (k : ℕ) (h : BlockId)
  /-- Send the certificate to a peer, with the decisions it certifies. -/
  | serveCert (peer : Validator) (c : Cert Validator BlockId) (ds : List (ℕ × Option BlockId))
  /-- Ask a peer for the decisions it certified from slot `lo` up. -/
  | requestDecisions (peer : Validator) (lo : ℕ)
  /-- Send the certificate to every peer, without decisions. -/
  | announce (c : Cert Validator BlockId)
  /-- Send another author's block to every peer: one of two blocks of one
  author at one round, the evidence of its equivocation. -/
  | relay (id : BlockId) (b : Block Validator BlockId Payload)

end Node

end LeanDag
