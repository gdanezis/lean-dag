import LeanDag.RedSnapper.Model.Five.Freeze
import LeanDag.RedSnapper.Model.Verdict

/-!
# The 5f+1 verdicts

Trusted core: the four decision routes of `Alg:snapper5f`'s
`TryDecide` — `TryFullDecideTX`, `TryFullUnlockObj`,
`FinalizeOnCommitTX` (both loops), `ResolveOnCommitObj` — as one order-free
inductive relation, the D6 pattern: a constructor per route, any
derivable verdict counts, and that all derivable verdicts agree is
RS8's theorem, never a side condition. `Fate` is shared with the `3f+1`
verdict.

Owned and mixed transactions compete on their owned input, and the
class decides only where a full certificate takes effect: an owned
transaction finalises on one observation (`fullFinal`), a mixed one at
a committed anchor whose history holds the certificate (`mixedFinal`),
since it must be ordered first (D9).

`FinalizeOnCommitTX`'s first loop aborts every candidate, owned or
mixed, of an object already in `decidedObj` (the paper's fix of record
finding 33: before it the loop was mixed-only, and the loser of a fast
commit was never decided). That local set is rendered by what put the
object there. An owned rival finalized on an observed full certificate
is `observedRivalDrop`, which reads the view as `fullFinal` does. A
rival, of either class, fully certified in the anchor's history is
`certifiedRivalDrop`. A resolution at an earlier anchor that the
transaction did not win is `resolvedDrop`. A release by a full unlock
certificate needs no new route: `fullUnlockDrop` drops a candidate seen
anywhere in the view. The rendering is exact up to one anchor of timing,
in both directions: the validator's loop runs before the second loop
and the recovery of the same anchor, so it aborts at the next anchor
what the relation drops at this one; and it runs only once an anchor is
processed, where `observedRivalDrop` asks for any committed anchor.

The consensusless routes read a **view** and decide on a *single*
observed certificate block — finality in one observation, unlike the
`3f+1` round quorum. The unlock route drops every candidate of
the object seen anywhere in the view (the algorithm's
`K = ⋃_{b ∈ DAG[r]} Candidates(b, o)`, at the one call that decides the
object; a candidate seen later is aborted by `FinalizeOnCommitTX`'s
first loop, and reading the whole view renders both at once). The recovery
route reads the global `(U, A)` of D4, so its cross-validator agreement
is definitional; it commits the eligible candidate minimal under
`prio`, the algorithm's fixed hash order rendered as a linear-order
parameter (D8's treatment of the coin) — `RecoverySafetyWin` holds for
an arbitrary member of `W`, so the tie-break carries no safety weight.

The algorithm's `decidedObj` one-shot and route precedence appear as no
clause, exactly as in the `3f+1` relation: RS8 proves the routes never
disagree.
-/

namespace LeanDag

namespace RedSnapper

variable {Validator BlockId Tx Obj : Type*} [Fintype Validator] [DecidableEq Validator]
  [DecidableEq BlockId] [F : Faults Validator] [T : Transactions Tx Obj]

/-- The verdict relation at `5f+1`: `VerdictFive U A V prio tx f` — the
validator holding view `V`, over the committed anchors `A` and the
fixed transaction order `prio`, can justify fate `f` for `tx`. -/
inductive VerdictFive (U : Universe Validator BlockId Tx Obj) (A : Anchors U) (V : View U)
    (prio : Tx → Tx → Prop) : Tx → Fate → Prop where
  /-- Consensusless finality (`TryFullDecideTX`): one observed full
  certificate finalises an owned transaction. -/
  | fullFinal {tx : Tx} {C : BlockId} :
      Owned tx →                        -- the IsOwned gate (D9)
      C ∈ V.ids →                       -- a block of the view ...
      IsFullCert U C tx →               -- ... carrying a full certificate
      VerdictFive U A V prio tx Fate.finalized
  /-- Consensusless release (`TryFullUnlockObj`): one observed full
  unlock certificate drops every candidate of the object. -/
  | fullUnlockDrop {tx : Tx} {C b : BlockId} :
      C ∈ V.ids →                       -- a block of the view ...
      IsFullUnlockCert U C (T.input tx) →  -- ... unlocking the input
      b ∈ V.ids →                       -- and the dropped transaction is
      IsCandidate U b (T.input tx) tx → -- a candidate seen in the view
      VerdictFive U A V prio tx Fate.dropped
  /-- Commit at an anchor (`FinalizeOnCommitTX`): a mixed transaction
  the anchor includes, fully certified in the anchor's history. -/
  | mixedFinal {tx : Tx} {i : ℕ} {a C : BlockId} :
      T.Mixed tx →                      -- the IsMixed gate: the consensus route
      A.seq[i]? = some a →              -- a committed anchor
      IsCandidate U a (T.input tx) tx → -- Includes(A, tx), valid: implied by the
                                        -- certificate below, kept as the paper has it
      C ∈ U.ids → Reaches U a C →       -- ∃ b, Link(b, A) ...
      IsFullCert U C tx →               -- ... carrying a full certificate
      VerdictFive U A V prio tx Fate.finalized
  /-- Drop beside an observed fast commit (`FinalizeOnCommitTX`, first
  loop): a candidate of a committed anchor, with an owned rival's full
  certificate in the view. -/
  | observedRivalDrop {tx tx' : Tx} {i : ℕ} {a C : BlockId} :
      A.seq[i]? = some a →              -- a committed anchor
      IsCandidate U a (T.input tx) tx → -- tx ∈ Candidates(A, o) ...
      Conflict tx tx' →                 -- ... with o ∈ decidedObj: a rival that
      Owned tx' →                       -- TryFullDecideTX finalized, on a full
      C ∈ V.ids → IsFullCert U C tx' →  -- certificate the view holds (`fullFinal`)
      VerdictFive U A V prio tx Fate.dropped
  /-- Drop beside a certified rival (`FinalizeOnCommitTX`, first loop): a
  candidate of an anchor whose history holds a rival's full
  certificate. -/
  | certifiedRivalDrop {tx tx' : Tx} {i : ℕ} {a C : BlockId} :
      A.seq[i]? = some a →              -- a committed anchor
      IsCandidate U a (T.input tx) tx → -- tx ∈ Candidates(A, o) ...
      Conflict tx tx' →                 -- ... with o ∈ decidedObj: a rival
      C ∈ U.ids → Reaches U a C →       -- fully certified in the anchor's history —
      IsFullCert U C tx' →              -- a mixed one is final at this anchor
      VerdictFive U A V prio tx Fate.dropped
  /-- Drop above a resolution (`FinalizeOnCommitTX`, first loop): a
  candidate of an anchor above the one that resolved its object, not the
  winner there. -/
  | resolvedDrop {tx : Tx} {i j m : ℕ} {aₖ aⱼ a : BlockId} :
      ResolvesFiveAt U A (T.input tx) i j →
      A.seq[i]? = some aₖ → A.seq[j]? = some aⱼ →
      A.seq[m]? = some a → j < m →      -- a later committed anchor ...
      IsCandidate U a (T.input tx) tx → -- ... with tx ∈ Candidates(A, o), o ∈ decidedObj
      ¬ (EligibleFive U aₖ aⱼ (T.input tx) tx ∧
          ∀ tx', EligibleFive U aₖ aⱼ (T.input tx) tx' → prio tx tx') →
                                        -- and tx ≠ win at the resolution
      VerdictFive U A V prio tx Fate.dropped
  /-- The recovery commit (`ResolveOnCommitObj`, `win = tx`): at the
  resolving anchor, the transaction is eligible and `prio`-minimal
  among the eligible. -/
  | recoveryFinal {tx : Tx} {i j : ℕ} {aₖ a : BlockId} :
      ResolvesFiveAt U A (T.input tx) i j →
      A.seq[i]? = some aₖ → A.seq[j]? = some a →
      EligibleFive U aₖ a (T.input tx) tx →     -- tx ∈ W ...
      (∀ tx', EligibleFive U aₖ a (T.input tx) tx' → prio tx tx') →
                                        -- ... and minimal under the fixed order
      VerdictFive U A V prio tx Fate.finalized
  /-- The recovery drop of a loser (`win = tx' ≠ tx`): a candidate that
  is not the winner is dropped at the resolving anchor. -/
  | recoveryDropLoser {tx tx' : Tx} {i j : ℕ} {aₖ a : BlockId} :
      ResolvesFiveAt U A (T.input tx) i j →
      A.seq[i]? = some aₖ → A.seq[j]? = some a →
      IsCandidate U a (T.input tx) tx →         -- tx ∈ K ...
      EligibleFive U aₖ a (T.input tx) tx' →    -- ... while the winner
      (∀ tx'', EligibleFive U aₖ a (T.input tx) tx'' → prio tx' tx'') →
      tx ≠ tx' →                                -- ... is someone else
      VerdictFive U A V prio tx Fate.dropped
  /-- The recovery release (`win = ⊥`): with nothing eligible, every
  candidate is dropped and the object released. -/
  | recoveryDropBot {tx : Tx} {i j : ℕ} {aₖ a : BlockId} :
      ResolvesFiveAt U A (T.input tx) i j →
      A.seq[i]? = some aₖ → A.seq[j]? = some a →
      IsCandidate U a (T.input tx) tx →         -- tx ∈ K ...
      (∀ tx', ¬ EligibleFive U aₖ a (T.input tx) tx') →  -- ... and W is empty
      VerdictFive U A V prio tx Fate.dropped

end RedSnapper

end LeanDag
