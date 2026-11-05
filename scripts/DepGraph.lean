import LeanDag
import LeanDagTest

/-!
# Declaration dependency extraction

Walks the compiled environment and emits, for every `LeanDag`/`LeanDagTest`
declaration, the constants it mentions — in its type *and* in its proof
term. Run from the repository root with

    lake env lean scripts/DepGraph.lean

It writes `docs/depgraph/deps.tsv` itself rather than printing: output of
`#eval` is captured as a message, and formatting a message of this size took
minutes where the walk takes seconds.

Output is tab-separated, two record kinds:

    NODE <name> <module> <kind>
    EDGE <name> <dependency>

`kind` is `thm` for proofs, `def` for definitions, `ind` for inductives
and structures, `ax` for axioms. Only edges between kept declarations are
emitted; Mathlib and core dependencies are dropped, since the question is
which results of *this* development support which others.
-/

open Lean

/-- A declaration's user-facing name. Private declarations are stored under
a mangled `_private.<Module>.<idx>.` prefix, so testing the raw name against
`LeanDag` rejects every one of them. Everything else is its own name. -/
def userName (n : Name) : Name := privateToUserName n

/-- Keep every declaration of this development, **including** private and
compiler-generated ones: a proof of one labelled result frequently reaches
another only through a private auxiliary or a `.proof_N`, and dropping those
would silently sever the path. Mathlib and core constants are excluded, and
safely so — they never mention a `LeanDag` constant, so no path between two
of our results can run through them.

The test is on the *user* name. Testing the stored name instead dropped
every private declaration — 53 of them — which is exactly the severing
this comment warns against, and it went unnoticed because the graph then
reports a shorter path rather than an error. -/
def keepName (n : Name) : Bool :=
  let n' := userName n
  (`LeanDag).isPrefixOf n' || (`LeanDagTest).isPrefixOf n'

def kindOf : ConstantInfo → String
  | .thmInfo _ => "thm"
  | .axiomInfo _ => "ax"
  | .inductInfo _ => "ind"
  | .ctorInfo _ => "ctor"
  | .recInfo _ => "rec"
  | _ => "def"

/-- Constants mentioned in a declaration's type *and* in its body. For
theorems the body is the proof term, which `ConstantInfo.value?` does not
surface for imported declarations — hence the explicit match. -/
def usedConsts (ci : ConstantInfo) : NameSet :=
  let s := ci.type.getUsedConstantsAsSet
  match ci with
  | .thmInfo tv => s.union tv.value.getUsedConstantsAsSet
  | .defnInfo dv => s.union dv.value.getUsedConstantsAsSet
  | .opaqueInfo ov => s.union ov.value.getUsedConstantsAsSet
  | _ => s

#eval show CoreM Unit from do
  let env ← getEnv
  let mut out : Array String := #[]
  for (n, ci) in env.constants.toList do
    if keepName n then
      let mod := match env.getModuleFor? n with
        | some m => m.toString
        | none => "«local»"
      out := out.push s!"NODE\t{userName n}\t{mod}\t{kindOf ci}"
      for d in (usedConsts ci).toList do
        if keepName d && userName d != userName n then
          out := out.push s!"EDGE\t{userName n}\t{userName d}"
  IO.FS.writeFile "docs/depgraph/deps.tsv" (String.intercalate "\n" out.toList ++ "\n")
