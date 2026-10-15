import VampireHammer.TFF
import VampireHammer.THF.Syntax

/-!
The data contract between TPTP decoding, sequential replay, and rule handlers.

These structures carry formulas, parent proofs, and certificates; they do not
parse annotations or construct proofs. Public names remain in `Backend` so
existing replay code can keep importing `VampireHammer.Backend`.
-/

namespace VampireHammer.Backend

private instance [BEq ε] [BEq α] : BEq (Except ε α) where
  beq
    | .ok a, .ok b => a == b
    | .error a, .error b => a == b
    | _, _ => false

open Lean Meta Elab Tactic
open Auto.Embedding.Lam

/-- CNF occurrence indices refer to the printed parent; swaps refer to the
conclusion. Binder names are local to their respective formulas. -/
structure CnfCertificate where
  binders : Array (String × String)
  permutation : Array Nat
  swapped : Array Nat
  deriving Inhabited, Repr

/-- The useful part of TPTP's generic annotation language.

This is deliberately a *lossless enough* view of the parser annotation rather
than a proof-specific AST. A future rule can inspect an annotation that this
backend does not yet understand without changing the C parser or the rest of
the replay pipeline. -/
inductive MetadataTerm where
  /-- A lower-case or quoted TPTP name, such as `f17` or `t_a1`. -/
  | atom (name : String)
  /-- A TPTP variable, such as the `Y0` in `b(X0,Y0)`. -/
  | variable (name : String)
  /-- A generic annotation function and its arguments. -/
  | application (name : String) (arguments : Array MetadataTerm)
  /-- TPTP square brackets, used for unifier and literal-reference lists. -/
  | list (entries : Array MetadataTerm)
  /-- TPTP tuple syntax, retained for rules that use positional metadata. -/
  | tuple (entries : Array MetadataTerm)
  /-- The source spelling of a number; only literal indices currently consume it. -/
  | number (text : String)
  /-- A quoted TPTP distinct object. -/
  | distinctObject (text : String)
  /-- A `head : tail` general term. -/
  | annotated (head tail : MetadataTerm)
  /-- A formula embedded in metadata. The current rule handlers do not decode it. -/
  | formula
  /-- Embedded THF terms retain their binders/types, including a diagnostic
  for a syntax alternative outside the supported simply typed fragment. -/
  | higherOrder (value : Except String THF.Term)
deriving Repr, BEq, Nonempty

/-- The substitution recorded for one parent of a resolution inference.

The right-hand side remains `MetadataTerm` here. It can mention a variable of
the resolvent, which has no Lean local expression until that conclusion's
quantifiers are opened during reconstruction. -/
structure ParentSubstitution where
  /-- Name of the parent clause named by `subs(parent, ...)`. -/
  parent : String
  /-- Source-binder name paired with its raw Vampire substitution value. -/
  bindings : Array (String × MetadataTerm)
deriving Repr, BEq

/-- A literal occurrence reported by Vampire.  Indices are zero based, as in
the TPTP proof annotation. -/
structure LiteralRef where
  /-- Parent clause in which the selected literal occurs. -/
  parent : String
  /-- Zero-based literal position in Vampire's flattened clause order. -/
  index : Nat
deriving Repr, BEq

/-- Proposed HOL cases certificate: the selected Boolean subterm and the
truth value substituted into its selected literal. -/
structure BooleanCaseInfo where
  literal : LiteralRef
  term : MetadataTerm
  replaceWithTrue : Bool
  occurrence? : Option Nat := none
deriving Repr, BEq

/-- Resolve a witness's ordered dependency subset against the parent scope.
Names must be distinct and must each identify exactly one parent binder. -/
def witnessDependencyIndices? (scope dependencies : Array String) : Option (Array Nat) := do
  guard (scope.toList.eraseDups.length == scope.size)
  guard (dependencies.toList.eraseDups.length == dependencies.size)
  dependencies.mapM fun name => scope.findIdx? (· == name)

/-- A witness rule preserves the whole parent scope. An explicit mapping is a
bijection from parent names to child names; absent metadata preserves the old
identical-scope convention. Return child positions in parent application order. -/
def witnessBinderIndices? (parent child : Array String)
    (mapping? : Option (Array (String × String))) : Option (Array Nat) := do
  guard (parent.size == child.size)
  guard (parent.toList.eraseDups.length == parent.size)
  guard (child.toList.eraseDups.length == child.size)
  match mapping? with
  | none =>
    guard (parent == child)
    pure (Array.range parent.size)
  | some mapping =>
    guard (mapping.size == parent.size)
    guard ((mapping.map (·.1)).toList.eraseDups.length == mapping.size)
    guard ((mapping.map (·.2)).toList.eraseDups.length == mapping.size)
    parent.mapM fun source => do
      let some (_, target) := mapping.find? (·.1 == source) | none
      child.findIdx? (· == target)

/-- Proposed replay certificate for a fresh extensionality difference
witness. Dependencies enumerate its arguments in application order. -/
structure NegativeExtensionalityInfo where
  literal : LiteralRef
  symbol : String
  dependencies : Array String
  binderMapping? : Option (Array (String × String)) := none
deriving Repr, BEq

structure QuantifierWitnessInfo where
  literal : LiteralRef
  symbol : String
  /-- Parent variable names, when every dependency is a variable. -/
  dependencies : Array String
  binderMapping? : Option (Array (String × String)) := none
  /-- Dependencies printed as arbitrary `$thf` terms, for a witness Vampire
  reused from its Skolem index. Empty when `dependencies` applies. -/
  dependencyTerms : Array MetadataTerm := #[]
  /-- Whether this step introduces the symbol (`new_symbols`). A reuse
  refers to an already bound witness. -/
  introduce : Bool := true
deriving Repr, BEq

/-- `heuristic_instantiation`: the universal proxy in the selected literal is
replaced by its predicate applied to `term`; `substitutions` is the type
instantiation of the parent. -/
structure QuantifierInstanceInfo where
  substitutions : Array ParentSubstitution
  literal : LiteralRef
  term : MetadataTerm
deriving Repr, BEq

/-- Proposed monomorphic choice instance. The introduction flag binds a fresh
operator; later instances may reuse only an already interpreted operator. -/
structure ChoiceAxiomInfo where
  symbol : String
  predicate : MetadataTerm
  variableName : String
  introduce : Bool
deriving Repr, BEq

structure FunctionalExtensionalityInfo where
  symbol : String
  leftVariable : String
  rightVariable : String
  introduce : Bool
deriving Repr, BEq

/-- One occurrence in an annotated EUF-to-AVATAR SAT conversion. -/
structure AvatarMapping where
  source : LiteralRef
  symbol : String
  positive : Bool
  definition : String
deriving Repr, BEq

/-- Parsed metadata shared by Vampire's binary resolution inferences.

The complete original annotation remains in `Inference.info`. This smaller
view keeps only the unifier and the two selected literal occurrences. -/
structure ResolutionInfo where
  /-- Explicit parent substitutions. Forward subsumption may omit parents
  whose substitution is empty. -/
  substitutions : Array ParentSubstitution
  /-- One selected literal entry for each parent. -/
  resolvedLiterals : Array LiteralRef
deriving Repr, BEq

/-- Metadata for `constrained_resolution`: an ordinary binary-resolution
certificate plus the number of `constraints([disequality(...)])` entries.
Vampire places exactly these disequalities first in the conclusion. -/
structure ConstrainedResolutionInfo where
  resolution : ResolutionInfo
  constraintCount : Nat
deriving Repr, BEq

/-- Metadata for `forward_subsumption_resolution`.

Vampire's current certificate names only the literal removed from the first
(main) parent. The selected occurrence in the subsuming side clause is not
printed: the backend recovers it by checking complementarity and that every
remaining side literal occurs in the main remainder. -/
structure ForwardSubsumptionInfo where
  /-- Explicit substitutions; unchanged parents may be omitted. -/
  substitutions : Array ParentSubstitution
  /-- The literal deleted from the first parent. -/
  removedLiteral : LiteralRef
deriving Repr, BEq

/-- Metadata for Vampire's ordinary factoring rule.

Vampire records the parent substitution in the usual `unifier` field and
identifies the duplicate occurrence removed from that parent with
`removed_literal(literal(parent,index))`. After applying the substitution, the
handler checks that this occurrence is definitionally equal to another literal
in the same clause. -/
structure FactoringInfo where
  substitutions : Array ParentSubstitution
  removedLiteral : LiteralRef
deriving Repr, BEq

/-- The parent mgu recorded for equality resolution. The affected negative
equality is recovered by comparing the instantiated parent with the child. -/
structure EqualityResolutionInfo where
  substitutions : Array ParentSubstitution
deriving Repr, BEq

/-- The parent mgu recorded for equality factoring. The selected and retained
positive equalities are recovered from the grounded clause and checked against
the complete child literal sequence. -/
structure EqualityFactoringInfo where
  substitutions : Array ParentSubstitution
deriving Repr, BEq

/-- Metadata for the basic two-parent superposition fragment.

`rewrittenLiteral` names the parent that supplies the literal containing the
rewritten term; the other parent supplies a unit positive equality. Both parent
substitutions are applied before the ground clause theorem is used. -/
structure SuperpositionInfo where
  substitutions : Array ParentSubstitution
  rewrittenLiteral : LiteralRef
deriving Repr, BEq

/-- Parent-local substitutions printed for forward demodulation.

`rewrittenLiteral` identifies the literal in the parent being simplified.
The other parent supplies the unit positive equality. Vampire prints an
explicit empty substitution record when a parent retains its conclusion
variables unchanged. The literal reference is useful even though this backend
rewrites every occurrence: it prevents us from silently reversing the two
proof parents and makes the exact certificate occurrence visible in the trace. -/
structure ForwardDemodulationInfo where
  substitutions : Array ParentSubstitution
  rewrittenLiteral : LiteralRef
deriving Repr, BEq

/-- Explicit rewrite direction and equality occurrence in Vampire replay. -/
structure CertifiedRewriteInfo where
  substitutions : Array ParentSubstitution
  rewrittenLiterals : Array LiteralRef
  equality : LiteralRef
  fromTerm : MetadataTerm
  toTerm : MetadataTerm
  constraints : Array MetadataTerm := #[]
  /-- Zero-based non-overlapping matching occurrence in the selected literal.
  Absent for the legacy replacement-of-all-matches certificate. -/
  occurrence? : Option Nat := none
deriving Repr, BEq

/-- A fresh nullary proposition introduced by an AVATAR definition node.

Vampire prints these nodes with an internal `introduced(definition, ...)`
source rather than an ordinary inference record. `Replay` normalizes that
source to the synthetic rule name `avatar_definition`, while retaining the
certified fresh symbol here. -/
structure AvatarDefinitionInfo where
  symbol : String
deriving Repr, BEq

/-- A fresh predicate introduced by Vampire's formula naming
(`predicate_definition_introduction`).  Unlike an AVATAR component the symbol
takes arguments: the free variables of the named subformula. -/
structure PredicateDefinitionInfo where
  symbol : String
deriving Repr, BEq

/-- One source-clause variable assignment certified by
`avatar_split_clause`'s `post_rewrite_instantiation` annotation.

`arg(f148, X3)`, for example, denotes the value bound for `X3` when the
component defined by `f148` is expanded.  It is not a first-order term in the
TPTP signature; it names a binder created locally by the AVATAR definition.
The reconstruction handler resolves that name after prenexing the expanded
target. -/
structure AvatarSplitBinding where
  /-- The leading universal variable of the principal source clause. -/
  sourceVariable : String
  /-- Proof-DAG name of the AVATAR definition that supplies its value. -/
  definitionParent : String
  /-- Binder spelling within that definition's right-hand side. -/
  definitionVariable : String
deriving Repr, BEq

/-- The variable-recovery part of Vampire's extended AVATAR split
certificate.  The annotation is optional for simple splits, but is required
when the expanded definitions induce a non-identity universal-binder order. -/
structure AvatarSplitInfo where
  bindings : Array AvatarSplitBinding
deriving Repr, BEq

/-- One explicit replacement in Vampire's `skolemize` annotation.

For example, `skolemize(X1, sK0(X0))` says that the original existential
variable `X1` is represented by the fresh function `sK0`.  The function's
arguments are recorded independently because `exists_prenex` can move the
existential binders into a different order before Lean chooses their values. -/
structure SkolemBinding where
  /-- Name of the existential variable eliminated by this step. -/
  existentialVariable : String
  /-- Name of the fresh TPTP Skolem constant or function. -/
  symbol : String
  /-- Universally quantified variables supplied to the Skolem function. -/
  arguments : Array String
deriving Repr, BEq

/-- The complete certificate fragment emitted by one Vampire `skolemize`
step.  Vampire can introduce several fresh symbols together, so retaining all
bindings is essential: the prenexed Lean proof is unpacked in the order
computed from the parent formula, rather than in an accidental annotation
order. -/
structure SkolemizationInfo where
  bindings : Array SkolemBinding
deriving Repr, BEq

/-- A parent reference in the proof DAG. -/
structure ParentRef where
  /-- Name used by a child node to look up the previously replayed DAG node. -/
  name : String
deriving Repr, BEq

/-- Parser information attached to an inference node.  `info` is retained for
rules that have not received a dedicated decoder yet. -/
structure Inference where
  /-- Vampire's rule name, for example `resolution` or `cnf_transformation`. -/
  rule : String
  /-- Generic useful-information entries following the rule name. -/
  info : Array MetadataTerm
  /-- The proof-DAG parents in the order reported by Vampire. -/
  parents : Array ParentRef
deriving Repr, BEq

/-- A named outer universal binder of a decoded TFF formula. -/
structure FormulaBinder where
  /-- TPTP spelling used by a substitution, such as `X0`. -/
  name : String
  /-- First-order sort written on the TFF binder.  Retaining it makes fresh
  Skolem function signatures checkable without guessing from Lean terms. -/
  sort : LamSort
deriving Repr, BEq

/-- A propositional node retained as an optional SAT-replay hint. -/
structure SatProofStep where
  name : String
  formula : LamTerm
  parents : Array ParentRef
  rule : String
deriving Repr

structure SatProof where
  root : String
  steps : Array SatProofStep
deriving Repr

/-- A decoded proof-DAG node.  `formula` uses lean-auto's `LamTerm`; inference
metadata remains in the parser-derived form above. -/
structure Step where
  /-- Unique TSTP node name, used as the replay-DAG key. -/
  name : String
  /-- The entire decoded TF0 formula, still in lean-auto's syntax. -/
  formula : LamTerm
  /-- Names and sorts of its leading universal binders. -/
  binders : Array FormulaBinder
  /-- Original existential names in outer-to-inner, left-to-right syntax
  traversal order, retained before `LamTerm` erases binder names. Skolem
  replay uses them to label the original variables and match their occurrences
  to the actual witnesses exposed by `exists_prenex`. -/
  existentialVariables : Array String := #[]
  /-- For an `avatar_definition` node, the named universal prefix of the
  component side of `spl ↔ component`.  It is separate from `binders`: the
  definition itself is closed, while expanding the component later introduces
  these variables.  `avatar_split_clause` certificates name them explicitly. -/
  componentBinders : Array FormulaBinder := #[]
  /-- Names of already reconstructed proof-DAG parents. -/
  parents : Array ParentRef
  /-- Exported `factN` name for an input node. -/
  sourceFact? : Option String
  /-- Rule metadata for a derived node. -/
  inference? : Option Inference
  /-- Flattened TPTP clause literals, assigned by Replay's sequential decoding
  pass from the first `cnf_transformation` onwards. -/
  clauseLiterals? : Option (Array LamTerm)
  /-- The original SAT sub-DAG, checked independently if small enough. -/
  satProof? : Option SatProof := none
deriving Repr

/-- A previously reconstructed parent, available to an inference handler. -/
structure ParentProof where
  /-- The child node's reference to this parent. -/
  parent : ParentRef
  /-- Parent leading binders, needed to apply its unifier. -/
  binders : Array FormulaBinder
  /-- Original existential names in syntax traversal order. A following
  `skolemize` step matches them to its actual prenex witnesses; this list does
  not predict the transformed binder order. -/
  existentialVariables : Array String
  /-- Named universal prefix on the component side of an AVATAR definition.
  This preserves the `arg(definition, variable)` namespace used by Vampire's
  AVATAR-split certificate after ordinary formula decoding has erased names. -/
  componentBinders : Array FormulaBinder
  /-- The parent's original parser formula. This is retained so the `grind`
  fallback can temporarily recover ordinary `Or` syntax from its stored clause
  proof. -/
  target : Expr
  /-- Whether `proof` is stored in `Clause.Holds` form. Clause form begins at
  a `cnf_transformation` result and is retained by later descendants. -/
  clauseForm : Bool
  /-- The parent's decoded clause literals, already translated from `LamTerm`
  to Lean expressions. They still have de Bruijn variables for the parent's
  leading universals; clause conversion opens those binders before using them. -/
  clauseLiterals? : Option (Array Expr)
  /-- Proofs of the conjuncts in the parent's VampLean CNF result, computed on
  demand: only a `cnf_transformation` that cannot be proved directly needs
  them. `cnfify` and conjunction splitting run once per proof-DAG parent;
  sibling `cnf_transformation` nodes share the cached array. -/
  cnfCandidates : MetaM (Option (Array (Expr × Expr)))
  /-- Kernel-checked Lean proof assembled for the parent node. -/
  proof : Expr

/-- A SAT-trail node translated to local propositions. -/
structure SatClause where
  name : String
  literals : Array Expr
  parents : Array ParentRef
  rule : String

/-- Everything a reconstruction rule needs for one Vampire proof-DAG node.

`target`, `parents`, and `symbols` all belong to the same local first-order
signature. They contain readable TPTP names and are independent of lean-auto's
temporary `Lam2DAAF` context. `step` retains the parser metadata needed to
check the rule certificate. -/
structure RuleInput where
  /-- Parser-level information for the node being reconstructed. -/
  step : Step
  /-- The conclusion as a Lean proposition in the local TPTP signature. -/
  target : Expr
  /-- For a sequential post-CNF step, the conclusion literals decoded directly
  from TPTP. The expressions use the same outer de Bruijn variables as
  `target`; handlers instantiate them after opening those binders. -/
  clauseLiterals? : Option (Array Expr)
  /-- Reconstructed parent proofs in the exact DAG parent order. -/
  parents : Array ParentProof
  /-- Local `factN` hypothesis for a TPTP input node, if this is one. -/
  sourceProof? : Option Expr
  /-- All source proof fvars, removed before a fallback `grind` invocation. -/
  sourceFVars : Array FVarId
  /-- TPTP function and predicate names interpreted as local Lean variables.
  Resolution terms are decoded against this table only when their rule runs. -/
  symbols : Std.HashMap String Expr
  /-- Optional original SAT trail and root, used only as checked replay hints. -/
  satProof? : Option (String × Array SatClause) := none
  /-- Replay's `vampireInhabitantᵢ` witnesses, one per local sort. Calculus
  rules instantiate variables erased by an inference with them. Empty outside
  Replay, where handlers fall back to scanning the local context. -/
  inhabitants : Array Expr := #[]
  /-- Replay's AVATAR split atoms, taken from the decoded symbol kinds. `none`
  outside Replay, where `avatarAtoms` falls back to Vampire's `spl` spelling. -/
  avatarAtoms? : Option (Array Expr) := none

/-- Decide where the replay enters clause form. `Replay.decodeSteps` marks the
sequential suffix beginning with the first `cnf_transformation`; this decoder
mark is authoritative, rather than inferring the phase again from DAG parents. -/
def storesClauseForm (input : RuleInput) : Bool :=
  input.step.clauseLiterals?.isSome

end VampireHammer.Backend
