import DynExpr.Expressions.Wrapper

namespace SymReg.Ext
open DynExpr DynExpr.Expressions

structure SymbolicOptions (O : Type) where
  identity : Nat
  operators : O

inductive SymbolicCall (E O S N K : Type) where
  | options (model : Nat)
  | tree (original : E)
  | operators (original : E) (options : Option (SymbolicOptions O))
  | forward (baseConvert : Bool) (tree : Addr) (operators : Option O) (keywords : K)
  | backward (term : S) (operators : O) (keywords : K)
  | convert (target : Nat) (term : Sum N S) (operators : O) (keywords : K)

abbrev SymbolicRun (E O S N K A : Type) := Jl A × List (SymbolicCall E O S N K)

-- Source: ext/SymbolicRegressionSymbolicUtilsExt.jl:16-20,41-48
/-
function node_to_symbolic(
    tree::Union{AbstractExpressionNode,AbstractExpression}, options::Options; kws...
)
    return node_to_symbolic(get_tree(tree), get_operators(tree, options); kws...)
end
function Base.convert(
    ::Type{SymbolicType},
    tree::Union{AbstractExpressionNode,AbstractExpression},
    options::Union{Options,Nothing}=nothing;
    kws...,
)
    return convert(SymbolicType, get_tree(tree), get_operators(tree, options); kws...)
end
-/
def forwardSymbolic {E O S N K : Type} (baseConvert : Bool)
    (getTree : E → Jl Addr) (lookup : E → Option (SymbolicOptions O) → Jl (Option O))
    (convert : Addr → Option O → K → Jl S) (original : E)
    (options : Option (SymbolicOptions O)) (kws : K) : SymbolicRun E O S N K S :=
  match getTree original with
  | .error e => (.error e, [.tree original])
  | .ok tree =>
    match lookup original options with
    | .error e => (.error e, [.tree original, .operators original options])
    | .ok ops => (convert tree ops kws,
      [.tree original, .operators original options, .forward baseConvert tree ops kws])

-- Source: ext/SymbolicRegressionSymbolicUtilsExt.jl:34-39
/-
function symbolic_to_node(eqn::SymbolicType, options::Options; kws...)
    return symbolic_to_node(eqn, options.operators; kws...)
end
-/
def symbolicToNode {E O S N K : Type} (convert : S → O → K → Jl Addr)
    (term : S) (options : SymbolicOptions O) (kws : K) : SymbolicRun E O S N K Addr :=
  (convert term options.operators kws, [.backward term options.operators kws])

-- Source: ext/SymbolicRegressionSymbolicUtilsExt.jl:58-62
/-
function Base.convert(
    ::Type{N}, x::Union{Number,SymbolicType}, options::Options; kws...
) where {N<:Union{AbstractExpressionNode,AbstractExpression}}
    return convert(N, x, options.operators; kws...)
end
-/
def convertNode {E O S N K A : Type} (convert : Nat → Sum N S → O → K → Jl A)
    (target : Nat) (term : Sum N S) (options : SymbolicOptions O) (kws : K) :
    SymbolicRun E O S N K A :=
  (convert target term options.operators kws, [.convert target term options.operators kws])

-- Source: ext/SymbolicRegressionSymbolicUtilsExt.jl:21-27,37-39,49-56,63-67
def regressorOptions {E O S N K A : Type} (getOptions : Nat → Jl (SymbolicOptions O))
    (model : Nat) (delegate : SymbolicOptions O → SymbolicRun E O S N K A) :
    SymbolicRun E O S N K A :=
  match getOptions model with
  | .error err => (.error err, [.options model])
  | .ok options =>
    let (result, events) := delegate options
    (result, .options model :: events)

-- return node_to_symbolic(tree, get_options(m); kws...)
-- return convert(SymbolicType, tree, get_options(m); kws...)
def regressorForward {E O S N K : Type} (base : Bool)
    (getOptions : Nat → Jl (SymbolicOptions O)) (getTree : E → Jl Addr)
    (lookup : E → Option (SymbolicOptions O) → Jl (Option O))
    (toSymbolic convert : Addr → Option O → K → Jl S) (original : E) (model : Nat) (kws : K) :
    SymbolicRun E O S N K S :=
  regressorOptions getOptions model (fun options =>
    forwardSymbolic base getTree lookup (if base then convert else toSymbolic) original (some options) kws)

-- return symbolic_to_node(eqn, get_options(m); kws...)
def regressorToNode {E O S N K : Type} (getOptions : Nat → Jl (SymbolicOptions O))
    (convert : S → O → K → Jl Addr) (term : S) (model : Nat) (kws : K) :
    SymbolicRun E O S N K Addr :=
  regressorOptions getOptions model (fun options => symbolicToNode convert term options kws)

-- return convert(N, x, get_options(m); kws...)
def regressorConvertNode {E O S N K A : Type} (getOptions : Nat → Jl (SymbolicOptions O))
    (convert : Nat → Sum N S → O → K → Jl A) (target : Nat) (term : Sum N S)
    (model : Nat) (kws : K) : SymbolicRun E O S N K A :=
  regressorOptions getOptions model (fun options => convertNode convert target term options kws)

def symbolicForwarding : Prop :=
  ∀ (E O S K : Type) base getTree lookup convert (original : E)
    (options : SymbolicOptions O) (kws : K) tree ops,
    getTree original = .ok tree → lookup original (some options) = .ok ops →
    forwardSymbolic (N := Unit) (S := S) base getTree lookup convert original (some options) kws =
      (convert tree ops kws, [.tree original, .operators original (some options),
        .forward base tree ops kws])

theorem symbolicForwarding_holds : symbolicForwarding := by
  intro E O S K base getTree lookup convert original options kws tree ops ht ho
  simp [forwardSymbolic, ht, ho]

def symbolicReverseForwarding : Prop :=
  ∀ (O S N K A : Type) toNode (toExpr : Nat → Sum N S → O → K → Jl A)
    (term : S) numberOrTerm target (options : SymbolicOptions O) (kws : K),
    symbolicToNode (E := Unit) (N := N) toNode term options kws =
      (toNode term options.operators kws, [.backward term options.operators kws]) ∧
    convertNode (E := Unit) toExpr target numberOrTerm options kws =
      (toExpr target numberOrTerm options.operators kws,
        [.convert target numberOrTerm options.operators kws])

theorem symbolicReverseForwarding_holds : symbolicReverseForwarding := by
  intro O S N K A toNode toExpr term numberOrTerm target options kws
  exact ⟨rfl, rfl⟩

def symbolicModelRouting : Prop :=
  ∀ (E O S N K A : Type) getOptions (model : Nat) getTree lookup
    (forward convertForward : Addr → Option O → K → Jl S) backward toExpr
    (original : E) (term : S) (input : Sum N S) (target : Nat) (kws : K),
  let node := regressorToNode (E := E) (N := N) getOptions backward term model kws
  let convert := regressorConvertNode (E := E) (A := A) getOptions toExpr target input model kws
  let fromTree := fun base => regressorForward (N := N) base getOptions getTree lookup
    forward convertForward original model kws
  (∀ e, getOptions model = .error e →
    node = (.error e, [.options model]) ∧ convert = (.error e, [.options model]) ∧
    ∀ base, fromTree base = (.error e, [.options model])) ∧
  (∀ options, getOptions model = .ok options →
    node = (backward term options.operators kws, [.options model, .backward term options.operators kws]) ∧
    convert = (toExpr target input options.operators kws,
      [.options model, .convert target input options.operators kws]) ∧
    (∀ e, getTree original = .error e → ∀ base,
      fromTree base = (.error e, [.options model, .tree original])) ∧
    (∀ tree, getTree original = .ok tree →
      (∀ e, lookup original (some options) = .error e → ∀ base,
        fromTree base = (.error e, [.options model, .tree original, .operators original (some options)])) ∧
      (∀ ops, lookup original (some options) = .ok ops →
        fromTree false = (forward tree ops kws, [.options model, .tree original,
          .operators original (some options), .forward false tree ops kws]) ∧
        fromTree true = (convertForward tree ops kws, [.options model, .tree original,
          .operators original (some options), .forward true tree ops kws]))))

theorem symbolicModelRouting_holds : symbolicModelRouting := by
  intro E O S N K A getOptions model getTree lookup forward convertForward backward toExpr
    original term input target kws
  refine ⟨?_, ?_⟩
  · intro e h
    simp [regressorToNode, regressorConvertNode, regressorForward, regressorOptions, h]
  · intro options h
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [regressorToNode, regressorOptions, symbolicToNode, h]
    · simp [regressorConvertNode, regressorOptions, convertNode, h]
    · intro e ht base
      simp [regressorForward, regressorOptions, forwardSymbolic, h, ht]
    · intro tree ht
      refine ⟨?_, ?_⟩
      · intro e ho base
        simp [regressorForward, regressorOptions, forwardSymbolic, h, ht, ho]
      · intro ops ho
        simp [regressorForward, regressorOptions, forwardSymbolic, h, ht, ho]

def runSymbolicRoundtrip {E O S K : Type}
    (getTree : E → Jl Addr) (lookup : E → Option (SymbolicOptions O) → Jl (Option O))
    (forward : Addr → Option O → K → Jl S) (backward : S → O → K → Jl Addr) (original : E)
    (options : SymbolicOptions O) (kws : K) : SymbolicRun E O S Unit K Addr :=
  match forwardSymbolic false getTree lookup forward original (some options) kws with
  | (.error e, events) => (.error e, events)
  | (.ok term, events) =>
    let (result, next) := symbolicToNode backward term options kws
    (result, events ++ next)

def symbolicRoundtripReduction : Prop :=
  ∀ (E O S K : Type) getTree lookup (forward : Addr → Option O → K → Jl S) backward (original : E)
    (options : SymbolicOptions O) (kws : K) tree,
    getTree original = .ok tree →
    lookup original (some options) = .ok (some options.operators) →
    (runSymbolicRoundtrip getTree lookup forward backward original options kws).1 =
      (do let term ← forward tree (some options.operators) kws
          backward term options.operators kws)

def symbolicRoundtrip : Prop :=
  ∀ (E O S K : Type) getTree lookup forward backward (original : E)
    (options : SymbolicOptions O) (kws : K) tree (term : S),
    getTree original = .ok tree → lookup original (some options) = .ok (some options.operators) →
    forward tree (some options.operators) kws = .ok term →
    backward term options.operators kws = .ok tree →
    runSymbolicRoundtrip getTree lookup forward backward original options kws =
      (.ok tree, [.tree original, .operators original (some options),
        .forward false tree (some options.operators) kws, .backward term options.operators kws])

theorem symbolicRoundtrip_holds : symbolicRoundtrip := by
  intro E O S K getTree lookup forward backward original options kws tree term ht ho hf hb
  simp [runSymbolicRoundtrip, forwardSymbolic, symbolicToNode, ht, ho, hf, hb]

def symbolicMetadataRouting : Prop :=
  ∀ (E O S K : Type) getTree lookup convert (original : E) (kws : K) tree,
    getTree original = .ok tree →
    (∀ err, lookup original none = .error err →
      forwardSymbolic (N := Unit) (O := O) (S := S) true getTree lookup convert original none kws =
        (.error err, [.tree original, .operators original none])) ∧
    ∀ ops, lookup original none = .ok ops →
      forwardSymbolic (N := Unit) true getTree lookup convert original none kws =
        (convert tree ops kws, [.tree original, .operators original none, .forward true tree ops kws])

theorem symbolicMetadataRouting_holds : symbolicMetadataRouting := by
  intro E O S K getTree lookup convert original kws tree ht
  exact ⟨fun err he => by simp [forwardSymbolic, ht, he],
    fun ops ho => by simp [forwardSymbolic, ht, ho]⟩

end SymReg.Ext
