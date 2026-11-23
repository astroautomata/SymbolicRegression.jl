import SymReg.HofMig.Core
import DynExpr.Registry.Types

namespace SymReg.PopMember
open DynExpr
open SymReg.HofMig (Member)

-- Source: src/PopMember.jl:82
-- generate_reference() = abs(rand(Int))
-- The draw is from Julia's task-local default RNG. Signed minimum wraps on abs.
def generateReference (draw : Int64) : Int :=
  (if draw < 0 then -draw else draw).toInt

-- Source: src/PopMember.jl:97-130
/-
function PopMember(
    t::AbstractExpression{T},
    cost::L,
    loss::L,
    options::Union{AbstractOptions,Nothing}=nothing,
    complexity::Union{Int,Nothing}=nothing;
    ref::Int=-1,
    parent::Int=-1,
    deterministic=nothing,
) where {T<:DATA_TYPE,L<:LOSS_TYPE}
    if ref == -1
        ref = generate_reference()
    end
    if !(deterministic isa Bool)
        throw(
            ArgumentError(
                "You must declare `deterministic` as `true` or `false`, it cannot be left undefined.",
            ),
        )
    end
    complexity = complexity === nothing ? -1 : complexity
    return PopMember{T,L,typeof(t)}(
        t,
        cost,
        loss,
        get_birth_order(; deterministic=deterministic),
        complexity,
        ref,
        parent,
    )
end
-/
def construct (tree treeId objectId : Nat) (cost loss : JF) (complexity : Option Int)
    (ref parent : Int) (deterministic : Option Bool) (birth : Bool → Jl Int)
    (stream : Nat → Int64) (cursor : Nat) : Jl Member × Nat :=
  let (ref, cursor) := if ref = -1 then (generateReference (stream cursor), cursor + 1)
    else (ref, cursor)
  let result : Jl Member := match deterministic with
    | none => .error (.argumentError
        "You must declare `deterministic` as `true` or `false`, it cannot be left undefined.")
    | some flag => (birth flag).map fun n =>
        { tree, treeId, objectId, cost, loss, complexity := complexity.getD (-1),
          birth := n, reference := ref, parent }
  (result, cursor)

-- Source: src/PopMember.jl:145-168
/-
function PopMember(
    dataset::Dataset{T,L},
    tree::Union{AbstractExpressionNode{T},AbstractExpression{T}},
    options::AbstractOptions,
    complexity::Union{Int,Nothing}=nothing;
    ref::Int=-1,
    parent::Int=-1,
    deterministic=nothing,
) where {T<:DATA_TYPE,L<:LOSS_TYPE}
    ex = create_expression(tree, options, dataset)
    set_complexity = complexity === nothing ? compute_complexity(ex, options) : complexity
    @assert set_complexity != -1
    cost, loss = eval_cost(dataset, ex, options; complexity=set_complexity)
    return PopMember(
        ex,
        cost,
        loss,
        options,
        set_complexity;
        ref=ref,
        parent=parent,
        deterministic=deterministic,
    )
end
-/
inductive ConstructorCall where
  | create | complexity | evaluate
  deriving DecidableEq

def constructEvaluated {E : Type} (create : E → Jl (Nat × Nat))
    (compute : Nat → Jl Int) (evaluate : Nat → Int → Jl (JF × JF))
    (tree : E) (objectId : Nat) (complexity : Option Int) (ref parent : Int)
    (deterministic : Option Bool) (birth : Bool → Jl Int)
    (stream : Nat → Int64) (cursor : Nat) : (Jl Member × Nat) × List ConstructorCall :=
  match create tree with
  | .error e => ((.error e, cursor), [.create])
  | .ok (ex, exId) =>
    let (resolved, calls) := match complexity with
      | none => (compute ex, [ConstructorCall.create, .complexity])
      | some n => (.ok n, [ConstructorCall.create])
    match resolved with
    | .error e => ((.error e, cursor), calls)
    | .ok n =>
      if n = -1 then ((.error (.assertionError "set_complexity != -1"), cursor), calls)
      else
        let result := match evaluate ex n with
          | .error e => (.error e, cursor)
          | .ok (cost, loss) => construct ex exId objectId cost loss (some n) ref parent deterministic birth stream cursor
        (result, calls ++ [.evaluate])

-- Source: src/PopMember.jl:58-70
/-
@unstable @inline function Base.getproperty(member::AbstractPopMember, field::Symbol)
    if field == :complexity
        throw(
            error("Don't access `.complexity` directly. Use `compute_complexity` instead.")
        )
    elseif field == :score
        Base.depwarn(
            "deprecated: use `cost` instead of `score`.", Symbol(:getproperty, :PopMember)
        )
        return getfield(member, :cost)
    end
    return getfield(member, field)
end
-/
def getProperty {A : Type} (getField : String → Jl A) (warn : Jl Unit) (field : String) : Jl A := do
  if field = "complexity" then
    throw (.errorException "Don't access `.complexity` directly. Use `compute_complexity` instead.")
  else if field = "score" then
    warn
    getField "cost"
  else getField field

-- Source: src/PopMember.jl:44-57
/-
@inline function Base.setproperty!(member::AbstractPopMember, field::Symbol, value)
    if field == :complexity
        throw(
            error("Don't set `.complexity` directly. Use `recompute_complexity!` instead.")
        )
    elseif field == :tree
        setfield!(member, :complexity, -1)
    elseif field == :score
        Base.depwarn(
            "deprecated: use `cost` instead of `score`.", Symbol(:setproperty!, :PopMember)
        )
        return setfield!(member, :cost, value)
    end
    return setfield!(member, field, value)
end
-/
-- setField represents the Julia primitive's type/field checks. The pair keeps
-- the cache mutation when assigning the new tree subsequently fails.
def setProperty {M A : Type} (setField : M → String → A → Jl M)
    (invalidate : M → Jl M) (warn : Jl Unit) (m : M) (field : String) (a : A) : Jl A × M :=
  let write (m : M) (field : String) : Jl A × M := match setField m field a with
    | .error e => (.error e, m)
    | .ok m' => (.ok a, m')
  if field = "complexity" then
    (.error (.errorException "Don't set `.complexity` directly. Use `recompute_complexity!` instead."), m)
  else if field = "tree" then
    match invalidate m with
    | .error e => (.error e, m)
    | .ok m' => write m' field
  else if field = "score" then
    match warn with
    | .error e => (.error e, m)
    | .ok () => write m "cost"
  else write m field

-- Source: src/PopMember.jl:73
-- shower(x) = sprint(show, x)
def shower (sprintShow : JF → Jl String) (x : JF) : Jl String := sprintShow x

-- Source: src/PopMember.jl:72-80
/-
function Base.show(io::IO, p::PopMember{T,L,N}) where {T,L,N}
    shower(x) = sprint(show, x)
    print(io, "PopMember(")
    print(io, "tree = (", string_tree(p.tree), "), ")
    print(io, "loss = ", shower(p.loss), ", ")
    print(io, "cost = ", shower(p.cost))
    print(io, ")")
    return nothing
end
-/
-- One output action per Julia print argument; rendering failures retain the
-- already printed prefix. A call's string arguments render before it prints.
def showMember {S : Type} (emit : S → String → Jl Unit × S)
    (treeString : Nat → Jl String) (sprintShow : JF → Jl String) (m : Member) :
    S → Jl Unit × S :=
  let rec output (chunks : List (Jl (List String))) (s : S) : Jl Unit × S :=
    match chunks with
    | [] => (.ok (), s)
    | .error e :: _ => (.error e, s)
    | .ok ss :: rest =>
      let run : Jl Unit × S := ss.foldl (fun ((r, s) : Jl Unit × S) text => match r with
        | .ok () => emit s text
        | .error e => (.error e, s)) (.ok (), s)
      match run with
      | (.ok (), s) => output rest s
      | (.error e, s) => (.error e, s)
  output [.ok ["PopMember("], (treeString m.tree).map (fun t => ["tree = (", t, "), "]),
    (shower sprintShow m.loss).map (fun l => ["loss = ", l, ", "]),
    (shower sprintShow m.cost).map (fun c => ["cost = ", c]), .ok [")"]]

/-- Type-object tags. Concrete tags carry the parameters independently of the instance. -/
structure Parameters where
  data : Nat
  loss : Nat
  expression : Nat
  deriving DecidableEq

inductive MemberType where
  | family
  | concrete (parameters : Parameters)
  deriving DecidableEq

-- Source: src/PopMember.jl:264
-- @unstable default_popmember_type() = PopMember
def defaultPopmemberType : MemberType := .family

-- Source: src/PopMember.jl:265
-- @unstable constructorof(::Type{<:PopMember}) = PopMember
def constructorOf (_ : MemberType) : MemberType := .family

-- Source: src/PopMember.jl:267-271
/-
@inline function with_expression_type(
    ::Type{<:PopMember{T,L}}, ::Type{N}
) where {T,L,N<:AbstractExpression{T}}
    return PopMember{T,L,N}
end
-/
def withExpressionType (old : Parameters) (expression : Nat) : MemberType :=
  .concrete ⟨old.data, old.loss, expression⟩

-- Source: src/PopMember.jl:273-277
/-
@inline function with_type_parameters(
    ::Type{<:PopMember}, ::Type{T}, ::Type{L}, ::Type{N}
) where {T,L,N}
    return PopMember{T,L,N}
end
-/
structure TypeBounds where
  dataOK : Nat → Bool
  lossOK : Nat → Bool
  expressionData : Nat → Option Nat

def withTypeParameters (_ : MemberType) (p : Parameters) (bounds : TypeBounds) : Jl MemberType :=
  if bounds.dataOK p.data && bounds.lossOK p.loss && bounds.expressionData p.expression == some p.data
  then .ok (.concrete p) else .error (.errorException "TypeError")

def replaceExpression (p : Parameters) (n : Nat) (bounds : TypeBounds) : Jl MemberType :=
  if bounds.expressionData n == some p.data then .ok (withExpressionType p n)
  else .error (.methodError "with_expression_type")

-- Source: src/PopMember.jl:279-281
/-
@inline function expression_type(::Type{<:AbstractPopMember{<:Any,<:Any,N}}) where {N}
    return N
end
-/
def expressionType (p : Parameters) : Nat := p.expression

end SymReg.PopMember
