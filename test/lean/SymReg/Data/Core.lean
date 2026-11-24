import SymReg.Loss.Witnesses
import DynExpr.Registry.Types

namespace SymReg.Data
open DynExpr

/-- The constructor returns DimensionMismatch for target size, and ErrorException for unit size. -/
inductive ConstructionError where
  | dimensionMismatch (message : String)
  | julia (error : JlError)
  deriving DecidableEq

-- Source: src/Dataset.jl:263-265
/-
function error_on_mismatched_size(_, ::Nothing)
    return nothing
end
-/
def checkAbsentUnits (_ : Nat) : Jl Unit := pure ()

-- Source: src/Dataset.jl:266-273
/-
function error_on_mismatched_size(nfeatures, X_units::AbstractVector)
    if nfeatures != length(X_units)
        error(
            "Number of features ($(nfeatures)) does not match number of units ($(length(X_units)))",
        )
    end
    return nothing
end
-/
def checkPresentUnits {U : Type} (nfeatures : Nat) (units : List U) : Jl Unit :=
  if nfeatures ≠ units.length then
    .error (.errorException s!"Number of features ({nfeatures}) does not match number of units ({units.length})")
  else pure ()

def checkUnits {U : Type} (nfeatures : Nat) : Option (List U) → Jl Unit
  | none => checkAbsentUnits nfeatures
  | some units => checkPresentUnits nfeatures units

-- Source: src/Dataset.jl:275-277
/-
function has_units(dataset::Dataset)
    return dataset.X_units !== nothing || dataset.y_units !== nothing
end
-/
def hasUnits (d : SymReg.Loss.Dataset) : Bool := d.full.xUnits || d.full.yUnits

/-- A named tuple descends into values only. Arrays are references; ordinary tuples and
other objects are opaque and remain untouched. -/
inductive FillValue (R : Type) where
  | array (reference : R)
  | namedTuple (values : List (FillValue R))
  | nothing
  | other (identity : Nat)

/-- Effects of reading a property or filling an array, including state before an error. -/
abbrev Effect (S A : Type) := S → Jl A × S

-- Source: src/Dataset.jl:287-290
/-
_fill!(x::AbstractArray, val) = fill!(x, val)
_fill!(x::NamedTuple, val) = foreach(v -> _fill!(v, val), values(x))
_fill!(::Nothing, val) = nothing
_fill!(x, val) = x
-/
mutual
  def fillValue {R V S : Type} (fillArray : R → V → Effect S R) (v : V) :
      FillValue R → Effect S (FillValue R)
    | .array r, s =>
      let (out, s') := fillArray r v s
      (out.map FillValue.array, s')
    | .namedTuple xs, s =>
      let (out, s') := fillValues fillArray v xs s
      (out.map (fun _ => .nothing), s')
    | .nothing, s => (.ok .nothing, s)
    | .other x, s => (.ok (.other x), s)
  def fillValues {R V S : Type} (fillArray : R → V → Effect S R) (v : V) :
      List (FillValue R) → Effect S Unit
    | [], s => (.ok (), s)
    | x :: xs, s =>
      match fillValue fillArray v x s with
      | (.error e, s') => (.error e, s')
      | (.ok _, s') => fillValues fillArray v xs s'
end

-- Source: src/Dataset.jl:280-286
/-
function Base.fill!(d::Dataset, val)
    _fill!(d.X, val)
    _fill!(d.y, val)
    _fill!(d.weights, val)
    _fill!(d.extra, val)
    return d
end
-/
def fillDataset {D R V S : Type} (readProperty : D → String → Effect S (FillValue R))
    (fillArray : R → V → Effect S R) (d : D) (v : V) : Effect S D :=
  let rec go (fields : List String) (s : S) : Jl D × S :=
    match fields with
    | [] => (.ok d, s)
    | f :: fs =>
      match readProperty d f s with
      | (.error e, s') => (.error e, s')
      | (.ok x, s') =>
        match fillValue fillArray v x s' with
        | (.error e, s'') => (.error e, s'')
        | (.ok _, s'') => go fs s''
  go ["X", "y", "weights", "extra"]

/-- A dimension-preserving matrix retains row count even with zero sample columns.
Unit tokens stand for results of the SI and symbolic conversion services. -/
structure In where
  matrix : JMat JF
  y : Option (List JF)
  weights : Option (List JF) := none
  index : Int := 1
  names : Option (List String) := none
  displayNames : Option (List String) := none
  yName : Option String := none
  extra : FillValue Nat := .namedTuple []
  xUnits : Option (List Nat) := none
  yUnits : Option Nat := none

def In.withDefaultDisplay (a : In) : In := { a with displayNames := a.names }

structure Built where
  fields : SymReg.Loss.Basic
  matrix : JMat JF
  index : Int
  names : List String
  displayNames : List String
  yName : String
  extra : FillValue Nat
  xSiUnits : Option (List Nat)
  ySiUnits : Option Nat
  xSymUnits : Option (List Nat)
  ySymUnits : Option Nat

def subscript (n : Nat) : String :=
  String.ofList (n.repr.toList.map fun c => match c with
    | '0' => '₀' | '1' => '₁' | '2' => '₂' | '3' => '₃' | '4' => '₄'
    | '5' => '₅' | '6' => '₆' | '7' => '₇' | '8' => '₈' | '9' => '₉' | c => c)

structure UnitServices where
  ySi : Option Nat → Jl (Option Nat)
  ySym : Option Nat → Jl (Option Nat)
  xSi : Option (List Nat) → Jl (Option (List Nat))
  xSym : Option (List Nat) → Jl (Option (List Nat))
  siDimensionless : Nat → Jl (Option (List Nat))
  symDimensionless : Nat → Jl (Option (List Nat))

def jl {A : Type} (r : Jl A) : Except ConstructionError A :=
  r.mapError ConstructionError.julia

-- Source: src/Dataset.jl:131-253
/-
function Dataset(
    X::AbstractMatrix{T},
    y::Union{AbstractVector,Nothing}=nothing,
    loss_type::Type{L}=Nothing;
    index::Int=1,
    weights::Union{AbstractVector,Nothing}=nothing,
    variable_names::Union{Array{String,1},Nothing}=nothing,
    display_variable_names=variable_names,
    y_variable_name::Union{String,Nothing}=nothing,
    extra::NamedTuple=NamedTuple(),
    X_units::Union{AbstractVector,Nothing}=nothing,
    y_units=nothing,
    # Deprecated:
    kws...,
) where {T<:DATA_TYPE,L}
    Base.require_one_based_indexing(X)
    y !== nothing && Base.require_one_based_indexing(y)
    # Deprecation warning:
    if haskey(kws, :loss_type)
        Base.depwarn(
            "The `loss_type` keyword argument is deprecated. Pass as an argument instead.",
            :Dataset,
        )
        return Dataset(
            X,
            y,
            kws[:loss_type];
            index,
            weights,
            variable_names,
            display_variable_names,
            y_variable_name,
            extra,
            X_units,
            y_units,
        )
    end

    n = size(X, 2)
    nfeatures = size(X, 1)
    if y !== nothing && length(y) != n
        throw(
            DimensionMismatch(
                "Number of samples in `X` (size(X, 2) = $n) does not match the length of `y` ($(length(y))). `X` should have shape (nfeatures, nsamples).",
            ),
        )
    end
    variable_names = @something(variable_names, ["x$(i)" for i in 1:nfeatures])
    display_variable_names = @something(
        display_variable_names, ["x$(subscriptify(i))" for i in 1:nfeatures]
    )
    y_variable_name = @something(y_variable_name, ("y" ∉ variable_names) ? "y" : "target")
    avg_y = if y === nothing || !(eltype(y) isa Number)
        nothing
    else
        if weights !== nothing
            sum(y .* weights) / sum(weights)
        else
            sum(y) / n
        end
    end
    out_loss_type = if L === Nothing
        T <: Complex ? get_base_type(T) : T
    else
        L
    end

    use_baseline = true
    baseline = one(out_loss_type)
    y_si_units = get_si_units(T, y_units)
    y_sym_units = get_sym_units(T, y_units)

    # TODO: Refactor
    # This basically just ensures that if the `y` units are set,
    # then the `X` units are set as well.
    X_si_units = let (_X = get_si_units(T, X_units))
        if _X === nothing && y_si_units !== nothing
            get_si_units(T, [one(T) for _ in 1:nfeatures])
        else
            _X
        end
    end
    X_sym_units = let _X = get_sym_units(T, X_units)
        if _X === nothing && y_sym_units !== nothing
            get_sym_units(T, [one(T) for _ in 1:nfeatures])
        else
            _X
        end
    end

    error_on_mismatched_size(nfeatures, X_si_units)

    return BasicDataset{
        T,
        out_loss_type,
        typeof(X),
        typeof(y),
        typeof(weights),
        typeof(extra),
        typeof(X_si_units),
        typeof(y_si_units),
        typeof(X_sym_units),
        typeof(y_sym_units),
    }(
        X,
        y,
        index,
        n,
        nfeatures,
        weights,
        extra,
        avg_y,
        use_baseline,
        baseline,
        variable_names,
        display_variable_names,
        y_variable_name,
        X_si_units,
        y_si_units,
        X_sym_units,
        y_sym_units,
    )
end
-/
-- requireX/requireY perform Julia's one-based-indexing checks; baseline performs one(out_loss_type).
-- A deprecated keyword repeats the same checks after emitting its warning, selecting its own type.
-- eltype(y) is a type object, so the arithmetic branch for avg_y is unreachable.
def construct (a : In) (units : UnitServices) (requireX requireY : Jl Unit)
    (lossType : Option Nat) (deprecatedLossType : Option (Jl Unit × Option Nat))
    (baseline : Option Nat → Jl JF) : Except ConstructionError Built := do
  jl requireX
  if a.y.isSome then jl requireY
  let lossType ← match deprecatedLossType with
    | none => pure lossType
    | some (warn, ty) => do
      jl warn
      jl requireX
      if a.y.isSome then jl requireY
      pure ty
  let n := a.matrix.ncols
  let nfeatures := a.matrix.nrows
  if let some y := a.y then
    if y.length ≠ n then
      throw (.dimensionMismatch s!"Number of samples in `X` (size(X, 2) = {n}) does not match the length of `y` ({y.length}). `X` should have shape (nfeatures, nsamples).")
  let names := a.names.getD ((List.range nfeatures).map fun i => s!"x{i+1}")
  let display := a.displayNames.getD ((List.range nfeatures).map fun i => "x" ++ subscript (i+1))
  let yName := a.yName.getD (if names.contains "y" then "target" else "y")
  let b ← jl (baseline lossType)
  let ySi ← jl (units.ySi a.yUnits)
  let ySym ← jl (units.ySym a.yUnits)
  let xSi ← jl (units.xSi a.xUnits)
  let xSi ← if xSi.isNone && ySi.isSome then jl (units.siDimensionless nfeatures) else pure xSi
  let xSym ← jl (units.xSym a.xUnits)
  let xSym ← if xSym.isNone && ySym.isSome then jl (units.symDimensionless nfeatures) else pure xSym
  jl (checkUnits nfeatures xSi)
  let columns := (List.range n).map fun j => (List.range nfeatures).map fun i =>
    a.matrix.data[j*nfeatures+i]?.getD (.fin 0)
  let fields := (SymReg.Loss.numericDataset columns a.y a.weights).full
  pure ⟨{ fields with baselineLoss := b, xUnits := xSi.isSome, yUnits := ySi.isSome },
    a.matrix, a.index, names, display, yName, a.extra, xSi, ySi, xSym, ySym⟩

-- Source: src/Dataset.jl:292-294
/-
function max_features(dataset::Dataset, _)
    return dataset.nfeatures
end
-/
def maxFeatures (d : Built) (_ : Nat) : Nat := d.matrix.nrows

-- Source: src/Dataset.jl:106-110
-- elseif prop == :n
--     return length(get_indices(d))
-- else
--     # Forward all other properties
--     return getproperty(get_full_dataset(d), prop)
structure BatchView where
  full : SymReg.Loss.Basic
  indices : Option (List Int)

def sampleCount (d : BatchView) : Nat :=
  d.indices.elim d.full.columns.length List.length

def otherProperty {A : Type} (get : SymReg.Loss.Basic → String → Jl A)
    (d : SymReg.Loss.Dataset) (prop : String) : Jl A := get d.full prop

-- Source: src/Dataset.jl:95-96
/-
@inline get_full_dataset(d::SubDataset) = getfield(d, :_dataset)
@inline get_indices(d::SubDataset) = getfield(d, :_indices)
-/
def getFullDataset (d : BatchView) : SymReg.Loss.Basic := d.full

def getIndices (d : BatchView) : Option (List Int) := d.indices

-- Source: src/Dataset.jl:113-113
/-
@inline Base.propertynames(d::SubDataset) = propertynames(get_full_dataset(d))
-/
def propertyNames (fullNames : SymReg.Loss.Basic → List String)
    (d : BatchView) : List String := fullNames (getFullDataset d)

-- Source: src/Dataset.jl:307-309
/-
function batch(dataset::BasicDataset{T,L}, indices::AbstractVector{Int}) where {T,L}
    return SubDataset{T,L,typeof(dataset),typeof(indices)}(dataset, indices)
end
-/
def batch (d : SymReg.Loss.Basic) (indices : List Int) : BatchView := ⟨d, some indices⟩

-- Source: src/Dataset.jl:310-312
/-
function batch(rng::AbstractRNG, dataset::BasicDataset{T,L}, batch_size::Int) where {T,L}
    return batch(dataset, rand(rng, 1:(dataset.n), batch_size))
end
-/
def batchWithRNG {R : Type} (sample : R → Nat → Int → Jl (List Int))
    (rng : R) (d : SymReg.Loss.Basic) (size : Int) : Jl BatchView :=
  (sample rng d.columns.length size).map (batch d)

-- Source: src/Dataset.jl:313-315
/-
function batch(dataset::BasicDataset, batch_size::Int)
    return batch(default_rng(), dataset, batch_size)
end
-/
def batchDefault {R : Type} (sample : R → Nat → Int → Jl (List Int))
    (rng : R) (d : SymReg.Loss.Basic) (size : Int) : Jl BatchView :=
  batchWithRNG sample rng d size

-- Source: src/Dataset.jl:296-304
-- function Base.fill!(d::Dataset, val)
--     _fill!(d.X, val)
--     _fill!(d.y, val)
--     _fill!(d.weights, val)
--     _fill!(d.extra, val)
--     Xe = eval_X(d)
--     Xe === d.X || _fill!(Xe, val)
--     return d
-- end
def fillDatasetWithEvalX {D R V S : Type} [DecidableEq R]
    (readProperty : D → String → Effect S (FillValue R))
    (readEvalX : D → Effect S (FillValue R))
    (fillArray : R → V → Effect S R) (d : D) (v : V) : Effect S D := fun s =>
  match fillDataset readProperty fillArray d v s with
  | (.error e, s') => (.error e, s')
  | (.ok d', s') =>
    match readProperty d "X" s' with
    | (.error e, s1) => (.error e, s1)
    | (.ok xVal, s1) =>
      match readEvalX d s1 with
      | (.error e, s2) => (.error e, s2)
      | (.ok xeVal, s2) =>
        let sameRef := match xVal, xeVal with
          | .array rx, .array rxe => decide (rx = rxe)
          | _, _ => false
        if sameRef then (.ok d', s2)
        else
          match fillValue fillArray v xeVal s2 with
          | (.error e, s3) => (.error e, s3)
          | (.ok _, s3) => (.ok d', s3)

/-- `eval_X` selection in `src/Dataset.jl:99-101, 235, 326`: Matrix datasets store
a transposed `FeatureMajorMatrix` copy, non-Matrix datasets alias `X`. -/
inductive EvalXKind where
  | featureMajor
  | aliased
  deriving DecidableEq

def selectEvalXKind (isMatrix : Bool) : EvalXKind :=
  if isMatrix then .featureMajor else .aliased

/-- `eval_tree_dispatch` input selection (`src/LossFunctions.jl:88, 105`):
uses `dataset.X` under `turbo = true` and `eval_X(dataset)` under `turbo = false`. -/
def dispatchInputMatrix {M : Type} (turbo : Bool) (rawX evalX : M) : M :=
  if turbo then rawX else evalX

/-- `expected_array_type(::FeatureMajorMatrix{T}, ::Type)` (`src/InterfaceDynamicExpressions.jl:123`,
`src/TemplateExpression.jl:903-905`): `Vector{T}` for ordinary expressions and `Any` for
`TemplateExpression`. -/
def expectedArrayTypeFeatureMajor (isTemplate : Bool) (vecTypeId : Nat) : Option Nat :=
  if isTemplate then none else some vecTypeId

end SymReg.Data
