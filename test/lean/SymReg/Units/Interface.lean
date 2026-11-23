import SymReg.Units.Sound

/-! `src/InterfaceDynamicQuantities.jl`: `get_units`, `get_si_units`, `get_sym_units`,
`get_dimensions_type`. DynamicQuantities parsing and conversion are arbitrary library
functions. -/

namespace SymReg.Units
open DynExpr

/-- Unit information passed to `get_units` (`src/InterfaceDynamicQuantities.jl:24-47`):
`nothing`, a string, a `Quantity`, an `AbstractDimensions`, a `Real`, a vector, or anything
else. `S` is the type of DynamicQuantities objects. -/
inductive UnitSpec (S : Type) where
  | nothing
  | str (s : String)
  | quantity (q : S)
  | dims (d : S)
  | real (v : JF)
  | vec (xs : List (UnitSpec S))
  | other

/-- Results of `get_units`: `nothing`, one quantity, or a `Vector{Quantity{T,D}}`. -/
inductive Units (Qt : Type) where
  | none
  | scalar (q : Qt)
  | vector (qs : List Qt)
  deriving DecidableEq, Repr

/-- The library calls of `get_units` for a numeric type `T` and dimension type `D`:
`one(Quantity{T,D})`, the parser `f` (`uparse` or `sym_uparse`),
`convert(Quantity{T,D}, x)` for a quantity, `convert(Quantity{T,D}, Quantity(one(T), x))`
for dimensions, and `Quantity(convert(T, x), D)` for a real. -/
structure UnitLib (S Qt : Type) where
  one : Qt
  parse : String → Jl S
  convQ : S → Jl Qt
  convD : S → Jl Qt
  real : JF → Jl Qt

/-- The fallback error of `src/InterfaceDynamicQuantities.jl:24-28`. -/
def unitsError : JlError := .errorException
  "Unit information must be passed as one of `AbstractDimensions`, `AbstractQuantity`, `AbstractString`, `Function`."

/-- `convert(Quantity{T,D}, get_units(T, D, xi, f))` for a vector element: only a scalar
result converts (`src/InterfaceDynamicQuantities.jl:46`). -/
def elemOf {Qt : Type} : Units Qt → Jl Qt
  | .scalar q => .ok q
  | .none => .error (.methodError "Cannot `convert` an object of type Nothing")
  | .vector _ => .error (.methodError "Cannot `convert` a vector to a Quantity")

mutual
/-- `get_units(T, D, x, f)` (`src/InterfaceDynamicQuantities.jl:24-47`). -/
def getUnits {S Qt : Type} (lib : UnitLib S Qt) : UnitSpec S → Jl (Units Qt)
  | .nothing => .ok .none
  | .str s => if s.isEmpty then .ok (.scalar lib.one) else do
      let q ← lib.parse s
      let u ← lib.convQ q
      pure (.scalar u)
  | .quantity q => do let u ← lib.convQ q; pure (.scalar u)
  | .dims d => do let u ← lib.convD d; pure (.scalar u)
  | .real v => do let u ← lib.real v; pure (.scalar u)
  | .vec xs => do let qs ← getUnitsL lib xs; pure (.vector qs)
  | .other => .error unitsError
/-- The comprehension `Quantity{T,D}[get_units(T, D, xi, f) for xi in x]`. -/
def getUnitsL {S Qt : Type} (lib : UnitLib S Qt) : List (UnitSpec S) → Jl (List Qt)
  | [] => .ok []
  | x :: xs => do
    let u ← getUnits lib x
    let q ← elemOf u
    let qs ← getUnitsL lib xs
    pure (q :: qs)
end

/-- `get_si_units(T, units)` and `get_sym_units(T, units)`
(`src/InterfaceDynamicQuantities.jl:55-66`) are `get_units` with the SI library
(`Dimensions{DEFAULT_DIM_BASE_TYPE}`, `uparse`) or the symbolic one
(`SymbolicDimensions{DEFAULT_DIM_BASE_TYPE}`, `sym_uparse`). -/
def getSiUnits {S Si Sym : Type} (libs : UnitLib S Si × UnitLib S Sym) :
    UnitSpec S → Jl (Units Si) := getUnits libs.1

/-- See `getSiUnits`. -/
def getSymUnits {S Si Sym : Type} (libs : UnitLib S Si × UnitLib S Sym) :
    UnitSpec S → Jl (Units Sym) := getUnits libs.2

theorem getUnitsL_all2 {S Qt : Type} (lib : UnitLib S Qt) :
    ∀ (xs : List (UnitSpec S)) (qs : List Qt),
      getUnitsL lib xs = .ok qs ↔ All2 (fun x q => getUnits lib x = .ok (.scalar q)) xs qs
  | [], qs => by
    simp only [getUnitsL]
    constructor
    · intro h; cases h; exact .nil
    · intro h; cases h; rfl
  | x :: xs, qs => by
    simp only [getUnitsL]
    constructor
    · intro h
      cases hu : getUnits lib x with
      | error e => simp [hu, bind, Except.bind] at h
      | ok u =>
        cases u with
        | none => simp [hu, elemOf, bind, Except.bind] at h
        | vector _ => simp [hu, elemOf, bind, Except.bind] at h
        | scalar q =>
          cases hr : getUnitsL lib xs with
          | error e => simp [hu, hr, elemOf, bind, Except.bind] at h
          | ok qs' =>
            simp [hu, hr, elemOf, bind, Except.bind, pure, Except.pure] at h
            subst h
            exact .cons hu ((getUnitsL_all2 lib xs qs').mp hr)
    · intro h
      cases h with
      | cons h1 h2 =>
        rw [(getUnitsL_all2 lib xs _).mpr h2]
        simp [h1, elemOf, bind, Except.bind, pure, Except.pure]

/-- `get_units` dispatch: `nothing` gives `nothing`; the empty string gives
`one(Quantity{T,D})` without parsing; other strings are parsed and converted; quantities,
dimensions and reals are converted; a vector succeeds exactly when every element yields a
single quantity, in order (a `nothing` element throws the conversion `MethodError`); any
other input throws the documented error. -/
def units_get_units : Prop :=
  ∀ (S Qt : Type) (lib : UnitLib S Qt) (s : String) (xs : List (UnitSpec S)) (qs : List Qt),
    getUnits lib .nothing = .ok .none ∧
    (s.isEmpty = true → getUnits lib (.str s) = .ok (.scalar lib.one)) ∧
    (s.isEmpty = false → getUnits lib (.str s) = (do
      let q ← lib.parse s; let u ← lib.convQ q; pure (.scalar u))) ∧
    (getUnits lib (.vec xs) = .ok (.vector qs) ↔
      All2 (fun x q => getUnits lib x = .ok (.scalar q)) xs qs) ∧
    (∀ (pre rest : List (UnitSpec S)) (prefixQs : List Qt),
      All2 (fun x q => getUnits lib x = .ok (.scalar q)) pre prefixQs →
      getUnits lib (.vec (pre ++ .nothing :: rest)) =
        .error (.methodError "Cannot `convert` an object of type Nothing")) ∧
    getUnits lib .other = .error unitsError ∧
    (∀ q, getUnits lib (.quantity q) = (lib.convQ q).map Units.scalar) ∧
    (∀ d, getUnits lib (.dims d) = (lib.convD d).map Units.scalar) ∧
    (∀ v, getUnits lib (.real v) = (lib.real v).map Units.scalar) ∧
    (∀ (Sym : Type) (sym : UnitLib S Sym) (x : UnitSpec S),
      getSiUnits (lib, sym) x = getUnits lib x ∧ getSymUnits (lib, sym) x = getUnits sym x)

theorem units_get_units_holds : units_get_units := by
  intro S Qt lib s xs qs
  refine ⟨rfl, fun h => by simp [getUnits, h], fun h => by simp [getUnits, h], ?_, ?_,
    rfl, ?_, ?_, ?_, fun _ _ _ => ⟨rfl, rfl⟩⟩
  · constructor
    · intro h
      simp only [getUnits] at h
      cases hr : getUnitsL lib xs with
      | error e => simp [hr, bind, Except.bind] at h
      | ok qs' =>
        simp [hr, bind, Except.bind, pure, Except.pure] at h
        subst h
        exact (getUnitsL_all2 lib xs qs').mp hr
    · intro h
      simp [getUnits, (getUnitsL_all2 lib xs qs).mpr h, bind, Except.bind, pure, Except.pure]
  · intro pre rest prefixQs h
    have go : getUnitsL lib (pre ++ .nothing :: rest) =
        .error (.methodError "Cannot `convert` an object of type Nothing") := by
      induction h with
      | nil => rfl
      | cons h₁ _ ih => simp [getUnitsL, h₁, ih, elemOf, bind, Except.bind]
    simp [getUnits, go, bind, Except.bind]
  · intro q; cases h : lib.convQ q <;> simp [getUnits, h, bind, Except.bind, pure, Except.pure, Except.map]
  · intro d; cases h : lib.convD d <;> simp [getUnits, h, bind, Except.bind, pure, Except.pure, Except.map]
  · intro v; cases h : lib.real v <;> simp [getUnits, h, bind, Except.bind, pure, Except.pure, Except.map]

/-! ## get_dimensions_type, src/InterfaceDynamicQuantities.jl:74-131 -/

/-- Dimension types: `Dimensions{FRInt32}` (`si`, DynamicQuantities' `DEFAULT_DIM_TYPE`),
`SymbolicDimensions{FRInt32}` (`sym`), or another. -/
inductive DimT where
  | si | sym | other (k : Nat)
  deriving DecidableEq, Repr

/-- An array element: a plain number or a quantity with its dimension type. -/
inductive Elem where
  | plain | quantity (d : DimT)
  deriving DecidableEq, Repr

/-- Array element types selecting a method: one of the listed concrete numeric types
(`src/InterfaceDynamicQuantities.jl:92-131`), a quantity type `Q` (with `dim_type(Q)` when
`Q` fixes its dimension type, `src/InterfaceDynamicQuantities.jl:82-86`), or any other
element type (`src/InterfaceDynamicQuantities.jl:74-81`). -/
inductive EltType where
  | fast | quantity (d : Option DimT) | other
  deriving DecidableEq, Repr

/-- The argument of `get_dimensions_type`. -/
inductive DimInput where
  | array (et : EltType) (xs : List Elem) | notArray
  deriving DecidableEq, Repr

/-- The dimension type of the first quantity element, or the default. -/
def firstQ (default : DimT) (xs : List Elem) : DimT :=
  match xs.find? (fun x => x != .plain) with
  | some (.quantity d) => d
  | _ => default

/-- `get_dimensions_type(A, default)`. For a quantity element type that leaves the
dimension type unspecified (`Vector{Quantity}`, `Vector{Quantity{Float64}}`),
`dim_type(Q)` is DynamicQuantities' `DEFAULT_DIM_TYPE` `Dimensions{FRInt32}` (for example,
`get_dimensions_type(Quantity[us"km"], Dimensions)` is `Dimensions{FRInt32}`). -/
def getDimensionsType (default : DimT) : DimInput → DimT
  | .notArray => default
  | .array .fast _ => default
  | .array (.quantity d) _ => d.getD .si
  | .array .other xs => firstQ default xs

/-- Elements agree with their array's element type. -/
def Consistent : EltType → List Elem → Prop
  | .fast, xs => ∀ x ∈ xs, x = .plain
  | .quantity none, xs => ∀ x ∈ xs, ∃ d, x = .quantity d
  | .quantity (some d), xs => ∀ x ∈ xs, x = .quantity d
  | .other, _ => True

theorem firstQ_plain (default : DimT) : ∀ (xs : List Elem), (∀ x ∈ xs, x = .plain) →
    firstQ default xs = default
  | [], _ => rfl
  | x :: xs, h => by
    have hx := h x List.mem_cons_self; subst hx
    simpa [firstQ] using firstQ_plain default xs fun y hy => h y (List.mem_cons_of_mem _ hy)

/-- For concrete element types and generic arrays, `get_dimensions_type` returns the
dimension type of the first quantity element, or the default when there is none; a
non-array gives the default. -/
def units_dimtype : Prop :=
  ∀ (default : DimT) (et : EltType) (xs : List Elem),
    (Consistent et xs → xs ≠ [] → et ≠ .quantity none →
      getDimensionsType default (.array et xs) = firstQ default xs) ∧
    getDimensionsType default .notArray = default

theorem units_dimtype_holds : units_dimtype := by
  intro default et xs
  refine ⟨fun hc hne het => ?_, rfl⟩
  cases et with
  | fast => exact (firstQ_plain default xs hc).symm
  | other => rfl
  | quantity d =>
    cases d with
    | none => exact absurd rfl het
    | some d =>
      cases xs with
      | nil => exact absurd rfl hne
      | cons x xs =>
        have hx := hc x List.mem_cons_self; subst hx
        simp [getDimensionsType, firstQ]

/-- The docstring "Recursively finds the dimension type from an array" for every element
type: the result is the first quantity element's dimension type. -/
def units_dimtype_abstract : Prop :=
  ∀ (default : DimT) (et : EltType) (xs : List Elem),
    Consistent et xs → xs ≠ [] → getDimensionsType default (.array et xs) = firstQ default xs

theorem units_dimtype_abstract_refuted : ¬ units_dimtype_abstract := by
  intro h
  have := h .si (.quantity none) [.quantity .sym]
    (fun x hx => ⟨.sym, by simpa using hx⟩) (by simp)
  simp [getDimensionsType, firstQ] at this

/-- The hypotheses of `units_dimtype` and `units_get_units` are satisfiable. -/
example : Consistent (.quantity (some .sym)) [.quantity .sym] ∧ [Elem.quantity .sym] ≠ [] ∧
    EltType.quantity (some .sym) ≠ .quantity none ∧ "".isEmpty = true ∧ "m".isEmpty = false :=
  ⟨fun x hx => by simpa using hx, by simp, by decide, rfl, rfl⟩

end SymReg.Units
