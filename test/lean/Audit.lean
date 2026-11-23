import SymReg
import SymReg.Registry
import SymReg.Registry.AuditCore

/-! Audit of the whole SymbolicRegression.jl property registry (`SymReg.Registry.audit`).
Run with `lake env lean Audit.lean`; any failure raises an error. -/

#eval SymReg.Registry.audit SymReg.Registry.all SymReg.Registry.staticFacts
