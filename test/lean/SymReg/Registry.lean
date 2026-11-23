import DynExpr.Registry.Types
import SymReg.Complexity
import SymReg.ConstraintsProofs
import SymReg.CrossoverProofs
import SymReg.Loss
import SymReg.HofMig
import SymReg.SimpCons
import SymReg.Population
import SymReg.MutateGen
import SymReg.Mutations
import SymReg.Search
import SymReg.Plugins
import SymReg.Options
import SymReg.MLJ
import SymReg.Templates
import SymReg.ConstOpt
import SymReg.Interface
import SymReg.Ext
import SymReg.Operators
import SymReg.Infra
import SymReg.CrossMut
import SymReg.Units
import SymReg.Backsolve
import SymReg.Data.Properties
import SymReg.PopMember.Properties
import SymReg.Search.DriverProperties
import SymReg.Search.Migration
import SymReg.Backsolve.FitProperties
import SymReg.Search.Serial
import SymReg.Search.HallStream

/-!
Registry of SymbolicRegression.jl properties, in the format of the DynamicExpressions
formalization (`DynExpr.Registry.Entry`). Julia files are paths in the SymbolicRegression.jl
repository at `upstream/master` 103f5d42.
-/

namespace SymReg.Registry
open DynExpr.Registry

/-- Entries of the first slices (crossover, complexity, constraints). -/
def core : List Entry := [
  { id := "crossover-swap"
    juliaFile := "src/MutationFunctions.jl"
    juliaFns := ["crossover_trees", "_random_node_and_parent", "_find_parent"]
    statement := "crossover_trees(tree1, tree2, rng) on two distinct plain Node trees swaps exactly the two sampled subtrees: with k1, k2 the preorder indices drawn by the two rand(rng, NodeSampler(; tree)) calls, the first child is tree1 with its k1-th node replaced by tree2's k2-th subtree and the second child is tree2 with its k2-th node replaced by tree1's k1-th subtree; both parents and every other existing object are unchanged, and both children consist of newly allocated objects only."
    preconditions := "Plain Node (preserve_sharing = false); tree1 !== tree2; both finite well-formed trees (unfold succeeds; Tree.WF with degrees <= D, op <= 255, features <= 65535); aliasing inside or between the parents allowed; arbitrary RNG index stream."
    status := .proven
    prop := ``SymReg.Crossover.crossover_swap
    thm := some ``SymReg.Crossover.crossover_swap_holds },
  { id := "complexity-weighted"
    juliaFile := "src/Complexity.jl"
    juliaFns := ["compute_complexity", "_compute_complexity", "ComplexityMapping"]
    statement := "compute_complexity(tree, options; break_sharing) equals the weighted node count: on plain Node, or with break_sharing=Val(true), the signed 64-bit machine sum of the per-operator/variable/constant weights (unit weights when the mapping is unused) over all unfolded nodes; on GraphNode with the default break_sharing=Val(false), the signed 64-bit machine sum of weights over the distinct reachable node objects (shared objects counted once, as count_nodes does)."
    preconditions := "complexity_mapping is a ComplexityMapping{Int} (not a function); finite well-formed tree (unfold succeeds; Tree.WF); every feature index and (degree, op) pair of the tree indexes the weight vectors when the mapping is used."
    status := .proven
    prop := ``SymReg.Complexity.complexity_weighted
    thm := some ``SymReg.Complexity.complexity_weighted_holds
    notes := "Fixed by PR #786: _compute_complexity passes f_on_shared=(result, is_shared) -> is_shared ? zero(CT) : result (src/Complexity.jl:61), as count_nodes does, so with the identity map (GraphNode, break_sharing=Val(false)) each reachable object's weight is counted once and repeat visits contribute zero." },
  { id := "complexity-weighted-tree"
    juliaFile := "src/Complexity.jl"
    juliaFns := ["compute_complexity", "_compute_complexity", "past_complexity_limit"]
    statement := "Companion of complexity-weighted: on plain Node trees, and with break_sharing=Val(true) on any node type, compute_complexity is the signed 64-bit machine sum of the weights over all unfolded nodes (unit weights, i.e. count_nodes, when the mapping is unused)."
    preconditions := "As complexity-weighted, without the identity cache (plain Node, or break_sharing=Val(true))."
    status := .proven
    prop := ``SymReg.Complexity.complexity_weighted_tree
    thm := some ``SymReg.Complexity.complexity_weighted_tree_holds },
  { id := "constraints-accept"
    juliaFile := "src/CheckConstraints.jl"
    juliaFns := ["check_constraints", "flag_operator_complexity", "_check_operator_constraints",
      "count_max_nestedness", "flag_illegal_nests"]
    statement := "check_constraints(tree, options, maxsize, cached_size) on a plain Node returns true exactly when the signed 64-bit weighted complexity is <= maxsize, the depth is <= maxdepth, every argument i of every node whose operator has a limit cons[i] != -1 has signed 64-bit weighted complexity <= cons[i], and for every nested constraint (op => [nested_op => max]) every node with operator op has at most max nodes of nested_op on any path below it."
    preconditions := "Plain Node; finite well-formed tree (Tree.WF); complexity_mapping is a ComplexityMapping{Int} covering the tree; op_constraints and nested_constraints shaped as Options builds them (degree-d limit tuples have d entries; nested degrees and op indices >= 1); cached_size is nothing or that signed 64-bit weighted complexity."
    status := .proven
    prop := ``SymReg.Constraints.constraints_accept
    thm := some ``SymReg.Constraints.constraints_accept_holds }
]

/-- Every registered property. -/
def all : List Entry :=
  core
    ++ SymReg.Loss.entries
    ++ SymReg.HofMig.entries
    ++ SymReg.SimpCons.entries
    ++ SymReg.Population.entries
    ++ SymReg.MutateGen.entries
    ++ SymReg.Mutations.entries
    ++ SymReg.Search.entries
    ++ SymReg.Plugins.entries
    ++ SymReg.Options.entries
    ++ SymReg.MLJ.entries
    ++ SymReg.Templates.entries
    ++ SymReg.ConstOpt.entries
    ++ SymReg.Interface.entries
    ++ SymReg.Ext.entries
    ++ SymReg.Operators.entries
    ++ SymReg.Infra.entries
    ++ SymReg.CrossMut.entries
    ++ SymReg.Units.entries
    ++ SymReg.Backsolve.entries
    ++ SymReg.Data.entries
    ++ SymReg.PopMember.entries
    ++ SymReg.Search.driverEntries
    ++ SymReg.Search.migrationEntries
    ++ SymReg.Backsolve.fitPropertyEntries
    ++ SymReg.Search.serialEntries
    ++ SymReg.Search.hallStreamEntries

/-- Ids of properties about fixed package code that takes no inputs. -/
def staticFacts : List String := []

end SymReg.Registry
