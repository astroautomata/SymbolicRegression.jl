using SymbolicRegression

operators = SymbolicRegression.OperatorEnum(; binary_operators=[+])
try
    options = SymbolicRegression.Options(; operators, constraints=Dict((+) => (-1, 3)))
    println("generic operator constraints built successfully: ", options.op_constraints)
catch err
    if err isa KeyError && err.key == 1
        println(
            "known + operator constraint with explicit enum raises: ",
            sprint(showerror, err),
        )
        println("REPRODUCED cons-generic-operator-pairs")
        println("REPRODUCED cons-builder-pair-layout")
    else
        println("unexpected builder exception: ", sprint(showerror, err))
    end
end
