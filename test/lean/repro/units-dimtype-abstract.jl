using SymbolicRegression
using SymbolicRegression.InterfaceDynamicQuantitiesModule: get_dimensions_type
using DynamicQuantities

# The same symbolic quantity, stored with an abstract `Quantity` or an `Any` element type.
typed = get_dimensions_type(Quantity[us"km"], Dimensions)
untyped = get_dimensions_type(Any[us"km"], Dimensions)
println("get_dimensions_type(Quantity[us\"km\"], Dimensions) = ", typed)
println("get_dimensions_type(Any[us\"km\"], Dimensions) = ", untyped)
if !(typed <: SymbolicDimensions) && untyped <: SymbolicDimensions
    println("REPRODUCED units-dimtype-abstract")
end
