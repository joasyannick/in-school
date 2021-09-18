module type SIG = sig
    val of_expression: Type.expression_t -> string
    val of_argument: Type.argument_t -> string
    val of_constructor: Type.constructor_t -> string
    val of_parameter: Type.parameter_t -> string
    val of_declaration: Type.declaration_t -> string
end
