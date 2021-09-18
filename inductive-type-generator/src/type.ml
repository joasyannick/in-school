exception NotAType
exception NotParenthesized
exception NotAProduct
exception NotAFunctionSignature




type expression_t =
      Type of string * string list
    | Parenthesized of expression_t
    | Product of expression_t list
    | FunctionSignature of expression_t * expression_t

    
type argument_t = Argument of string * expression_t


type constructor_t = Constructor of string * argument_t list


type parameter_t = Parameter of string * expression_t


type declaration_t = Declaration of string * parameter_t list * constructor_t list




let dataType = function
      Type (dataType, _) -> dataType
    | _ -> raise NotAType


let genericity = function
      Type (_, genericity) -> genericity
    | _ -> raise NotAType


let parenthesized = function
      Parenthesized expression -> expression
    | _ -> raise NotParenthesized


let product = function
      Product product -> product
    | _ -> raise NotAProduct


let domain = function
      FunctionSignature (domain, _) -> domain
    | _ -> raise NotAFunctionSignature


let codomain = function
      FunctionSignature (_, codomain) -> codomain
    | _ -> raise NotAFunctionSignature


let argIdentifier = function Argument (identifier, _) -> identifier


let argType = function Argument (_, argumentType) -> argumentType


let consIdentifier = function Constructor (identifier, _) -> identifier


let arguments = function Constructor (_, arguments) -> arguments


let paramIdentifier = function Parameter (identifier, _) -> identifier


let paramType = function Parameter (_, parameterType) -> parameterType


let declaredType = function Declaration (identifier, _, _) -> identifier


let parameters = function Declaration (_, parameters, _) -> parameters


let constructors = function Declaration (_, _, constructors) -> constructors
