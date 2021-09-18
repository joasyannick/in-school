module String : CodeGenerator.SIG = struct
    let rec of_expression = function
          Type.Type (dataType, genericity) ->
              String.concat " " (dataType :: genericity)
        | Type.Parenthesized expression ->
              "(" ^ (of_expression expression) ^ ")"
        | Type.Product product ->
              String.concat " * " (List.map of_expression product)
        | Type.FunctionSignature (domain, codomain) ->
              (of_expression domain) ^ " -> " ^ (of_expression codomain)


    let of_argument argument =
        let of_identifier = Type.argIdentifier argument
        and of_type = of_expression (Type.argType argument)
        in  "(" ^ of_identifier ^ " : " ^ of_type ^ ")"


    let of_arguments arguments =
        String.concat " " (List.map of_argument arguments)


    let of_constructor constructor =
        let of_identifier = Type.consIdentifier constructor
        and of_arguments = of_arguments (Type.arguments constructor)
        in  of_identifier ^ " " ^ of_arguments


    let of_constructors constructors =
        let of_constructors = List.map of_constructor constructors
        in  "\n\t\t  " ^ (String.concat "\n\t\t| " of_constructors) ^ "."


    let of_parameter parameter =
        let of_identifier = Type.paramIdentifier parameter
        and of_type = of_expression (Type.paramType parameter)
        in  "(" ^ of_identifier ^ " : " ^ of_type ^ ")"


    let of_parameters parameters =
        String.concat " " (List.map of_parameter parameters)


    let of_inputVariable = "__input"


    let of_type declaredType parameters =
        let paramIdentifiers = List.map Type.paramIdentifier parameters
        in  of_expression (Type.Type (declaredType, paramIdentifiers))


    let of_inputs declaredType parameters of_inputVariable =
        let of_parameter parameter =
            let of_identifier = Type.paramIdentifier parameter
            and of_type = of_expression (Type.paramType parameter)
            in  "{" ^ of_identifier ^ ": " ^ of_type ^ "}"
        in  let of_parameters = List.map of_parameter parameters
            and of_type = of_type declaredType parameters
            in  (String.concat " " of_parameters) ^ " (" ^ of_inputVariable ^ " : " ^ of_type ^ ")"


    let of_observerPattern constructor =
        let of_identifier = Type.consIdentifier constructor
        and of_pattern = List.map (fun argument -> "_") (Type.arguments constructor)
        in  of_identifier ^ " " ^ (String.concat " " of_pattern)


    let of_observer declaredType parameters constructors constructor =
        let of_identifier = Type.consIdentifier constructor
        and of_inputs = of_inputs declaredType parameters of_inputVariable
        and of_pattern = of_observerPattern constructor
        in  "Definition is" ^ of_identifier ^ " " ^ of_inputs ^ " : Prop :=" ^
            "\n\t\tmatch "^ of_inputVariable ^ " with" ^
            "\n\t\t\t  " ^ of_pattern ^ " => True" ^
            (if List.length constructors >= 2
             then "\n\t\t\t| _ => False"
             else "") ^
            "\n\t\tend."


    let of_observers declaration =
        let declaredType = Type.declaredType declaration
        and parameters = Type.parameters declaration
        and constructors = Type.constructors declaration
        in  let of_observers = List.map (of_observer declaredType parameters constructors) constructors
            in  "\n\n\n\t" ^ (String.concat "\n\n\n\t" of_observers)


    let of_getterPattern constructor argument =
        let of_identifier = Type.consIdentifier constructor
        and of_pattern = List.map
                (fun a -> if a = argument then Type.argIdentifier a else "_")
                (Type.arguments constructor)
        in  of_identifier ^ " " ^ (String.concat " " of_pattern)


    let of_precondition = "__precondition"


    let of_getter declaration constructor argument =
        let of_consIdentifier = Type.consIdentifier constructor
        and of_argIdentifier = Type.argIdentifier argument
        and of_argType = of_expression (Type.argType argument)
        and of_inputs = of_inputs (Type.declaredType declaration) (Type.parameters declaration) of_inputVariable
        and of_pattern = of_getterPattern constructor argument
        in  let dependancy = List.exists
                (fun a -> (Type.argIdentifier a = of_argType) & (of_expression (Type.argType a) = "Type"))
                (Type.arguments constructor)
            and of_withDependancy =
                "Definition get" ^ of_consIdentifier ^ (String.capitalize of_argIdentifier) ^ " " ^ of_inputs ^ " : " ^
                    "forall (" ^ of_precondition ^ " : is" ^ of_consIdentifier ^ " " ^ of_inputVariable ^ "), get" ^
                    of_consIdentifier ^ (String.capitalize of_argType) ^ " " ^ of_inputVariable ^ " " ^ of_precondition ^ " :=" ^
                "\n\t\tmatch " ^ of_inputVariable ^ " return forall (" ^ of_precondition ^ " : is" ^ of_consIdentifier ^ " " ^
                    of_inputVariable ^ "), get" ^ of_consIdentifier ^ (String.capitalize of_argType) ^ " " ^ of_inputVariable ^
                    " " ^ of_precondition ^ " with" ^
                "\n\t\t\t  " ^ of_pattern ^ " => fun " ^ of_precondition ^" => " ^ of_argIdentifier ^
                (if List.length (Type.constructors declaration) >= 2
                 then "\n\t\t\t| _ => fun " ^ of_precondition ^ " => match " ^ of_precondition ^ " with end"
                 else "") ^
                "\n\t\tend."
            and of_withoutDependancy =
                "Definition get" ^ of_consIdentifier ^ (String.capitalize of_argIdentifier) ^ " " ^ of_inputs ^ " : " ^
                "is" ^ of_consIdentifier ^ " " ^ of_inputVariable ^ " -> " ^ of_argType ^ " :=" ^
                "\n\t\tmatch " ^ of_inputVariable ^ " with" ^
                "\n\t\t\t  " ^ of_pattern ^ " => fun " ^ of_precondition ^" => " ^ of_argIdentifier ^
                (if List.length (Type.constructors declaration) >= 2
                 then "\n\t\t\t| _ => fun " ^ of_precondition ^ " => match " ^ of_precondition ^ " with end"
                 else "") ^
                "\n\t\tend."
            in  match dependancy with
                  true -> of_withDependancy
                | false -> of_withoutDependancy


    let of_constructorGetters declaration constructor =
        let arguments = Type.arguments constructor
        in  let of_constructorGetters = List.map (of_getter declaration constructor) arguments
            in String.concat "\n\n\n\t" of_constructorGetters


    let of_getters declaration =
        let constructors = Type.constructors declaration
        in  let of_getters = List.map (of_constructorGetters declaration) constructors
            in  "\n\n\n\t" ^ (String.concat "\n\n\n\t" of_getters)


    let of_rootVariable = "__root"
    let of_labelType = "Label"
    let of_labeledConstructor = "Labeled"
    let of_tagArgument = "__tag"
    let of_dataArgument = "__data"
    let of_refConstructor = "Reference"
    let of_subtermType = "subterm"


    let of_subtermCase declaredType parameters constructor argument =
        let of_consIdentifier = Type.consIdentifier constructor
        and of_argIdentifier = Type.argIdentifier argument
        and of_arguments = String.concat " " (List.map Type.argIdentifier (Type.arguments constructor))
        and of_parameters = String.concat " " (List.map Type.paramIdentifier parameters)
        in  "Sub" ^ of_consIdentifier ^ (String.capitalize of_argIdentifier) ^ " : forall " ^
            of_arguments ^ ", " ^ of_subtermType ^ " " ^ of_rootVariable ^ " (" ^
            of_consIdentifier ^ " " ^ of_parameters ^ " " ^ of_arguments ^ ") -> " ^
            of_subtermType ^ " " ^ of_rootVariable ^ " " ^ of_argIdentifier


    let recursiveArguments declaredType parameters constructor =
        let arguments = Type.arguments constructor
        in  List.filter
                (fun argument -> of_expression (Type.argType argument) =
                    of_type declaredType parameters)
                arguments


    let of_subtermCases declaredType parameters constructor =
        let arguments = recursiveArguments declaredType parameters constructor
        in  String.concat "\n\t\t| " (List.map
                (of_subtermCase declaredType parameters constructor)
                arguments)


    let recursiveConstructors declaration =
        let declaredType = Type.declaredType declaration
        and parameters = Type.parameters declaration
        and constructors = Type.constructors declaration
        in  List.filter
                (fun constructor -> List.exists
                    (fun argument -> of_expression (Type.argType argument) =
                        of_type declaredType parameters)
                    (Type.arguments constructor))
                constructors


    let of_subtermConstructors declaration =
        let of_declaredType = Type.declaredType declaration
        and parameters = Type.parameters declaration
        and constructors = recursiveConstructors declaration
        in  if constructors = []
            then ""
            else "\n\t\t| " ^ (String.concat "\n\t\t| "
                    (List.map
                (of_subtermCases of_declaredType parameters)
                constructors))

    
    let of_subterm declaration =
        let of_declaredType = Type.declaredType declaration
        and parameters = Type.parameters declaration
        and of_parameters = String.concat " " (List.map Type.paramIdentifier (Type.parameters declaration))
        in  let of_inputs = of_inputs of_declaredType parameters of_rootVariable
            and of_type = of_type of_declaredType parameters
            and of_subtermConstructors = of_subtermConstructors declaration
            in  "\n\n\n\tInductive " ^ of_subtermType ^ " " ^ of_inputs ^ " : " ^ of_type ^ " -> Type :=" ^
                "\n\t\t  SubRoot : " ^ of_subtermType ^ " " ^ of_rootVariable ^ " " ^ of_rootVariable ^
                "\n\t\t| SubLabeled : forall " ^ of_tagArgument ^ " " ^ of_dataArgument ^ ", " ^ of_subtermType ^ " " ^
                   of_rootVariable ^ " (" ^ of_labeledConstructor ^ " " ^ of_parameters ^ " " ^
                      of_tagArgument ^ " " ^ of_dataArgument ^ ") -> " ^ of_subtermType ^ " " ^
                   of_rootVariable ^ " " ^ of_dataArgument ^
                of_subtermConstructors ^ "."


    let of_module declaration =
        let of_moduleIdentifier = String.capitalize (Type.declaredType declaration)
        and of_declaredType = Type.declaredType declaration
        and parameters = List.map Type.paramIdentifier (Type.parameters declaration)
        in  let labelConstructor = Type.Constructor (
                of_labeledConstructor, [Type.Argument (of_tagArgument, Type.Type (of_labelType, []));
                    Type.Argument (of_dataArgument, Type.Type (of_declaredType, parameters))])
            and referenceConstructor = Type.Constructor (
                    of_refConstructor, [Type.Argument (of_tagArgument, Type.Type (of_labelType, []))])
            in  let augmentedDeclaration = Type.Declaration (
                    Type.declaredType declaration,
                    Type.parameters declaration,
                    (Type.constructors declaration) @ [labelConstructor; referenceConstructor])
                    in  let of_parameters = of_parameters (Type.parameters augmentedDeclaration)
                        and of_constructors = of_constructors (Type.constructors augmentedDeclaration)
                        and of_observers = of_observers augmentedDeclaration
                        and of_getters = of_getters augmentedDeclaration
                        and of_subterm = of_subterm declaration
                        in  "\nModule " ^ of_moduleIdentifier ^ "." ^
                            "\n\tParameter " ^ of_labelType ^ " : Type." ^
                            "\n\n\tCoInductive " ^ of_declaredType ^ " " ^ of_parameters ^ " :=" ^
                            of_constructors ^
                            of_observers ^
                            of_getters ^
                            of_subterm ^
                            "\nEnd " ^ of_moduleIdentifier ^ "."


    let of_comodule declaration =
        let of_moduleIdentifier = "Co" ^ (String.capitalize (Type.declaredType declaration))
        and of_declaredType = Type.declaredType declaration
        and of_parameters = of_parameters (Type.parameters declaration)
        and of_constructors = of_constructors (Type.constructors declaration)
        and of_observers = of_observers declaration
        and of_getters = of_getters declaration
        in  "Module " ^ of_moduleIdentifier ^ "." ^
            "\n\tCoInductive " ^ of_declaredType ^ " " ^ of_parameters ^ " :=" ^
            of_constructors ^
            of_observers ^
            of_getters ^
            "\nEnd " ^ of_moduleIdentifier ^ "."


    let of_declaration declaration =
        let of_comodule = of_comodule declaration
        and of_module = of_module declaration
        in  of_comodule ^ "\n\n\n\n\n" ^ of_module
end
