let grammar = Grammar.gcreate (Plexer.gmake ())
let declaration = Grammar.Entry.create grammar "declaration"
let loc = ref 0

EXTEND
  GLOBAL: declaration;

  declaration:
  [ [ "type"; i = LIDENT; p = LIST0 parameter; "="; c = LIST1 constructor SEP "|"  ->
          Type.Declaration (i, p, c) ] ];

  parameter:
  [ [ "("; i = LIDENT; ":"; e = expression; ")" ->
          Type.Parameter (i, e) ] ];

  constructor:
  [ [ i = UIDENT; a = LIST0 argument ->
          Type.Constructor (i, a) ] ];

  argument:
  [ [ "("; i = LIDENT; ":"; e = expression; ")" ->
          Type.Argument (i, e) ] ];

  expression:
  [ [ i = identifier; l = LIST0 identifier ->
          Type.Type (i, l) ]
  | [ "("; e = SELF; ")" ->
          Type.Parenthesized e ]
  | RIGHTA
    [ e = SELF; "->"; f = SELF ->
          Type.FunctionSignature (e, f) ]
  | [ e = SELF; "*"; l = LIST1 SELF SEP "*" ->
          Type.Product (e :: l) ] ];

  identifier:
  [ [ i = LIDENT -> i ]
  | [ i = UIDENT -> i ] ];
END

try
  let d = Grammar.Entry.parse declaration (Stream.of_channel stdin) in
  print_string (CoqGenerator.String.of_declaration d)
with Ploc.Exc(pos,ex) ->
  prerr_string "erreur ligne "; 
  prerr_int (Ploc.line_nb pos);
  prerr_string ",position "; 
  prerr_int (Ploc.bol_pos pos);
  prerr_newline()
