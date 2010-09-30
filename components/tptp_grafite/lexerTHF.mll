{ 
  open ParserTHF
  exception BadToken of string 
  
  let incr_linenum lexbuf =
    let pos = lexbuf.Lexing.lex_curr_p in
    lexbuf.Lexing.lex_curr_p <- { pos with
      Lexing.pos_lnum = pos.Lexing.pos_lnum + 1;
      Lexing.pos_bol = pos.Lexing.pos_cnum;
    }
  ;;
  
}

let dust = ' ' | '\t'
let comment = '%' [^ '\n' ] * '\n'
let lname = 
  ['a'-'z'] ['a'-'z''A'-'Z''0'-'9''_']*
let uname = 
  ['A'-'Z'] ['a'-'z''A'-'Z''0'-'9''_']*
let qstring = ''' [^ ''' ]+ '''
let type_ =   
  "axiom" | "hypothesis" | "definition" | "lemma" | "theorem" |
  "conjecture" | "lemma_conjecture" | "negated_conjecture" |
  "plain" | "unknown" | "type"

let ieq = "="
let peq = "equal"
let nieq = "!="

rule yylex = parse 
   | dust { yylex lexbuf }
   | '\n' { incr_linenum lexbuf; yylex lexbuf }
   | comment { incr_linenum lexbuf; COMMENT (Lexing.lexeme lexbuf) }
   | "include" { INCLUSION }
   | type_ { TYPE (Lexing.lexeme lexbuf) }
   | "thf" { THF } 
   | "$true" { TRUE }
   | "$false" { FALSE }
   | "equal" { PEQ }
   
   | "$i" { TYPE_I }
   | "$o" { TYPE_O }
   | "$tType" { TYPE_U }
   | ">" { TO }

   | lname { LNAME (Lexing.lexeme lexbuf) }
   | uname { UNAME (Lexing.lexeme lexbuf) }

   | ['0' - '9']+ { NUM (int_of_string (Lexing.lexeme lexbuf)) }
   | ',' { COMMA }
   | '.' { DOT }
   | '(' { LPAREN }
   | ')' { RPAREN }
   | '|' { IOR }
   | '&' { IAND }
   | '~' { NOT }
   | '=' { IEQ }
   | "=>" { IMPLY }
   | "<=" { IMPLYLR }
   | "<=>" { COIMPLY }
   | "<~>" { XOR }
   | "!=" { NIEQ }
   | "!" { FORALL }
   | "?" { EXISTS }
   | "!" { FORALL }
   | "^" { LAMBDA }
   | "[" { BEGINVARLIST }
   | "]" { ENDVARLIST }
   | ":" { COLON }
   | "," { COMMA }
   | "@" { APPLY }
   | qstring { QSTRING (Lexing.lexeme lexbuf) }
   | eof { EOF } 
   | _ { raise (BadToken (Lexing.lexeme lexbuf)) }

{ (* trailer *) }
