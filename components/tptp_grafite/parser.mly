%{
  (* header *)
  open Ast
  open Parsing
  open Lexing
  
  let parse_error s = Printf.eprintf "%s: " s ;;
  let rm_q s = String.sub s 1 (String.length s - 2) ;;
  
%}
  %token <string> TYPE
  %token <string> COMMENT
  %token <int> NUM
  %token <string> LNAME
  %token <string> UNAME
  %token <string> QSTRING
  %token COMMA
  %token INCLUSION
  %token LPAREN
  %token RPAREN
  %token CNF
  %token TRUE
  %token FALSE
  %token IOR
  %token NOT
  %token NIEQ
  %token IEQ
  %token PEQ
  %token DOT
  %token EOF

  %type <Ast.ast list> main
  %start main
%%
  main: 
    | tptp_input EOF {[$1]}
    | tptp_input main {$1::$2}
    | error { 
        let start_pos = rhs_start_pos 1 in
				let end_pos = rhs_end_pos 1 in
				Printf.eprintf "from line %d char %d to line %d char %d\n" 
          start_pos.pos_lnum (start_pos.pos_cnum - start_pos.pos_bol)
          end_pos.pos_lnum (end_pos.pos_cnum - end_pos.pos_bol);
        exit 1
       }
  ;

  tptp_input:
    | annot_formula {$1}
    | include_ {$1}
    | comment {$1}
  ;
 
  annot_formula: 
    | CNF LPAREN 
            name COMMA formula_type COMMA formula formula_source_and_infos 
          RPAREN DOT {
            AnnotatedFormula ($3,$5,$7,fst $8,snd $8)  
      }
  ;
  
  formula_type: 
    | TYPE {
        match $1 with
        | "axiom" -> Axiom 
        | "hypothesis" -> Hypothesis
        | "definition" -> Definition
        | "lemma" -> Lemma
        | "theorem" -> Theorem
        | "conjecture" -> Conjecture
        | "lemma_conjecture" -> Lemma_conjecture
        | "negated_conjecture" -> Negated_conjecture
        | "plain" -> Plain
        | "unknown" -> Unknown
        | _ -> assert false
      }
  ;
  
  formula:
    | LPAREN disjunction RPAREN {$2}
    | disjunction {$1}
  ;

  disjunction:
    | literal {$1}
    | literal IOR disjunction {
        Disjunction ($1,$3)
      } 
  ;

  literal:
    | NOT atom { NegAtom $2 } 
    | atom { Atom $1 } 
  ;

  atom: 
    | atomic_word LPAREN term_list RPAREN { Predicate ($1,$3) }
    | atomic_word { Proposition $1 } 
    | TRUE { True } 
    | FALSE { False }
    | term IEQ term { Eq ($1,$3) }
    | term NIEQ term { NotEq ($1,$3) }
    | PEQ LPAREN term COMMA term RPAREN { Eq ($3,$5) }
  ;

  term_list:
    | term { [$1] }
    | term COMMA term_list { $1 :: $3 }
  ;

  term:
    | upper_word { Variable $1 }
    | atomic_word LPAREN term_list RPAREN { Function ($1,$3) }
    | atomic_word { Constant $1 }
  ;

  upper_word: UNAME { $1 } ;
  
  atomic_word:
    | LNAME { $1 }
    | QSTRING { rm_q $1 }
    | TYPE { (* workaround! *)
      match $1 with 
      | "theorem" -> "theoremP" 
      | "axiom" -> "axiomP" 
      | s -> prerr_endline s;assert false }
  ;
  
  formula_source_and_infos:
        | { NoSource, [NoInfo] }
    | COMMA { assert false }
  ;
    
  include_: 
    | INCLUSION LPAREN QSTRING selection_of_formulae RPAREN DOT {
        let fname = rm_q $3 in 
        Inclusion (fname,$4)
    } 
  ;
  
  selection_of_formulae: 
    | { [] } 
    | COMMA name selection_of_formulae { $2::$3 } 
  ;
  
  comment: COMMENT {Comment $1} ;

  name: NUM { string_of_int $1} | LNAME { $1 } | UNAME { $1 } ;
%%
  (* trailer *)
