%{
  (* header *)
  open AstTHF
  open Parsing
  open Lexing
  module T = CicNotationPt
  
  let parse_error s = Printf.eprintf "%s: " s ;;
  let rm_q s = String.sub s 1 (String.length s - 2) ;;

let reserved = [
  "in","In";
  "to","To";
  "theorem","Theorem";
];;

let unreserve k =
  try List.assoc k reserved with Not_found -> k
;;

  
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
  %token NOT
  %token IAND
  %token IOR
  %token NIEQ
  %token IEQ
  %token XOR
  %token IMPLY
  %token IMPLYLR
  %token COIMPLY
  %token PEQ
  %token DOT
  %token EOF
  %token FORALL
  %token EXISTS
  %token LAMBDA
  %token COLON
  %token BEGINVARLIST
  %token ENDVARLIST
  %token APPLY
  %token TYPE_I
  %token TYPE_O
  %token TYPE_U
  %token TO
  %token THF

  %left IOR
  %left IAND 
  %nonassoc NOT
  %right TO
  %left APPLY

  %type <AstTHF.ast list> main
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
 
  formula_source_and_infos:
    | { () }
    | COMMA { assert false }
  ;

  annot_formula: 
    | THF LPAREN name COMMA formula_type COMMA 
      term formula_source_and_infos RPAREN DOT {
         match $5 with
         | Definition ->
             (match $7 with
             | T.Appl [T.Symbol("Eq",_);T.Ident(name,_);body] -> 
                   ThfDefinition($3,unreserve name,body)
             | _ -> prerr_endline ("near " ^ $3); assert false)
         | Type -> 
             (match $7 with
             | T.Cast (T.Ident(name,_),ty) -> ThfType($3,unreserve name,ty)
             | _ -> assert false)
         | _ -> ThfFormula($3,$5,$7)  
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
        | "type" -> Type
        | _ -> assert false
      }
  ;

  quantifier : 
    | FORALL {`Forall}  
    | EXISTS {`Exists}
    | LAMBDA {`Lambda}

  vardecl : 
    | UNAME { T.Ident($1,None), None }
    | UNAME COLON term { T.Ident($1,None),Some $3 }
   
  varlist : 
    | vardecl { [$1] } 
    | vardecl COMMA varlist { $1 :: $3 }
  
  term:
    | quantifier BEGINVARLIST varlist ENDVARLIST COLON term {
        List.fold_right (fun v t -> T.Binder($1,v,t)) $3 $6
        }
    | term APPLY term { 
        match $1 with 
        | T.Appl l -> T.Appl (l @ [$3])
        | x -> T.Appl ([$1; $3]) 
    }
    | LPAREN term COLON term RPAREN { T.Cast ($2,$4) }
    | term TO term { T.Binder (`Forall,(T.Ident("_",None),Some $1),$3) }
    | term IMPLY term { T.Binder (`Forall,(T.Ident("_",None),Some $1),$3) }
    | term IMPLYLR term { T.Binder (`Forall,(T.Ident("_",None),Some $3),$1) }
    | term COIMPLY term { T.Appl [T.Symbol("Iff",0);$1;$3] }
    | term XOR term { T.Appl [T.Symbol("Xor",0);$1;$3] }
    | term IEQ term { T.Appl [T.Symbol("Eq",0);$1;$3] }
    | term NIEQ term { T.Appl [T.Symbol("NotEq",0);$1;$3] }
    | term IAND term { T.Appl [T.Symbol("And",0);$1;$3] }
    | term IOR term { T.Appl [T.Symbol("Or",0);$1;$3] }
    | NOT term { T.Appl [T.Symbol("Not",0);$2] }
    | LPAREN term RPAREN {$2}
    | LNAME { T.Ident(unreserve $1,None) }
    | UNAME { T.Ident($1,None) }
    | TYPE_I { T.Symbol("i",0) }
    | TYPE_O { T.Symbol("o",0) }
    | TYPE_U { T.Sort (`NType "0") }
    | FALSE { T.Symbol("False",0)}
    | TRUE { T.Symbol("True",0)}
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
