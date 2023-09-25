
let trans_atom = function 
  | Ast.True | Ast.False | Ast.Predicate _ | Ast.Proposition _ -> assert false
  | Ast.Eq (a,b) -> true, Ast.Function ("==",[Ast.Constant "_"; a; b])
  | Ast.NotEq (a,b) -> false, Ast.Function ("==",[Ast.Constant "_"; a; b])
;;

let trans_formulae = function
  | Ast.Disjunction _ -> assert false
  | Ast.Atom a -> trans_atom a
  | Ast.NegAtom _ -> assert false
;;


(* HELPERS *)
let resolve ~tptppath s = 
  let resolved_name = 
    if HExtlib.is_regular s then s else
    if tptppath = "/" then s else
    if Filename.check_suffix s ".p" then
     (assert (String.length s > 5);
     let prefix = String.sub s 0 3 in
     tptppath ^ "/Problems/" ^ prefix ^ "/" ^ s)
    else tptppath ^ "/" ^ s
  in
  if HExtlib.is_regular resolved_name then
    resolved_name
  else
    begin
      prerr_endline ("Unable to find " ^ s ^ " (" ^ resolved_name ^ ")");
      exit 1
    end
;;

(* MAIN *)
let parse ~tptppath filename =
  let rec aux = function
    | [] -> []
    | (Ast.Inclusion (file,_)) :: tl ->
        let file = resolve ~tptppath file in
        let lexbuf = Lexing.from_channel (open_in file) in
        let statements = Parser.main Lexer.yylex lexbuf in
        aux (statements @ tl)
    | hd::tl -> hd :: aux tl
  in
  let statements = aux [Ast.Inclusion (filename,[])] in
  let positives, negatives = 
    let rec aux p n = function
      | [] -> p,n
      | Ast.Comment _ :: tl -> aux p n tl
      | Ast.AnnotatedFormula (name, 
          (Ast.Axiom | Ast.Hypothesis|Ast.Negated_conjecture), f,_,_) :: tl->
          let is_positive, f = trans_formulae f in
          if is_positive then aux (p@[Ast.Constant name,f]) n tl
          else aux p (n@[Ast.Constant name,f]) tl
      | _ -> prerr_endline "bad syntax"; assert false
    in
      aux [] [] statements
  in
  positives, negatives
;;

