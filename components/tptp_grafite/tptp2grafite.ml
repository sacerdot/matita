module GA = GrafiteAst;;
module LA = LexiconAst;;
module PT = CicNotationPt;;
module A = Ast;;

type sort = Prop | Univ;;

let floc = HExtlib.dummy_floc;;


let paramod_timeout = ref 600;;
let depth = ref 10;;

let universe = "Univ" ;;
let prop = "Prop";;

let kw = [
 "and","myand"
];;

let mk_ident s =
  PT.Ident ((try List.assoc s kw with Not_found -> s),None)
;;

let rec collect_arities_from_term = function
  | A.Constant name -> [name,(0,Univ)]
  | A.Variable name -> [name,(0,Univ)]
  | A.Function (name,l) -> 
      (name,(List.length l,Univ))::
        List.flatten (List.map collect_arities_from_term l)
;;

let rec collect_fv_from_term = function
  | A.Constant name -> []
  | A.Variable name -> [name]
  | A.Function (_,l) -> 
      List.flatten (List.map collect_fv_from_term l)
;;

let collect_arities_from_atom a = 
  let aux = function
    | A.Proposition name -> [name,(0,Prop)]
    | A.Predicate (name,args) -> 
        (name,(List.length args,Prop)) :: 
          (List.flatten (List.map collect_arities_from_term args))
    | A.True -> []
    | A.False -> []
    | A.Eq (t1,t2) -> 
        collect_arities_from_term t1 @ collect_arities_from_term t2
    | A.NotEq (t1,t2) -> 
        collect_arities_from_term t1 @ collect_arities_from_term t2
  in
  HExtlib.list_uniq (List.sort compare (List.flatten (List.map aux a)))
;;
  
let collect_fv_from_atom a = 
  let aux = function
    | A.Proposition name -> [name] 
    | A.Predicate (name,args) -> 
        name :: List.flatten (List.map collect_fv_from_term args)
    | A.True -> []
    | A.False -> []
    | A.Eq (t1,t2) -> collect_fv_from_term t1 @ collect_fv_from_term t2
    | A.NotEq (t1,t2) -> collect_fv_from_term t1 @ collect_fv_from_term t2
  in
  let rec aux2 = function
    | [] -> []
    | hd::tl -> aux hd @ aux2 tl
  in
  HExtlib.list_uniq (List.sort compare (aux2 a))
;;  

let rec collect_fv_from_formulae = function
  | A.Disjunction (a,b) -> 
      collect_fv_from_formulae a @ collect_fv_from_formulae b
  | A.NegAtom a 
  | A.Atom a -> collect_fv_from_atom [a]
;;

let rec convert_term = function
  | A.Variable x -> mk_ident x
  | A.Constant x -> mk_ident x
  | A.Function (name, args) -> 
      PT.Appl (mk_ident name :: List.map convert_term args)
;;

let rec atom_of_formula neg pos = function
    | A.Disjunction (a,b) ->
        let neg, pos = atom_of_formula neg pos a in
        atom_of_formula neg pos b 
    | A.NegAtom a -> a::neg, pos 
    | A.Atom (A.NotEq (a,b)) -> (A.Eq (a,b) :: neg), pos
    | A.Atom a -> neg, a::pos
;;

let atom_of_formula f =
  let neg, pos = atom_of_formula [] [] f in
  neg @ pos
;;
  
let rec mk_arrow component tail = function
  | 0 -> begin
      match tail with
      | Prop -> mk_ident prop
      | Univ -> mk_ident universe
      end
  | n -> 
      PT.Binder 
        (`Forall,
          ((mk_ident "_"),Some (mk_ident component)),
          mk_arrow component tail (n-1))
;;

let build_ctx_for_arities univesally arities t = 
  let binder = if univesally then `Forall else `Exists in
  let rec aux = function
    | [] -> t
    | (name,(nargs,sort))::tl ->
        PT.Binder 
          (binder,
            (mk_ident name,Some (mk_arrow universe sort nargs)),
            aux tl)
  in
  aux arities
;;

let convert_atom universally a = 
  let aux = function
  | A.Proposition p -> mk_ident p
  | A.Predicate (name,params) -> 
      PT.Appl ((mk_ident name) :: (List.map convert_term params))
  | A.True -> mk_ident "True"
  | A.False -> mk_ident "False"
  | A.Eq (l,r)
  | A.NotEq (l,r) -> (* removes the negation *)
      PT.Appl [mk_ident "eq";mk_ident universe;convert_term l;convert_term r]
  in
  let rec aux2 = function
    | [] -> assert false
    | [x] -> aux x
    | he::tl -> 
        if universally then 
          PT.Binder (`Forall, (mk_ident "_", Some (aux he)), aux2 tl)
        else
          PT.Appl [mk_ident "And";aux he;aux2 tl]
  in
  let arities = collect_arities_from_atom a in
  let fv = collect_fv_from_atom a in
  build_ctx_for_arities universally 
    (List.filter 
      (function (x,(0,Univ)) -> List.mem x fv | _-> false) 
      arities) 
    (aux2 a)
;;

let collect_arities atom ctx = 
  let atoms = atom@(List.flatten (List.map atom_of_formula ctx)) in
  collect_arities_from_atom atoms
;;

let collect_arities_from_formulae f =
  let rec collect_arities_from_formulae = function
  | A.Disjunction (a,b) -> 
      collect_arities_from_formulae a @ collect_arities_from_formulae b
  | A.NegAtom a 
  | A.Atom a -> collect_arities_from_atom [a]
  in
  HExtlib.list_uniq (List.sort compare (collect_arities_from_formulae f))
;;

let is_formulae_1eq_negated f =
  let atom = atom_of_formula f in
  match atom with
  | [A.NotEq (l,r)] -> true
  | _ -> false
;;  

let collect_fv_1stord_from_formulae f =
  let arities = collect_arities_from_formulae f in
  let fv = collect_fv_from_formulae f in
  List.map fst 
    (List.filter (function (x,(0,Univ)) -> List.mem x fv | _-> false) arities)
;;

let rec convert_formula fv no_arities context f =
  let atom = atom_of_formula f in
  let t = convert_atom (fv = []) atom in
  let rec build_ctx n = function
    | [] -> t
    | hp::tl -> 
        PT.Binder 
          (`Forall,
            (mk_ident ("H" ^ string_of_int n), 
              Some (convert_formula [] true [] hp)), 
            build_ctx (n+1) tl)
  in
  let arities = if no_arities then [] else collect_arities atom context in
  build_ctx_for_arities true arities (build_ctx 0 context) 
;;

let check_if_atom_is_negative = function
  | A.True -> false
  | A.False -> true
  | A.Proposition _ -> false
  | A.Predicate _ -> false
  | A.Eq _ -> false
  | A.NotEq _ -> true
;;

let rec check_if_formula_is_negative = function
  | A.Disjunction (a,b) ->
      check_if_formula_is_negative a && check_if_formula_is_negative b
  | A.NegAtom a -> not (check_if_atom_is_negative a)
  | A.Atom a -> check_if_atom_is_negative a
;;

let ng_generate_tactics fv ueq_case context arities =
  [ GA.Executable(floc,GA.NTactic(floc, 
     [GA.NIntro (floc,"Univ") ; GA.NDot(floc)])) ]
  @      
  (HExtlib.list_mapi
   (fun (name,_) _-> 
     GA.Executable(floc,GA.NTactic(floc, 
      [GA.NIntro (floc,(try List.assoc name kw with Not_found -> name));
       GA.NDot(floc)])))
   arities)
  @
  (HExtlib.list_mapi
   (fun _ i-> 
     GA.Executable(floc,GA.NTactic(floc, 
      [GA.NIntro (floc,"H"^string_of_int i);GA.NDot(floc)])))
   context)
  @
(if fv <> [] then     
  (List.flatten
    (List.map 
      (fun _ -> 
        [GA.Executable(floc,GA.NTactic(floc, 
          [GA.NApply (floc,
            PT.Appl
             [mk_ident "ex_intro";PT.Implicit `JustOne;PT.Implicit `JustOne;
              PT.Implicit `JustOne;PT.Implicit `JustOne]);GA.NBranch floc]));
         GA.Executable(floc,GA.NTactic(floc, 
          [GA.NPos (floc,[2])]))])
      fv)) 
 else [])@
  [GA.Executable(floc,GA.NTactic(floc, [
    if (*ueq_case*) true then
        GA.NAuto (floc,(Some 
          HExtlib.list_mapi 
            (fun _ i -> 
               mk_ident ("H" ^ string_of_int i)) 
            context    
                ,[]))
    else
        GA.NAuto (floc,(None,[
                "depth",string_of_int 5;
                "width",string_of_int 5;
                "size",string_of_int 20;
                "timeout",string_of_int 10;
        ]))
 ;
  GA.NSemicolon(floc)]));
(*
  GA.Executable(floc,GA.NTactic(floc, Some (GA.Try(floc,
    GA.Assumption floc)), GA.Dot(floc)))
*)
  ]@
(if fv <> [] then     
  (List.flatten
    (List.map 
      (fun _ -> 
              [GA.Executable(floc,GA.NTactic(floc, [GA.NShift floc;
               GA.NSkip floc; GA.NMerge floc]))])
      fv)) 
 else [])@
    [GA.Executable(floc,GA.NTactic(floc,[GA.NTry(floc, GA.NAssumption(floc));
					 GA.NSemicolon(floc)]))]@
  [GA.Executable(floc,GA.NCommand(floc, GA.NQed(floc)))]
;;

let generate_tactics fv ueq_case =
  [GA.Executable(floc,GA.Tactic(floc, Some
   (GA.Intros (floc,(None,[]))),GA.Dot(floc)))] @
(if fv <> [] then     
  (List.flatten
    (List.map 
      (fun _ -> 
        [GA.Executable(floc,GA.Tactic(floc, Some
          (GA.Exists floc),GA.Branch floc));
         GA.Executable(floc,GA.Tactic(floc, None,
          (GA.Pos (floc,[2]))))])
      fv)) 
 else [])@
  [GA.Executable(floc,GA.Tactic(floc, Some (
    if true (*ueq_case*) then
        GA.AutoBatch (floc,(None,["paramodulation","";
        "timeout",string_of_int !paramod_timeout]))
    else
        GA.AutoBatch (floc,(None,[
                "depth",string_of_int 5;
                "width",string_of_int 5;
                "size",string_of_int 20;
                "timeout",string_of_int 10;
        ]))
  ),
    GA.Semicolon(floc)));
  GA.Executable(floc,GA.Tactic(floc, Some (GA.Try(floc,
    GA.Assumption floc)), GA.Dot(floc)))
  ]@
(if fv <> [] then     
  (List.flatten
    (List.map 
      (fun _ -> 
        [GA.Executable(floc,GA.Tactic(floc, None, GA.Shift floc));
         GA.Executable(floc,GA.NonPunctuationTactical(floc, GA.Skip floc,
         (GA.Merge floc)))])
      fv)) 
 else [])@
  [GA.Executable(floc,GA.Command(floc, GA.Print(floc,"proofterm")));
   GA.Executable(floc,GA.Command(floc, GA.Qed(floc)))]
;;

let convert_ast ng statements context = function
  | A.Comment s -> 
      let s = String.sub s 1 (String.length s - 1) in
      let s = 
        if s.[String.length s - 1] = '\n' then
          String.sub s 0 (String.length s - 1)
        else 
          s
      in
      statements @ [GA.Comment (floc,GA.Note (floc,s))],
      context
  | A.Inclusion (s,_) ->
      statements @ [
        GA.Comment (
          floc, GA.Note (
            floc,"Inclusion of: " ^ s))], context
  | A.AnnotatedFormula (name,kind,f,_,_) -> 
      match kind with
      | A.Axiom 
      | A.Hypothesis ->
          statements, f::context
      | A.Negated_conjecture when not (check_if_formula_is_negative f) ->
          statements, f::context
      | A.Negated_conjecture ->
          let ueq_case = is_formulae_1eq_negated f in
          let fv = collect_fv_1stord_from_formulae f in 
          let old_f = f in
          let f = 
            PT.Binder 
             (`Forall,
               (mk_ident universe,Some (PT.Sort (`Type (CicUniv.fresh ())))), 
               convert_formula fv false context f)
          in
          let o = PT.Theorem (`Theorem,name,f,None,`Regular) in
          (statements @ 
          [ GA.Executable(floc,GA.Command(floc,
             (*if ng then GA.NObj (floc,o) else*) GA.Obj(floc,o))); ] @
          if ng then 
            ng_generate_tactics fv ueq_case context
              (let atom = atom_of_formula old_f in collect_arities atom context)
          else generate_tactics fv ueq_case),
          context
      | A.Definition 
      | A.Lemma 
      | A.Theorem 
      | A.Conjecture
      | A.Lemma_conjecture 
      | A.Plain 
      | A.Unknown -> assert false
;;

(* HELPERS *)
let resolve ~tptppath s = 
  let resolved_name = 
    if Filename.check_suffix s ".p" then
      (assert (String.length s > 5);
      let prefix = String.sub s 0 3 in
      tptppath ^ "/Problems/" ^ prefix ^ "/" ^ s)
    else
      tptppath ^ "/" ^ s
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
let tptp2grafite ?(timeout=600) ?(def_depth=10) ?raw_preamble ~tptppath ~filename ~ng () =
  paramod_timeout := timeout;
  depth := def_depth;
  let rec aux = function
    | [] -> []
    | ((A.Inclusion (file,_)) as hd) :: tl ->
        let file = resolve ~tptppath file in
        let lexbuf = Lexing.from_channel (open_in file) in
        let statements = Parser.main Lexer.yylex lexbuf in
        hd :: aux (statements @ tl)
    | hd::tl -> hd :: aux tl
  in
  let statements = aux [A.Inclusion (filename,[])] in
  let grafite_ast_statements,_ = 
    List.fold_left 
      (fun (st, ctx) f -> 
        let newst, ctx = convert_ast ng st ctx f in
        newst, ctx)
      ([],[]) statements 
  in
  let pp t = 
    (* ZACK: setting width to 80 will trigger a bug of BoxPp.render_to_string
     * which will show up using the following command line:
     * ./tptp2grafite -tptppath ~tassi/TPTP-v3.1.1 GRP170-1 *)
    let width = max_int in
    let term_pp prec content_term =
      let pres_term = TermContentPres.pp_ast content_term in
      let lookup_uri = fun _ -> None in
      let markup = CicNotationPres.render ~lookup_uri ~prec pres_term in
      let s = BoxPp.render_to_string List.hd width markup ~map_unicode_to_tex:false in
      Pcre.substitute 
       ~rex:(Pcre.regexp ~flags:[`UTF8] "∀[Ha-z][a-z0-9_]*") ~subst:(fun x -> "\n" ^ x) 
       s
    in
    CicNotationPp.set_pp_term (term_pp 90);
    let lazy_term_pp = fun x -> assert false in
    let obj_pp = CicNotationPp.pp_obj CicNotationPp.pp_term in
    Pcre.replace ~pat:"theorem" ~templ:"ntheorem" 
     (GrafiteAstPp.pp_statement
       ~map_unicode_to_tex:false ~term_pp:(term_pp 19) ~lazy_term_pp ~obj_pp t)
  in
  let buri = Pcre.replace ~pat:"\\.p$" ("cic:/matita/TPTP/" ^ filename) in
  let extra_statements_start = [
    (*GA.Executable(floc,GA.Command(floc,
    GA.Set(floc,"baseuri",buri)))*)]
  in
  let preamble = 
    match raw_preamble with
    | None -> 
      pp
       (GA.Executable(floc,
         GA.Command(floc,GA.Include(floc,true,`OldAndNew,"logic/equality.ma"))))
    | Some s -> s buri
  in
  let extra_statements_end = [] in
  let aliases = []
   (*[("eq","cic:/Coq/Init/Logic/eq.ind#xpointer(1/1)");
   ("trans_eq","cic:/Coq/Init/Logic/trans_eq.con");
   ("eq_ind_r","cic:/Coq/Init/Logic/eq_ind_r.con");
   ("eq_ind","cic:/Coq/Init/Logic/eq_ind.con");
   ("sym_eq","cic:/Coq/Init/Logic/sym_eq.con");
   ("refl_equal","cic:/Coq/Init/Logic/eq.ind#xpointer(1/1/1)")] *)
  in
  let s1 = List.map pp extra_statements_start in
  let s2 = 
    List.map 
     (fun (n,s) -> 
       LexiconAstPp.pp_command (LA.Alias(floc, LA.Ident_alias(n,s))) ^ ".")
     aliases
  in
  let s3 = List.map pp grafite_ast_statements in
  let s4 = List.map pp extra_statements_end in
  String.concat "\n" (s1@[preamble]@s2@s3@s4)
;;
