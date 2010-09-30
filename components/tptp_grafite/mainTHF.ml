module T = CicNotationPt
module GA = GrafiteAst
module A = AstTHF

let floc = HExtlib.dummy_floc;;

(* OPTIONS *)
let tptppath = ref "./";;
let ng = ref false;;
let spec = [
  ("-ng",Arg.Set ng,"Matita ng syntax");
  ("-tptppath", 
      Arg.String (fun x -> tptppath := x), 
      "Where to find the Axioms/ and Problems/ directory")
]

let resolve ~tptppath s = 
  if s.[0] = '/' then s else
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


let find_related id =
  HExtlib.filter_map_monad 
    (fun acc -> function 
      | A.ThfDefinition (_,did,dbody) when did = id -> Some dbody, None
      | A.ThfType (_,did,dtype) when did = id -> Some dtype, None
      | x -> acc, Some x)
;;

(* MAIN *)
let _ =
  let usage = "Usage: tptpTHF2grafite [options] file" in
  let inputfile = ref "" in
  Arg.parse spec (fun s -> inputfile := s) usage;
  if !inputfile = "" then 
    begin
      prerr_endline usage;
      exit 1
    end;
  let tptppath = !tptppath in
  let statements = 
    let rec aux = function
      | [] -> []
      | ((A.Inclusion (file,_)) as hd) :: tl ->
          let file = resolve ~tptppath file in
          let lexbuf = Lexing.from_channel (open_in file) in
          let statements = ParserTHF.main LexerTHF.yylex lexbuf in
          hd :: aux (statements @ tl)
      | hd::tl -> hd :: aux tl
    in
     aux [A.Inclusion (!inputfile,[])] 
  in
  let statements = 
    let rec aux = function
      | [] -> []
      | A.Comment s :: tl -> 
         let s = Pcre.replace ~pat:"\n" ~templ:"" s in
         let s = Pcre.replace ~pat:"\\*\\)" ~templ:"" s in
         GA.Comment (floc,GA.Note (floc,s)) :: aux tl
      | A.Inclusion (s,_) :: tl -> 
        GA.Comment (
          floc, GA.Note (
            floc,"Inclusion of: " ^ s)) :: aux tl
      | A.ThfType(name,id,ty) :: tl -> 
         let body, tl = find_related id None tl in
         let what = match body with None -> `Axiom | _ -> `Definition in
         GA.Executable(floc,
          GA.NCommand(floc,
           GA.NObj(floc,
            T.Theorem(what, id,ty,body,`Regular)))) :: aux tl
      | A.ThfDefinition(name,id,body) :: tl -> 
         let ty, tl = find_related id None tl in
         let ty = match ty with Some x -> x | None -> T.Implicit `JustOne in
         GA.Executable(floc,
          GA.NCommand(floc,
           GA.NObj(floc,
            T.Theorem(`Definition,
             id,ty,Some body,`Regular)))):: aux tl
      | A.ThfFormula(name,(A.Axiom|A.Hypothesis|A.Assumption),term) :: tl -> 
         GA.Executable(floc,
          GA.NCommand(floc,
           GA.NObj(floc,
            T.Theorem(`Axiom, name,term,None,`Regular)))):: aux tl
      | A.ThfFormula(name,A.Conjecture,term) :: tl -> 
         GA.Executable(floc,
          GA.NCommand(floc,
           GA.NObj(floc,
            T.Theorem(`Theorem, name,
             term,None,`Regular)))):: aux tl
      | A.ThfFormula _ :: tl -> assert false
    in
      aux statements
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
    Pcre.replace ~pat:"^theorem" ~templ:"ntheorem" 
    (Pcre.replace ~pat:"^axiom" ~templ:"naxiom" 
    (Pcre.replace ~pat:"^definition" ~templ:"ndefinition" 
    (Pcre.replace ~pat:"Type \\\\sub ([0-9]+)" ~templ:"Type[$1]" 
     (GrafiteAstPp.pp_statement
       ~map_unicode_to_tex:false 
         ~term_pp:(term_pp 19) ~lazy_term_pp ~obj_pp t))))
  in
  print_endline (pp (GA.Executable (floc,
    GA.Command(floc,GA.Include(floc,true,`OldAndNew,"TPTP.ma")))));
  List.iter (fun x -> print_endline (pp x)) statements;
  exit 0

