(* Copyright (C) 2005, HELM Team.
 * 
 * This file is part of HELM, an Hypertextual, Electronic
 * Library of Mathematics, developed at the Computer Science
 * Department, University of Bologna, Italy.
 * 
 * HELM is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or (at your option) any later version.
 * 
 * HELM is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with HELM; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place - Suite 330, Boston,
 * MA  02111-1307, USA.
 * 
 * For details, see the HELM World-Wide-Web page,
 * http://helm.cs.unibo.it/
 *)

(* $Id$ *)

module N  = NotationPt
module G  = GrafiteAst
module L  = LexiconAst
module LE = LexiconEngine

exception NoInclusionPerformed of string (* full path *)

type 'a localized_option =
   LSome of 'a
 | LNone of G.loc

type ast_statement = G.statement

type 'status statement =
  ?never_include:bool -> 
    (* do not call LexiconEngine to do includes, always raise NoInclusionPerformed *) 
  include_paths:string list -> (#LE.status as 'status) ->
    'status * ast_statement localized_option

type 'status parser_status = {
  grammar : Grammar.g;
  term : N.term Grammar.Entry.e;
  statement : #LE.status as 'status statement Grammar.Entry.e;
}

let grafite_callback = ref (fun _ -> ())
let set_grafite_callback cb = grafite_callback := cb

let lexicon_callback = ref (fun _ -> ())
let set_lexicon_callback cb = lexicon_callback := cb

let initial_parser () = 
  let grammar = CicNotationParser.level2_ast_grammar () in
  let term = CicNotationParser.term () in
  let statement = Grammar.Entry.create grammar "statement" in
  { grammar = grammar; term = term; statement = statement }
;;

let grafite_parser = ref (initial_parser ())

let add_raw_attribute ~text t = N.AttributedTerm (`Raw text, t)

let default_associativity = Gramext.NonA
        
let mk_rec_corec ind_kind defs loc = 
  let name,ty = 
    match defs with
    | (params,(N.Ident (name, None), ty),_,_) :: _ ->
        let ty = match ty with Some ty -> ty | None -> N.Implicit `JustOne in
        let ty =
         List.fold_right
          (fun var ty -> N.Binder (`Pi,var,ty)
          ) params ty
        in
         name,ty
    | _ -> assert false 
  in
  let body = N.Ident (name,None) in
   (loc, N.Theorem(`Definition, name, ty, Some (N.LetRec (ind_kind, defs, body)), `Regular))

let nmk_rec_corec ind_kind defs loc = 
 let loc,t = mk_rec_corec ind_kind defs loc in
  G.NObj (loc,t)

(*
let nnon_punct_of_punct = function
  | G.Skip loc -> G.NSkip loc
  | G.Unfocus loc -> G.NUnfocus loc
  | G.Focus (loc,l) -> G.NFocus (loc,l)
;; *)

type by_continuation =
   BYC_done
 | BYC_weproved of N.term * string option * N.term option
 | BYC_letsuchthat of string * N.term * string * N.term
 | BYC_wehaveand of string * N.term * string * N.term

let initialize_parser () =
  (* {{{ parser initialization *)
  let term = !grafite_parser.term in
  let statement = !grafite_parser.statement in
  let let_defs = CicNotationParser.let_defs () in
  let protected_binder_vars = CicNotationParser.protected_binder_vars () in
EXTEND
  GLOBAL: term statement;
  constructor: [ [ name = IDENT; SYMBOL ":"; typ = term -> (name, typ) ] ];
  tactic_term: [ [ t = term LEVEL "90" -> t ] ];
  new_name: [
    [ SYMBOL "_" -> None
    | id = IDENT -> Some id ]
    ];
  ident_list0: [ [ LPAREN; idents = LIST0 new_name; RPAREN -> idents ] ];
  ident_list1: [ [ LPAREN; idents = LIST1 IDENT; RPAREN -> idents ] ];
  tactic_term_list1: [
    [ tactic_terms = LIST1 tactic_term SEP SYMBOL "," -> tactic_terms ]
  ];
  reduction_kind: [
    [ IDENT "normalize" -> `Normalize
    | IDENT "simplify" -> `Simpl
    | IDENT "unfold"; t = OPT tactic_term -> `Unfold t
    | IDENT "whd" -> `Whd ]
  ];
  nreduction_kind: [
    [ IDENT "normalize" ; delta = OPT [ IDENT "nodelta" -> () ] ->
       let delta = match delta with None -> true | _ -> false in
        `Normalize delta
    (*| IDENT "unfold"; t = OPT tactic_term -> `Unfold t*)
    | IDENT "whd" ; delta = OPT [ IDENT "nodelta" -> () ] ->
       let delta = match delta with None -> true | _ -> false in
        `Whd delta]
  ];
  sequent_pattern_spec: [
   [ hyp_paths =
      LIST0
       [ id = IDENT ;
         path = OPT [SYMBOL ":" ; path = tactic_term -> path ] ->
         (id,match path with Some p -> p | None -> N.UserInput) ];
     goal_path = OPT [ SYMBOL <:unicode<vdash>>; term = tactic_term -> term ] ->
      let goal_path =
       match goal_path, hyp_paths with
          None, [] -> Some N.UserInput
        | None, _::_ -> None
        | Some goal_path, _ -> Some goal_path
      in
       hyp_paths,goal_path
   ]
  ];
  pattern_spec: [
    [ res = OPT [
       "in";
       wanted_and_sps =
        [ "match" ; wanted = tactic_term ;
          sps = OPT [ "in"; sps = sequent_pattern_spec -> sps ] ->
           Some wanted,sps
        | sps = sequent_pattern_spec ->
           None,Some sps
        ] ->
         let wanted,hyp_paths,goal_path =
          match wanted_and_sps with
             wanted,None -> wanted, [], Some N.UserInput
           | wanted,Some (hyp_paths,goal_path) -> wanted,hyp_paths,goal_path
         in
          wanted, hyp_paths, goal_path ] ->
      match res with
         None -> None,[],Some N.UserInput
       | Some ps -> ps]
  ];
  inverter_param_list: [ 
    [ params = tactic_term -> 
      let deannotate = function
        | N.AttributedTerm (_,t) | t -> t
      in match deannotate params with
      | N.Implicit _ -> [false]
      | N.UserInput -> [true]
      | N.Appl l -> 
         List.map (fun x -> match deannotate x with  
           | N.Implicit _ -> false
           | N.UserInput -> true
           | _ -> raise (Invalid_argument "malformed target parameter list 1")) l
      | _ -> raise (Invalid_argument ("malformed target parameter list 2\n" ^ NotationPp.pp_term params)) ]
  ];
  direction: [
    [ SYMBOL ">" -> `LeftToRight
    | SYMBOL "<" -> `RightToLeft ]
  ];
  int: [ [ num = NUMBER -> int_of_string num ] ];
  intros_names: [
   [ idents = OPT ident_list0 ->
      match idents with None -> [] | Some idents -> idents
   ]
  ];
  intros_spec: [
    [ OPT [ IDENT "names" ]; 
      num = OPT [ num = int -> num ]; 
      idents = intros_names ->
        num, idents
    ]
  ];
  using: [ [ using = OPT [ IDENT "using"; t = tactic_term -> t ] -> using ] ];
  ntactic: [
    [ SYMBOL "@"; t = tactic_term -> G.NTactic(loc,[G.NApply (loc, t)])
    | IDENT "apply"; t = tactic_term -> G.NTactic(loc,[G.NApply (loc, t)])
    | IDENT "applyS"; t = tactic_term -> G.NTactic(loc,[G.NSmartApply(loc, t)])
    | IDENT "assert";
       seqs = LIST0 [
        hyps = LIST0
         [ id = IDENT ; SYMBOL ":" ; ty = tactic_term -> id,`Decl ty
         | id = IDENT ; SYMBOL ":" ; ty = tactic_term ;
                        SYMBOL <:unicode<def>> ; bo = tactic_term ->
            id,`Def (bo,ty)];
        SYMBOL <:unicode<vdash>>;
        concl = tactic_term -> (List.rev hyps,concl) ] ->
         G.NTactic(loc,[G.NAssert (loc, seqs)])
    | IDENT "auto"; params = auto_params -> 
        G.NTactic(loc,[G.NAuto (loc, params)])
    | SYMBOL "/"; num = OPT NUMBER ; 
       params = nauto_params; SYMBOL "/" ; 
       just = OPT [ IDENT "by"; by = 
         [ univ = tactic_term_list1 -> `Univ univ
         | SYMBOL "{"; SYMBOL "}" -> `EmptyUniv
         | SYMBOL "_" -> `Trace ] -> by ] ->
       let depth = match num with Some n -> n | None -> "1" in
       (match just with
       | None -> 
	   G.NTactic(loc,
            [G.NAuto(loc,(None,["slir","";"depth",depth]@params))])
       | Some (`Univ univ) ->
	   G.NTactic(loc,
            [G.NAuto(loc,(Some univ,["slir","";"depth",depth]@params))])
       | Some `EmptyUniv ->
	   G.NTactic(loc,
            [G.NAuto(loc,(Some [],["slir","";"depth",depth]@params))])
       | Some `Trace ->
	   G.NMacro(loc,
             G.NAutoInteractive (loc, (None,["slir","";"depth",depth]@params))))
    | IDENT "intros" -> G.NMacro (loc, G.NIntroGuess loc)
    | IDENT "check"; t = term -> G.NMacro(loc,G.NCheck (loc,t))
    | IDENT "screenshot"; fname = QSTRING -> 
        G.NMacro(loc,G.Screenshot (loc, fname))
    | IDENT "cases"; what = tactic_term ; where = pattern_spec ->
        G.NTactic(loc,[G.NCases (loc, what, where)])
    | IDENT "change"; what = pattern_spec; "with"; with_what = tactic_term -> 
        G.NTactic(loc,[G.NChange (loc, what, with_what)])
    | SYMBOL "@"; num = OPT NUMBER; l = LIST0 tactic_term -> 
        G.NTactic(loc,[G.NConstructor (loc, (match num with None -> None | Some x -> Some (int_of_string x)),l)])
    | IDENT "cut"; t = tactic_term -> G.NTactic(loc,[G.NCut (loc, t)])
(*  | IDENT "discriminate"; t = tactic_term -> G.NDiscriminate (loc, t)
    | IDENT "subst"; t = tactic_term -> G.NSubst (loc, t) *)
    | IDENT "destruct"; just = OPT [ dom = ident_list1 -> dom ];
      exclude = OPT [ IDENT "skip"; skip = ident_list1 -> skip ]
        -> let exclude' = match exclude with None -> [] | Some l -> l in
           G.NTactic(loc,[G.NDestruct (loc,just,exclude')])
    | IDENT "elim"; what = tactic_term ; where = pattern_spec ->
        G.NTactic(loc,[G.NElim (loc, what, where)])
    | IDENT "generalize"; p=pattern_spec ->
        G.NTactic(loc,[G.NGeneralize (loc, p)])
    | IDENT "inversion"; what = tactic_term ; where = pattern_spec ->
        G.NTactic(loc,[G.NInversion (loc, what, where)])
    | IDENT "lapply"; t = tactic_term -> G.NTactic(loc,[G.NLApply (loc, t)])
    | IDENT "letin"; name = IDENT ; SYMBOL <:unicode<def>> ; t = tactic_term;
        where = pattern_spec ->
        G.NTactic(loc,[G.NLetIn (loc,where,t,name)])
    | kind = nreduction_kind; p = pattern_spec ->
        G.NTactic(loc,[G.NReduce (loc, kind, p)])
    | dir = direction; what = tactic_term ; where = pattern_spec ->	
        G.NTactic(loc,[G.NRewrite (loc, dir, what, where)])
    | IDENT "rewrite"; dir = direction; what = tactic_term ; where = pattern_spec ->	
        G.NTactic(loc,[G.NRewrite (loc, dir, what, where)])
    | IDENT "try"; tac = SELF -> 
        let tac = match tac with G.NTactic(_,[t]) -> t | _ -> assert false in
        G.NTactic(loc,[ G.NTry (loc,tac)])
    | IDENT "repeat"; tac = SELF -> 
        let tac = match tac with G.NTactic(_,[t]) -> t | _ -> assert false in
        G.NTactic(loc,[ G.NRepeat (loc,tac)])
    | LPAREN; l = LIST1 SELF; RPAREN -> 
        let l = 
          List.flatten 
            (List.map (function G.NTactic(_,t) -> t | _ -> assert false) l) in
        G.NTactic(loc,[G.NBlock (loc,l)])
    | IDENT "assumption" -> G.NTactic(loc,[ G.NAssumption loc])
    | SYMBOL "#"; ns=IDENT -> G.NTactic(loc,[ G.NIntros (loc,[ns])])
    | SYMBOL "#"; SYMBOL "_" -> G.NTactic(loc,[ G.NIntro (loc,"_")])
    | SYMBOL "*" -> G.NTactic(loc,[ G.NCase1 (loc,"_")])
    | SYMBOL "*"; n=IDENT -> G.NTactic(loc,[ G.NCase1 (loc,n)])
    ]
  ];
  auto_fixed_param: [
   [ IDENT "demod"
   | IDENT "fast_paramod"
   | IDENT "paramod"
   | IDENT "depth"
   | IDENT "width"
   | IDENT "size"
   | IDENT "timeout"
   | IDENT "library"
   | IDENT "type"
   | IDENT "all"
   ]
];
  auto_params: [
    [ params = 
      LIST0 [
         i = auto_fixed_param -> i,""
       | i = auto_fixed_param ; SYMBOL "="; v = [ v = int ->
              string_of_int v | v = IDENT -> v ] -> i,v ]; 
      tl = OPT [ IDENT "by"; tl = tactic_term_list1 -> tl] -> tl,
      (* (match tl with Some l -> l | None -> []), *)
      params
   ]
];
  nauto_params: [
    [ params = 
      LIST0 [
         i = auto_fixed_param -> i,""
       | i = auto_fixed_param ; SYMBOL "="; v = [ v = int ->
              string_of_int v | v = IDENT -> v ] -> i,v ] ->
      params
   ]
];

  by_continuation: [
    [ WEPROVED; ty = tactic_term ; LPAREN ; id = IDENT ; RPAREN ; t1 = OPT [IDENT "that" ; IDENT "is" ; IDENT "equivalent" ; "to" ; t2 = tactic_term -> t2] -> BYC_weproved (ty,Some id,t1)
    | WEPROVED; ty = tactic_term ; t1 = OPT [IDENT "that" ; IDENT "is" ; IDENT "equivalent" ; "to" ; t2 = tactic_term -> t2] ; 
            "done" -> BYC_weproved (ty,None,t1)
    | "done" -> BYC_done
    | "let" ; id1 = IDENT ; SYMBOL ":" ; t1 = tactic_term ;
      IDENT "such" ; IDENT "that" ; t2=tactic_term ; LPAREN ; 
      id2 = IDENT ; RPAREN -> BYC_letsuchthat (id1,t1,id2,t2)
    | WEHAVE; t1=tactic_term ; LPAREN ; id1=IDENT ; RPAREN ;"and" ; t2=tactic_term ; LPAREN ; id2=IDENT ; RPAREN ->
              BYC_wehaveand (id1,t1,id2,t2)
    ]
];
  rewriting_step_continuation : [
    [ "done" -> true
    | -> false
    ]
];
(* MATITA 1.0
  atomic_tactical:
    [ "sequence" LEFTA
      [ t1 = SELF; SYMBOL ";"; t2 = SELF ->
          let ts =
            match t1 with
            | G.Seq (_, l) -> l @ [ t2 ]
            | _ -> [ t1; t2 ]
          in
          G.Seq (loc, ts)
      ]
    | "then" NONA
      [ tac = SELF; SYMBOL ";";
        SYMBOL "["; tacs = LIST0 SELF SEP SYMBOL "|"; SYMBOL "]"->
          (G.Then (loc, tac, tacs))
      ]
    | "loops" RIGHTA
      [ IDENT "do"; count = int; tac = SELF ->
          G.Do (loc, count, tac)
      | IDENT "repeat"; tac = SELF -> G.Repeat (loc, tac)
      ]
    | "simple" NONA
      [ IDENT "first";
        SYMBOL "["; tacs = LIST0 SELF SEP SYMBOL "|"; SYMBOL "]"->
          G.First (loc, tacs)
      | IDENT "try"; tac = SELF -> G.Try (loc, tac)
      | IDENT "solve";
        SYMBOL "["; tacs = LIST0 SELF SEP SYMBOL "|"; SYMBOL "]"->
          G.Solve (loc, tacs)
      | IDENT "progress"; tac = SELF -> G.Progress (loc, tac)
      | LPAREN; tac = SELF; RPAREN -> tac
      | tac = tactic -> tac
        ]
      ];
*)
  npunctuation_tactical:
    [
      [ SYMBOL "[" -> G.NBranch loc
      | SYMBOL "|" -> G.NShift loc
      | i = LIST1 int SEP SYMBOL ","; SYMBOL ":" -> G.NPos (loc, i)
      | SYMBOL "*"; SYMBOL ":" -> G.NWildcard loc
      | name = IDENT; SYMBOL ":" -> G.NPosbyname (loc, name)
      | SYMBOL "]" -> G.NMerge loc
      | SYMBOL ";" -> G.NSemicolon loc
      | SYMBOL "." -> G.NDot loc
      ]
    ];
  nnon_punctuation_tactical:
    [ "simple" NONA
      [ IDENT "focus"; goals = LIST1 int -> G.NFocus (loc, goals)
      | IDENT "unfocus" -> G.NUnfocus loc
      | IDENT "skip" -> G.NSkip loc
      ]
      ];
  ntheorem_flavour: [
    [ [ IDENT "definition"  ] -> `Definition
    | [ IDENT "fact"        ] -> `Fact
    | [ IDENT "lemma"       ] -> `Lemma
    | [ IDENT "example"     ] -> `Example
    | [ IDENT "theorem"     ] -> `Theorem
    | [ IDENT "corollary"   ] -> `Corollary
    ]
  ];
  inductive_spec: [ [
    fst_name = IDENT; 
      params = LIST0 protected_binder_vars;
    SYMBOL ":"; fst_typ = term; SYMBOL <:unicode<def>>; OPT SYMBOL "|";
    fst_constructors = LIST0 constructor SEP SYMBOL "|";
    tl = OPT [ "with";
        types = LIST1 [
          name = IDENT; SYMBOL ":"; typ = term; SYMBOL <:unicode<def>>;
         OPT SYMBOL "|"; constructors = LIST0 constructor SEP SYMBOL "|" ->
            (name, true, typ, constructors) ] SEP "with" -> types
      ] ->
        let params =
          List.fold_right
            (fun (names, typ) acc ->
              (List.map (fun name -> (name, typ)) names) @ acc)
            params []
        in
        let fst_ind_type = (fst_name, true, fst_typ, fst_constructors) in
        let tl_ind_types = match tl with None -> [] | Some types -> types in
        let ind_types = fst_ind_type :: tl_ind_types in
        (params, ind_types)
    ] ];
    
    record_spec: [ [
      name = IDENT; 
      params = LIST0 protected_binder_vars;
       SYMBOL ":"; typ = term; SYMBOL <:unicode<def>>; SYMBOL "{" ; 
       fields = LIST0 [ 
         name = IDENT ; 
         coercion = [ 
             SYMBOL ":" -> false,0 
           | SYMBOL ":"; SYMBOL ">" -> true,0
           | SYMBOL ":"; arity = int ; SYMBOL ">" -> true,arity
         ]; 
         ty = term -> 
           let b,n = coercion in 
           (name,ty,b,n) 
       ] SEP SYMBOL ";"; SYMBOL "}" -> 
        let params =
          List.fold_right
            (fun (names, typ) acc ->
              (List.map (fun name -> (name, typ)) names) @ acc)
            params []
        in
        (params,name,typ,fields)
    ] ];

    alias_spec: [
      [ IDENT "id"; id = QSTRING; SYMBOL "="; uri = QSTRING ->
        let alpha = "[a-zA-Z]" in
        let num = "[0-9]+" in
        let ident_cont = "\\("^alpha^"\\|"^num^"\\|_\\|\\\\\\)" in
        let decoration = "\\'" in
        let ident = "\\("^alpha^ident_cont^"*"^decoration^"*\\|_"^ident_cont^"+"^decoration^"*\\)" in
        let rex = Str.regexp ("^"^ident^"$") in
        if Str.string_match rex id 0 then
          if (try ignore (UriManager.uri_of_string uri); true
              with UriManager.IllFormedUri _ -> false) ||
             (try ignore (NReference.reference_of_string uri); true
              with NReference.IllFormedReference _ -> false)
          then
            L.Ident_alias (id, uri)
          else
            raise
             (HExtlib.Localized (loc, CicNotationParser.Parse_error (Printf.sprintf "Not a valid uri: %s" uri)))
        else
          raise (HExtlib.Localized (loc, CicNotationParser.Parse_error (
            Printf.sprintf "Not a valid identifier: %s" id)))
      | IDENT "symbol"; symbol = QSTRING;
        instance = OPT [ LPAREN; IDENT "instance"; n = int; RPAREN -> n ];
        SYMBOL "="; dsc = QSTRING ->
          let instance =
            match instance with Some i -> i | None -> 0
          in
          L.Symbol_alias (symbol, instance, dsc)
      | IDENT "num";
        instance = OPT [ LPAREN; IDENT "instance"; n = int; RPAREN -> n ];
        SYMBOL "="; dsc = QSTRING ->
          let instance =
            match instance with Some i -> i | None -> 0
          in
          L.Number_alias (instance, dsc)
      ]
     ];
    argument: [
      [ l = LIST0 [ SYMBOL <:unicode<eta>> (* η *); SYMBOL "." -> () ];
        id = IDENT ->
          N.IdentArg (List.length l, id)
      ]
    ];
    associativity: [
      [ IDENT "left";  IDENT "associative" -> Gramext.LeftA
      | IDENT "right"; IDENT "associative" -> Gramext.RightA
      | IDENT "non"; IDENT "associative" -> Gramext.NonA
      ]
    ];
    precedence: [
      [ "with"; IDENT "precedence"; n = NUMBER -> int_of_string n ]
    ];
    notation: [
      [ dir = OPT direction; s = QSTRING;
        assoc = OPT associativity; prec = precedence;
        IDENT "for";
        p2 = 
          [ blob = UNPARSED_AST ->
              add_raw_attribute ~text:(Printf.sprintf "@{%s}" blob)
                (CicNotationParser.parse_level2_ast
                  (Ulexing.from_utf8_string blob))
          | blob = UNPARSED_META ->
              add_raw_attribute ~text:(Printf.sprintf "${%s}" blob)
                (CicNotationParser.parse_level2_meta
                  (Ulexing.from_utf8_string blob))
          ] ->
            let assoc =
              match assoc with
              | None -> default_associativity
              | Some assoc -> assoc
            in
            let p1 =
              add_raw_attribute ~text:s
                (CicNotationParser.parse_level1_pattern prec
                  (Ulexing.from_utf8_string s))
            in
            (dir, p1, assoc, prec, p2)
      ]
    ];
    level3_term: [
      [ u = URI -> N.UriPattern (UriManager.uri_of_string u)
      | r = NREF -> N.NRefPattern (NReference.reference_of_string r)
      | IMPLICIT -> N.ImplicitPattern
      | id = IDENT -> N.VarPattern id
      | LPAREN; terms = LIST1 SELF; RPAREN ->
          (match terms with
          | [] -> assert false
          | [term] -> term
          | terms -> N.ApplPattern terms)
      ]
    ];
    interpretation: [
      [ s = CSYMBOL; args = LIST0 argument; SYMBOL "="; t = level3_term ->
          (s, args, t)
      ]
    ];
    
    include_command: [ [
        IDENT "include" ; path = QSTRING -> 
          loc,path,true,L.WithPreferences
      | IDENT "include" ; IDENT "source" ; path = QSTRING -> 
          loc,path,false,L.WithPreferences	  
      | IDENT "include'" ; path = QSTRING -> 
          loc,path,true,L.WithoutPreferences
     ]];

  grafite_ncommand: [ [
      IDENT "qed" -> G.NQed loc
    | nflavour = ntheorem_flavour; name = IDENT; SYMBOL ":"; typ = term;
      body = OPT [ SYMBOL <:unicode<def>> (* ≝ *); body = term -> body ] ->
        G.NObj (loc, N.Theorem (nflavour, name, typ, body,`Regular))
    | nflavour = ntheorem_flavour; name = IDENT; SYMBOL <:unicode<def>> (* ≝ *);
      body = term ->
        G.NObj (loc, N.Theorem (nflavour, name, N.Implicit `JustOne, Some body,`Regular))
    | IDENT "axiom"; name = IDENT; SYMBOL ":"; typ = term ->
        G.NObj (loc, N.Theorem (`Axiom, name, typ, None, `Regular))
    | IDENT "discriminator" ; indty = tactic_term -> G.NDiscriminator (loc,indty)
    | IDENT "inverter"; name = IDENT; IDENT "for" ; indty = tactic_term ;
      paramspec = OPT inverter_param_list ; 
      outsort = OPT [ SYMBOL ":" ; outsort = term -> outsort ] -> 
        G.NInverter (loc,name,indty,paramspec,outsort)
    | NLETCOREC ; defs = let_defs -> 
        nmk_rec_corec `CoInductive defs loc
    | NLETREC ; defs = let_defs -> 
        nmk_rec_corec `Inductive defs loc
    | IDENT "inductive"; spec = inductive_spec ->
        let (params, ind_types) = spec in
        G.NObj (loc, N.Inductive (params, ind_types))
    | IDENT "coinductive"; spec = inductive_spec ->
        let (params, ind_types) = spec in
        let ind_types = (* set inductive flags to false (coinductive) *)
          List.map (fun (name, _, term, ctors) -> (name, false, term, ctors))
            ind_types
        in
        G.NObj (loc, N.Inductive (params, ind_types))
    | IDENT "universe"; IDENT "constraint"; u1 = tactic_term; 
        SYMBOL <:unicode<lt>> ; u2 = tactic_term ->
        let urify = function 
          | NotationPt.AttributedTerm (_, NotationPt.Sort (`NType i)) ->
              NUri.uri_of_string ("cic:/matita/pts/Type"^i^".univ")
          | _ -> raise (Failure "only a Type[…] sort can be constrained")
        in
        let u1 = urify u1 in
        let u2 = urify u2 in
         G.NUnivConstraint (loc,u1,u2)
    | IDENT "unification"; IDENT "hint"; n = int; t = tactic_term ->
        G.UnificationHint (loc, t, n)
    | IDENT "coercion"; name = IDENT; SYMBOL ":"; ty = term; 
        SYMBOL <:unicode<def>>; t = term; "on"; 
        id = [ IDENT | PIDENT ]; SYMBOL ":"; source = term;
        "to"; target = term ->
          G.NCoercion(loc,name,t,ty,(id,source),target)     
    | IDENT "record" ; (params,name,ty,fields) = record_spec ->
        G.NObj (loc, N.Record (params,name,ty,fields))
    | IDENT "copy" ; s = IDENT; IDENT "from"; u = URI; "with"; 
      m = LIST0 [ u1 = URI; SYMBOL <:unicode<mapsto>>; u2 = URI -> u1,u2 ] ->
        G.NCopy (loc,s,NUri.uri_of_string u,
          List.map (fun a,b -> NUri.uri_of_string a, NUri.uri_of_string b) m)
  ]];

  lexicon_command: [ [
      IDENT "alias" ; spec = alias_spec ->
        L.Alias (loc, spec)
    | IDENT "notation"; (dir, l1, assoc, prec, l2) = notation ->
        L.Notation (loc, dir, l1, assoc, prec, l2)
    | IDENT "interpretation"; id = QSTRING;
      (symbol, args, l3) = interpretation ->
        L.Interpretation (loc, id, (symbol, args), l3)
  ]];
  executable: [
    [ ncmd = grafite_ncommand; SYMBOL "." -> G.NCommand (loc, ncmd)
    | punct = npunctuation_tactical -> G.NTactic (loc, [punct])
    | tac = nnon_punctuation_tactical(*; punct = npunctuation_tactical*) ->
          G.NTactic (loc, [tac])
    | tac = ntactic (*; punct = npunctuation_tactical*) ->
         tac 
(*
    | tac = nnon_punctuation_tactical; 
        punct = npunctuation_tactical ->
          G.NTactic (loc, [tac; punct])
*)
    ]
  ];
  comment: [
    [ BEGINCOMMENT ; ex = executable ; ENDCOMMENT -> 
       G.Code (loc, ex)
    | str = NOTE -> 
       G.Note (loc, str)
    ]
  ];
  statement: [
    [ ex = executable ->
       fun ?(never_include=false) ~include_paths status ->
          let stm = G.Executable (loc, ex) in
          !grafite_callback stm;
	  status, LSome stm
    | com = comment ->
       fun ?(never_include=false) ~include_paths status -> 
          let stm = G.Comment (loc, com) in
          !grafite_callback stm;
	  status, LSome stm
    | (iloc,fname,normal,mode) = include_command ; SYMBOL "."  ->
       fun ?(never_include=false) ~include_paths status ->
	let _root, buri, fullpath, _rrelpath = 
          Librarian.baseuri_of_script ~include_paths fname in
        if never_include then raise (NoInclusionPerformed fullpath)
        else
         begin
	  let stm =
	   G.Executable
            (loc, G.Command (loc, G.Include (iloc,fname))) in
          !grafite_callback stm;
	  let status =
           LE.eval_command status (L.Include (iloc,buri,mode,fullpath)) in
          let stm =
	   G.Executable
            (loc,G.Command (loc,G.Include (iloc,buri)))
	  in
	   status, LSome stm
         end
    | scom = lexicon_command ; SYMBOL "." ->
       fun ?(never_include=false) ~include_paths status ->
          !lexicon_callback scom;	  
	  let status = LE.eval_command status scom in
          status, LNone loc
    | EOI -> raise End_of_file
    ]
  ];
END
(* }}} *)
;;

let _ = initialize_parser () ;;

let exc_located_wrapper f =
  try
    f ()
  with
  | Stdpp.Exc_located (_, End_of_file) -> raise End_of_file
  | Stdpp.Exc_located (floc, Stream.Error msg) ->
      raise (HExtlib.Localized (floc,CicNotationParser.Parse_error msg))
  | Stdpp.Exc_located (floc, HExtlib.Localized(_,exn)) ->
      raise
       (HExtlib.Localized (floc,CicNotationParser.Parse_error (Printexc.to_string exn)))
  | Stdpp.Exc_located (floc, exn) ->
      raise
       (HExtlib.Localized (floc,CicNotationParser.Parse_error (Printexc.to_string exn)))

let parse_statement lexbuf =
  exc_located_wrapper
    (fun () -> (Grammar.Entry.parse (Obj.magic !grafite_parser.statement) (Obj.magic lexbuf)))

let statement () = Obj.magic !grafite_parser.statement

let history = ref [] ;;

let push () =
  LexiconSync.push ();
  history := !grafite_parser :: !history;
  grafite_parser := initial_parser ();
  initialize_parser ()
;;

let pop () =
  LexiconSync.pop ();
  match !history with
  | [] -> assert false
  | gp :: tail ->
      grafite_parser := gp;
      history := tail
;;

(* vim:set foldmethod=marker: *)

