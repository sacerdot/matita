(* Copyright (C) 2004-2005, HELM Team.
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

open Printf
open GrafiteTypes

module TA = GrafiteAst

let debug = false
let debug_print = if debug then prerr_endline else ignore

  (** raised when one of the script margins (top or bottom) is reached *)
exception Margin
exception NoUnfinishedProof
exception ActionCancelled of string

let safe_substring s i j =
  try String.sub s i j with Invalid_argument _ -> assert false

let heading_nl_RE = Pcre.regexp "^\\s*\n\\s*"
let heading_nl_RE' = Pcre.regexp "^(\\s*\n\\s*)"
let only_dust_RE = Pcre.regexp "^(\\s|\n|%%[^\n]*\n)*$"
let multiline_RE = Pcre.regexp "^\n[^\n]+$"
let newline_RE = Pcre.regexp "\n"
let comment_RE = Pcre.regexp "\\(\\*(.|\n)*\\*\\)\n?" ~flags:[`UNGREEDY]
 
let comment str =
  if Pcre.pmatch ~rex:multiline_RE str then
    "\n(** " ^ (Pcre.replace ~rex:newline_RE str) ^ " *)"
  else
    "\n(**\n" ^ str ^ "\n*)"

let strip_comments str =
  Pcre.qreplace ~templ:"\n" ~pat:"\n\n" (Pcre.qreplace ~rex:comment_RE str)
;;
                     
let first_line s =
  let s = Pcre.replace ~rex:heading_nl_RE s in
  try
    let nl_pos = String.index s '\n' in
    String.sub s 0 nl_pos
  with Not_found -> s

type guistuff = {
  mathviewer:MatitaTypes.mathViewer;
  urichooser: UriManager.uri list -> UriManager.uri list;
  ask_confirmation: title:string -> message:string -> [`YES | `NO | `CANCEL];
  develcreator: containing:string option -> unit;
  mutable filenamedata: string option * MatitamakeLib.development option
}

let eval_with_engine guistuff lexicon_status grafite_status user_goal
 skipped_txt nonskipped_txt st
=
  let module TAPp = GrafiteAstPp in
  let module DTE = DisambiguateTypes.Environment in
  let module DP = DisambiguatePp in
  let parsed_text_length =
    String.length skipped_txt + String.length nonskipped_txt 
  in
  let text = skipped_txt ^ nonskipped_txt in
  let prefix_len = MatitaGtkMisc.utf8_string_length skipped_txt in
  let enriched_history_fragment =
   MatitaEngine.eval_ast ~do_heavy_checks:true
    lexicon_status grafite_status (text,prefix_len,st)
  in
  let enriched_history_fragment = List.rev enriched_history_fragment in
  (* really fragile *)
  let res,_ = 
    List.fold_left 
      (fun (acc, to_prepend) (status,alias) ->
       match alias with
       | None -> (status,to_prepend ^ nonskipped_txt)::acc,""
       | Some (k,((v,_) as value)) ->
            let newtxt = DP.pp_environment (DTE.add k value DTE.empty) in
            (status,to_prepend ^ newtxt ^ "\n")::acc, "")
      ([],skipped_txt) enriched_history_fragment
  in
  res,"",parsed_text_length

let wrap_with_developments guistuff f arg = 
  let compile_needed_and_go_on lexiconfile d exc =
    let target = Pcre.replace ~pat:"lexicon$" ~templ:"moo" lexiconfile in
    let target = Pcre.replace ~pat:"metadata$" ~templ:"moo" target in
    let refresh_cb () = 
      while Glib.Main.pending () do ignore(Glib.Main.iteration false); done
    in
    if not(MatitamakeLib.build_development_in_bg ~target refresh_cb d) then
      raise exc
    else
      f arg
  in
  let do_nothing () = raise (ActionCancelled "Inclusion not performed") in
  let check_if_file_is_exists f =
    assert(Pcre.pmatch ~pat:"ma$" f);
    let pwd = Sys.getcwd () in
    let f_pwd = pwd ^ "/" ^ f in
    if not (HExtlib.is_regular f_pwd) then
      raise (ActionCancelled ("File "^f_pwd^" does not exists!"))
    else
      raise 
        (ActionCancelled 
          ("Internal error: "^f_pwd^" exists but I'm unable to include it!"))
  in
  let handle_with_devel d lexiconfile mafile exc =
    let name = MatitamakeLib.name_for_development d in
    let title = "Unable to include " ^ lexiconfile in
    let message = 
      mafile ^ " is handled by development <b>" ^ name ^ "</b>.\n\n" ^
      "<i>Should I compile it and Its dependencies?</i>"
    in
    (match guistuff.ask_confirmation ~title ~message with
    | `YES -> compile_needed_and_go_on lexiconfile d exc
    | `NO -> raise exc
    | `CANCEL -> do_nothing ())
  in
  let handle_without_devel mafilename exc =
    let title = "Unable to include " ^ mafilename in
    let message = 
     mafilename ^ " is <b>not</b> handled by a development.\n" ^
     "All dependencies are automatically solved for a development.\n\n" ^
     "<i>Do you want to set up a development?</i>"
    in
    (match guistuff.ask_confirmation ~title ~message with
    | `YES -> 
        guistuff.develcreator ~containing:(Some (Filename.dirname mafilename));
        do_nothing ()
    | `NO -> raise exc
    | `CANCEL -> do_nothing())
  in
  try 
    f arg
  with
  | DependenciesParser.UnableToInclude mafilename -> 
      assert (Pcre.pmatch ~pat:"ma$" mafilename);
      check_if_file_is_exists mafilename
  | LexiconEngine.IncludedFileNotCompiled (xfilename,mafilename) 
  | GrafiteEngine.IncludedFileNotCompiled (xfilename,mafilename) as exn ->
      assert (Pcre.pmatch ~pat:"ma$" mafilename);
      assert (Pcre.pmatch ~pat:"lexicon$" xfilename || 
              Pcre.pmatch ~pat:"mo$" xfilename );
      (* we know that someone was able to include the .ma, get the baseuri
       * but was unable to get the compilation output 'xfilename' *)
      match MatitamakeLib.development_for_dir (Filename.dirname mafilename) with
      | None -> handle_without_devel mafilename exn
      | Some d -> handle_with_devel d xfilename mafilename exn
;;
    
let eval_with_engine
     guistuff lexicon_status grafite_status user_goal 
       skipped_txt nonskipped_txt st
=
  wrap_with_developments guistuff
    (eval_with_engine 
      guistuff lexicon_status grafite_status user_goal 
        skipped_txt nonskipped_txt) st
;;

let pp_eager_statement_ast =
  GrafiteAstPp.pp_statement ~term_pp:CicNotationPp.pp_term
    ~lazy_term_pp:(fun _ -> assert false) ~obj_pp:(fun _ -> assert false)

(* naive implementation of procedural proof script generation, 
 * starting from an applicatiove *auto generated) proof.
 * this is out of place, but I like it :-P *)
let cic2grafite context menv t =
  (* indents a proof script in a stupid way, better than nothing *)
  let stupid_indenter s =
    let next s = 
      let idx_square_o = try String.index s '[' with Not_found -> -1 in
      let idx_square_c = try String.index s ']' with Not_found -> -1 in
      let idx_pipe = try String.index s '|' with Not_found -> -1 in
      let tok = 
        List.sort (fun (i,_) (j,_) -> compare i j)
          [idx_square_o,'[';idx_square_c,']';idx_pipe,'|']
      in
      let tok = List.filter (fun (i,_) -> i <> -1) tok in
      match tok with
      | (i,c)::_ -> Some (i,c)
      | _ -> None
    in
    let break_apply n s =
      let tab = String.make (n+1) ' ' in
      Pcre.replace ~templ:(".\n" ^ tab ^ "apply") ~pat:"\\.apply" s
    in
    let rec ind n s =
      match next s with
      | None -> 
          s
      | Some (position, char) ->
          try 
            let s1, s2 = 
              String.sub s 0 position, 
              String.sub s (position+1) (String.length s - (position+1))
            in
            match char with
            | '[' -> break_apply n s1 ^ "\n" ^ String.make (n+2) ' ' ^
                       "[" ^ ind (n+2) s2
            | '|' -> break_apply n s1 ^ "\n" ^ String.make n ' ' ^ 
                       "|" ^ ind n s2
            | ']' -> break_apply n s1 ^ "\n" ^ String.make n ' ' ^ 
                       "]" ^ ind (n-2) s2
            | _ -> assert false
          with
          Invalid_argument err -> 
            prerr_endline err;
            s
    in
     ind 0 s
  in
  let module PT = CicNotationPt in
  let module GA = GrafiteAst in
  let pp_t context t =
    let names = 
      List.map (function Some (n,_) -> Some n | None -> None) context 
    in
    CicPp.pp t names
  in
  let sort_of context t = 
    try
      let ty,_ = 
        CicTypeChecker.type_of_aux' menv context t
          CicUniv.oblivion_ugraph 
      in
      let sort,_ = CicTypeChecker.type_of_aux' menv context ty
          CicUniv.oblivion_ugraph
      in
      match sort with
      | Cic.Sort Cic.Prop -> true
      | _ -> false
    with
      CicTypeChecker.TypeCheckerFailure _ ->
        HLog.error "auto proof to sript transformation error"; false
  in
  let floc = HExtlib.dummy_floc in
  (* minimalisti cic.term -> pt.term *)
  let print_term c t =
    let rec aux c = function
      | Cic.Rel _
      | Cic.MutConstruct _ 
      | Cic.MutInd _ 
      | Cic.Const _ as t -> 
          PT.Ident (pp_t c t, None)
      | Cic.Appl l -> PT.Appl (List.map (aux c) l)
      | Cic.Implicit _ -> PT.Implicit
      | Cic.Lambda (Cic.Name n, s, t) ->
          PT.Binder (`Lambda, (PT.Ident (n,None), Some (aux c s)),
            aux (Some (Cic.Name n, Cic.Decl s)::c) t)
      | Cic.Prod (Cic.Name n, s, t) ->
          PT.Binder (`Forall, (PT.Ident (n,None), Some (aux c s)),
            aux (Some (Cic.Name n, Cic.Decl s)::c) t)
      | Cic.LetIn (Cic.Name n, s, t) ->
          PT.Binder (`Lambda, (PT.Ident (n,None), Some (aux c s)),
            aux (Some (Cic.Name n, Cic.Def (s,None))::c) t)
      | Cic.Meta _ -> PT.Implicit
      | Cic.Sort (Cic.Type u) -> PT.Sort (`Type u)
      | Cic.Sort Cic.Set -> PT.Sort `Set
      | Cic.Sort Cic.CProp -> PT.Sort `CProp
      | Cic.Sort Cic.Prop -> PT.Sort `Prop
      | _ as t -> PT.Ident ("ERROR: "^CicPp.ppterm t, None)
    in
    aux c t
  in
  (* prints an applicative proof, that is an auto proof.
   * don't use in the general case! *)
  let rec print_proof context = function
    | Cic.Rel _
    | Cic.Const _ as t -> 
        [GA.Executable (floc, 
          GA.Tactic (floc,
          Some (GA.Apply (floc, print_term context t)), GA.Dot floc))]
    | Cic.Appl (he::tl) ->
        let tl = List.map (fun t -> t, sort_of context t) tl in
        let subgoals = 
          HExtlib.filter_map (function (t,true) -> Some t | _ -> None) tl
        in
        let args = 
          List.map (function | (t,true) -> Cic.Implicit None | (t,_) -> t) tl
        in
        if List.length subgoals > 1 then
          (* branch *)
          [GA.Executable (floc, 
            GA.Tactic (floc,
              Some (GA.Apply (floc, print_term context (Cic.Appl (he::args)))),
              GA.Semicolon floc))] @
          [GA.Executable (floc, GA.Tactic (floc, None, GA.Branch floc))] @
          (HExtlib.list_concat 
          ~sep:[GA.Executable (floc, GA.Tactic (floc, None,GA.Shift floc))]
            (List.map (print_proof context) subgoals)) @
          [GA.Executable (floc, GA.Tactic (floc, None,GA.Merge floc))]
        else
          (* simple apply *)
          [GA.Executable (floc, 
            GA.Tactic (floc,
            Some (GA.Apply 
              (floc, print_term context (Cic.Appl (he::args)) )), GA.Dot floc))]
          @
          (match subgoals with
          | [] -> []
          | [x] -> print_proof context x
          | _ -> assert false)
    | Cic.Lambda (Cic.Name n, ty, bo) ->
        [GA.Executable (floc, 
          GA.Tactic (floc,
            Some (GA.Cut (floc, Some n, (print_term context ty))),
            GA.Branch floc))] @
        (print_proof (Some (Cic.Name n, Cic.Decl ty)::context) bo) @
        [GA.Executable (floc, GA.Tactic (floc, None,GA.Shift floc))] @
        [GA.Executable (floc, GA.Tactic (floc, 
          Some (GA.Assumption floc),GA.Merge floc))]
    | _ -> []
    (*
        debug_print (lazy (CicPp.ppterm t));
        assert false
        *)
  in
  (* performs a lambda closure of the proof term abstracting metas.
   * this is really an approximation of a closure, local subst of metas 
   * is not kept into account *)
  let close_pt menv context t =
    let metas = CicUtil.metas_of_term t in
    let metas = 
      HExtlib.list_uniq ~eq:(fun (i,_) (j,_) -> i = j)
        (List.sort (fun (i,_) (j,_) -> compare i j) metas)
    in
    let mk_rels_and_collapse_metas metas = 
      let rec aux i map acc acc1 = function 
        | [] -> acc, acc1, map
        | (j,_ as m)::tl -> 
            let _,_,ty = CicUtil.lookup_meta j menv in
            try 
              let n = List.assoc ty map in
              aux i map (Cic.Rel n :: acc) (m::acc1) tl 
            with Not_found -> 
              let map = (ty, i)::map in
              aux (i+1) map (Cic.Rel i :: acc) (m::acc1) tl
      in
      aux 1 [] [] [] metas
    in
    let rels, metas, map = mk_rels_and_collapse_metas metas in
    let n_lambdas = List.length map in
    let t = 
      if metas = [] then 
        t 
      else
        let t =
          ProofEngineReduction.replace_lifting
           ~what:(List.map (fun (x,_) -> Cic.Meta (x,[])) metas)
           ~with_what:rels
           ~context:context
           ~equality:(fun _ x y ->
             match x,y with
             | Cic.Meta(i,_), Cic.Meta(j,_) when i=j -> true
             | _ -> false)
           ~where:(CicSubstitution.lift n_lambdas t)
        in
        let rec mk_lam = function 
          | [] -> t 
          | (ty,n)::tl -> 
              let name = "fresh_"^ string_of_int n in
              Cic.Lambda (Cic.Name name, ty, mk_lam tl)
        in
         mk_lam 
          (fst (List.fold_left 
            (fun (l,liftno) (ty,_)  -> 
              (l @ [CicSubstitution.lift liftno ty,liftno] , liftno+1))
            ([],0) map))
    in
      t
  in
  let ast = print_proof context (close_pt menv context t) in
  let pp t = 
    (* ZACK: setting width to 80 will trigger a bug of BoxPp.render_to_string
     * which will show up using the following command line:
     * ./tptp2grafite -tptppath ~tassi/TPTP-v3.1.1 GRP170-1 *)
    let width = max_int in
    let term_pp content_term =
      let pres_term = TermContentPres.pp_ast content_term in
      let dummy_tbl = Hashtbl.create 1 in
      let markup = CicNotationPres.render dummy_tbl pres_term in
      let s = "(" ^ BoxPp.render_to_string List.hd width markup ^ ")" in
      Pcre.substitute 
        ~pat:"\\\\forall [Ha-z][a-z0-9_]*" ~subst:(fun x -> "\n" ^ x) s
    in
    CicNotationPp.set_pp_term term_pp;
    let lazy_term_pp = fun x -> assert false in
    let obj_pp = CicNotationPp.pp_obj CicNotationPp.pp_term in
    GrafiteAstPp.pp_statement ~term_pp ~lazy_term_pp ~obj_pp t
  in
  let script = String.concat "" (List.map pp ast) in
  prerr_endline script;
  stupid_indenter script
;;

let rec eval_macro include_paths (buffer : GText.buffer) guistuff lexicon_status grafite_status user_goal unparsed_text parsed_text script mac =
  let module TAPp = GrafiteAstPp in
  let module MQ = MetadataQuery in
  let module MDB = LibraryDb in
  let module CTC = CicTypeChecker in
  let module CU = CicUniv in
  (* no idea why ocaml wants this *)
  let parsed_text_length = String.length parsed_text in
  let dbd = LibraryDb.instance () in
  let pp_macro = 
    let f t = ProofEngineReduction.replace 
      ~equality:(fun _ t -> match t with Cic.Meta _ -> true | _ -> false)
      ~what:[()] ~with_what:[Cic.Implicit None] ~where:t
    in
    let metasenv = GrafiteTypes.get_proof_metasenv grafite_status in
    TAPp.pp_macro 
      ~term_pp:(fun x -> 
        ApplyTransformation.txt_of_cic_term max_int metasenv [] (f x))
  in
  match mac with
  (* WHELP's stuff *)
  | TA.WMatch (loc, term) -> 
     let l =  Whelp.match_term ~dbd term in
     let entry = `Whelp (pp_macro mac, l) in
     guistuff.mathviewer#show_uri_list ~reuse:true ~entry l;
     [], "", parsed_text_length
  | TA.WInstance (loc, term) ->
     let l = Whelp.instance ~dbd term in
     let entry = `Whelp (pp_macro mac, l) in
     guistuff.mathviewer#show_uri_list ~reuse:true ~entry l;
     [], "", parsed_text_length
  | TA.WLocate (loc, s) -> 
     let l = Whelp.locate ~dbd s in
     let entry = `Whelp (pp_macro mac, l) in
     guistuff.mathviewer#show_uri_list ~reuse:true ~entry l;
     [], "", parsed_text_length
  | TA.WElim (loc, term) ->
     let uri =
       match term with
       | Cic.MutInd (uri,n,_) -> UriManager.uri_of_uriref uri n None 
       | _ -> failwith "Not a MutInd"
     in
     let l = Whelp.elim ~dbd uri in
     let entry = `Whelp (pp_macro mac, l) in
     guistuff.mathviewer#show_uri_list ~reuse:true ~entry l;
     [], "", parsed_text_length
  | TA.WHint (loc, term) ->
     let _subst = [] in
     let s = ((None,[0,[],term], _subst, Cic.Meta (0,[]) ,term, []),0) in
     let l = List.map fst (MQ.experimental_hint ~dbd s) in
     let entry = `Whelp (pp_macro mac, l) in
     guistuff.mathviewer#show_uri_list ~reuse:true ~entry l;
     [], "", parsed_text_length
  (* REAL macro *)
  | TA.Hint loc -> 
      let user_goal' =
       match user_goal with
          Some n -> n
        | None -> raise NoUnfinishedProof
      in
      let proof = GrafiteTypes.get_current_proof grafite_status in
      let proof_status = proof,user_goal' in
      let l = List.map fst (MQ.experimental_hint ~dbd proof_status) in
      let selected = guistuff.urichooser l in
      (match selected with
      | [] -> [], "", parsed_text_length
      | [uri] -> 
          let suri = UriManager.string_of_uri uri in
          let ast loc =
            TA.Executable (loc, (TA.Tactic (loc,
             Some (TA.Apply (loc, CicNotationPt.Uri (suri, None))),
             TA.Dot loc))) in
          let text =
           comment parsed_text ^ "\n" ^
            pp_eager_statement_ast (ast HExtlib.dummy_floc) in
          let text_len = MatitaGtkMisc.utf8_string_length text in
          let loc = HExtlib.floc_of_loc (0,text_len) in
          let statement = `Ast (GrafiteParser.LSome (ast loc),text) in
          let res,_,_parsed_text_len =
           eval_statement include_paths buffer guistuff lexicon_status
            grafite_status user_goal script statement
          in
           (* we need to replace all the parsed_text *)
           res,"",String.length parsed_text
      | _ -> 
          HLog.error 
            "The result of the urichooser should be only 1 uri, not:\n";
          List.iter (
            fun u -> HLog.error (UriManager.string_of_uri u ^ "\n")
          ) selected;
          assert false)
  | TA.Check (_,term) ->
      let metasenv = GrafiteTypes.get_proof_metasenv grafite_status in
      let context =
       match user_goal with
          None -> []
        | Some n -> GrafiteTypes.get_proof_context grafite_status n in
      let ty,_ = CTC.type_of_aux' metasenv context term CicUniv.empty_ugraph in
      let t_and_ty = Cic.Cast (term,ty) in
      guistuff.mathviewer#show_entry (`Cic (t_and_ty,metasenv));
      [], "", parsed_text_length
  | TA.AutoInteractive (_, params) ->
      let user_goal' =
       match user_goal with
          Some n -> n
        | None -> raise NoUnfinishedProof
      in
      let proof = GrafiteTypes.get_current_proof grafite_status in
      let proof_status = proof,user_goal' in
      (try
        let _,menv,_,_,_,_ = proof in
        let i,cc,ty = CicUtil.lookup_meta user_goal' menv in
        let timestamp = Unix.gettimeofday () in
        let (_,menv,subst,_,_,_), _ = 
          ProofEngineTypes.apply_tactic
            (Auto.auto_tac ~dbd ~params
              ~universe:grafite_status.GrafiteTypes.universe) proof_status
        in
        let proof_term = 
          let irl = 
            CicMkImplicit.identity_relocation_list_for_metavariable cc
          in
          CicMetaSubst.apply_subst subst (Cic.Meta (i,irl))
        in
        let time = Unix.gettimeofday () -. timestamp in
        let text = 
          comment parsed_text ^ "\n" ^ 
          cic2grafite cc menv proof_term ^ 
          (Printf.sprintf "\n(* end auto proof: %4.2f *)" time)
        in
        (* alternative using FG stuff 
        let proof_term = 
          Auto.lambda_close ~prefix_name:"orrible_hack_" proof_term menv cc 
        in
        let ty,_ = 
          CicTypeChecker.type_of_aux' menv [] proof_term CicUniv.empty_ugraph
        in
        let obj = 
          Cic.Constant ("",Some proof_term, ty, [], [`Flavour `Lemma])
        in
        let text = 
          comment parsed_text ^ 
          Pcre.qreplace ~templ:"?" ~pat:"orrible_hack_[0-9]+"
           (strip_comments
            (ApplyTransformation.txt_of_cic_object
              ~map_unicode_to_tex:false 
              ~skip_thm_and_qed:true
              ~skip_initial_lambdas:true
              80 (GrafiteAst.Procedural None) "" obj)) ^
          "(* end auto proof *)"
        in
        *)
        [],text,parsed_text_length
      with
        ProofEngineTypes.Fail _ -> [], comment parsed_text, parsed_text_length)
  | TA.Inline (_,style,suri,prefix) ->
       let str = ApplyTransformation.txt_of_inline_macro style suri prefix in
       [], str, String.length parsed_text
                                
and eval_executable include_paths (buffer : GText.buffer) guistuff
lexicon_status grafite_status user_goal unparsed_text skipped_txt nonskipped_txt
script ex loc
=
 let module TAPp = GrafiteAstPp in
 let module MD = GrafiteDisambiguator in
 let module ML = MatitaMisc in
  try
   begin
    match ex with
     | TA.Command (_,TA.Set (_,"baseuri",u)) ->
        if  Http_getter_storage.is_read_only u then
          raise (ActionCancelled ("baseuri " ^ u ^ " is readonly"));
        if not (Http_getter_storage.is_empty u) then
         (match 
            guistuff.ask_confirmation 
              ~title:"Baseuri redefinition" 
              ~message:(
                "Baseuri " ^ u ^ " already exists.\n" ^
                "Do you want to redefine the corresponding "^
                "part of the library?")
          with
           | `YES -> LibraryClean.clean_baseuris [u]
           | `NO -> ()
           | `CANCEL -> raise MatitaTypes.Cancel)
     | _ -> ()
   end;
   ignore (buffer#move_mark (`NAME "beginning_of_statement")
    ~where:((buffer#get_iter_at_mark (`NAME "locked"))#forward_chars
       (Glib.Utf8.length skipped_txt))) ;
   eval_with_engine
    guistuff lexicon_status grafite_status user_goal skipped_txt nonskipped_txt
     (TA.Executable (loc, ex))
  with
     MatitaTypes.Cancel -> [], "", 0
   | GrafiteEngine.Macro (_loc,lazy_macro) ->
      let context =
       match user_goal with
          None -> []
        | Some n -> GrafiteTypes.get_proof_context grafite_status n in
      let grafite_status,macro = lazy_macro context in
       eval_macro include_paths buffer guistuff lexicon_status grafite_status
        user_goal unparsed_text (skipped_txt ^ nonskipped_txt) script macro

and eval_statement include_paths (buffer : GText.buffer) guistuff lexicon_status
 grafite_status user_goal script statement
=
  let (lexicon_status,st), unparsed_text =
    match statement with
    | `Raw text ->
        if Pcre.pmatch ~rex:only_dust_RE text then raise Margin;
        let ast = 
          wrap_with_developments guistuff
            (GrafiteParser.parse_statement 
              (Ulexing.from_utf8_string text) ~include_paths) lexicon_status 
        in
          ast, text
    | `Ast (st, text) -> (lexicon_status, st), text
  in
  let text_of_loc floc = 
    let nonskipped_txt,_ = MatitaGtkMisc.utf8_parsed_text unparsed_text floc in
    let start, stop = HExtlib.loc_of_floc floc in 
    let floc = HExtlib.floc_of_loc (0, start) in
    let skipped_txt,_ = MatitaGtkMisc.utf8_parsed_text unparsed_text floc in
    let floc = HExtlib.floc_of_loc (0, stop) in
    let txt,len = MatitaGtkMisc.utf8_parsed_text unparsed_text floc in
    txt,nonskipped_txt,skipped_txt,len
  in 
  match st with
  | GrafiteParser.LNone loc ->
      let parsed_text, _, _, parsed_text_length = text_of_loc loc in
       [(grafite_status,lexicon_status),parsed_text],"",
        parsed_text_length
  | GrafiteParser.LSome (GrafiteAst.Comment (loc, _)) -> 
      let parsed_text, _, _, parsed_text_length = text_of_loc loc in
      let remain_len = String.length unparsed_text - parsed_text_length in
      let s = String.sub unparsed_text parsed_text_length remain_len in
      let s,text,len = 
       try
        eval_statement include_paths buffer guistuff lexicon_status
         grafite_status user_goal script (`Raw s)
       with
          HExtlib.Localized (floc, exn) ->
           HExtlib.raise_localized_exception 
             ~offset:(MatitaGtkMisc.utf8_string_length parsed_text) floc exn
        | GrafiteDisambiguator.DisambiguationError (offset,errorll) ->
           raise
            (GrafiteDisambiguator.DisambiguationError
              (offset+parsed_text_length, errorll))
      in
      assert (text=""); (* no macros inside comments, please! *)
      (match s with
      | (statuses,text)::tl ->
         (statuses,parsed_text ^ text)::tl,"",parsed_text_length + len
      | [] -> [], "", 0)
  | GrafiteParser.LSome (GrafiteAst.Executable (loc, ex)) ->
     let _, nonskipped, skipped, parsed_text_length = 
       text_of_loc loc 
     in
      eval_executable include_paths buffer guistuff lexicon_status
       grafite_status user_goal unparsed_text skipped nonskipped script ex loc
  
let fresh_script_id =
  let i = ref 0 in
  fun () -> incr i; !i

class script  ~(source_view: GSourceView.source_view)
              ~(mathviewer: MatitaTypes.mathViewer) 
              ~set_star
              ~ask_confirmation
              ~urichooser 
              ~develcreator 
              () =
let buffer = source_view#buffer in
let source_buffer = source_view#source_buffer in
let initial_statuses () =
 (* these include_paths are used only to load the initial notation *)
 let include_paths =
  Helm_registry.get_list Helm_registry.string "matita.includes" in
 let lexicon_status =
  CicNotation2.load_notation ~include_paths
   BuildTimeConf.core_notation_script in
 let grafite_status = GrafiteSync.init () in
  grafite_status,lexicon_status
in
object (self)
  val mutable include_paths =
   Helm_registry.get_list Helm_registry.string "matita.includes"

  val scriptId = fresh_script_id ()
  
  val guistuff = {
    mathviewer = mathviewer;
    urichooser = urichooser;
    ask_confirmation = ask_confirmation;
    develcreator = develcreator;
    filenamedata = (None, None)} 
  
  method private getFilename =
    match guistuff.filenamedata with Some f,_ -> f | _ -> assert false

  method filename = self#getFilename
    
  method private ppFilename =
    match guistuff.filenamedata with 
    | Some f,_ -> f 
    | None,_ -> sprintf ".unnamed%d.ma" scriptId
  
  initializer 
    ignore (GMain.Timeout.add ~ms:300000 
       ~callback:(fun _ -> self#_saveToBackupFile ();true));
    ignore (buffer#connect#modified_changed 
      (fun _ -> set_star (Filename.basename self#ppFilename) buffer#modified))

  val mutable statements = []    (** executed statements *)

  val mutable history = [ initial_statuses () ]
    (** list of states before having executed statements. Head element of this
      * list is the current state, last element is the state at the beginning of
      * the script.
      * Invariant: this list length is 1 + length of statements *)

  (** goal as seen by the user (i.e. metano corresponding to current tab) *)
  val mutable userGoal = None

  (** text mark and tag representing locked part of a script *)
  val locked_mark =
    buffer#create_mark ~name:"locked" ~left_gravity:true buffer#start_iter
  val beginning_of_statement_mark =
    buffer#create_mark ~name:"beginning_of_statement"
     ~left_gravity:true buffer#start_iter
  val locked_tag = buffer#create_tag [`BACKGROUND "lightblue"; `EDITABLE false]
  val error_tag = buffer#create_tag [`UNDERLINE `SINGLE; `FOREGROUND "red"]

  method locked_mark = locked_mark
  method locked_tag = locked_tag
  method error_tag = error_tag

    (* history can't be empty, the invariant above grant that it contains at
     * least the init grafite_status *)
  method grafite_status = match history with (s,_)::_ -> s | _ -> assert false
  method lexicon_status = match history with (_,ss)::_ -> ss | _ -> assert false

  method private _advance ?statement () =
   let s = match statement with Some s -> s | None -> self#getFuture in
   HLog.debug ("evaluating: " ^ first_line s ^ " ...");
   let entries, newtext, parsed_len = 
    try
     eval_statement include_paths buffer guistuff self#lexicon_status
      self#grafite_status userGoal self (`Raw s)
    with End_of_file -> raise Margin
   in
   let new_statuses, new_statements =
     let statuses, texts = List.split entries in
     statuses, texts
   in
   history <- new_statuses @ history;
   statements <- new_statements @ statements;
   let start = buffer#get_iter_at_mark (`MARK locked_mark) in
   let new_text = String.concat "" (List.rev new_statements) in
   if statement <> None then
     buffer#insert ~iter:start new_text
   else begin
     let parsed_text = String.sub s 0 parsed_len in
     if new_text <> parsed_text then begin
       let stop = start#copy#forward_chars (Glib.Utf8.length parsed_text) in
       buffer#delete ~start ~stop;
       buffer#insert ~iter:start new_text;
     end;
   end;
   self#moveMark (Glib.Utf8.length new_text);
   buffer#insert ~iter:(buffer#get_iter_at_mark (`MARK locked_mark)) newtext;
   (* here we need to set the Goal in case we are going to cursor (or to
      bottom) and we will face a macro *)
   match self#grafite_status.proof_status with
      Incomplete_proof p ->
       userGoal <-
         (try Some (Continuationals.Stack.find_goal p.stack)
         with Failure _ -> None)
    | _ -> userGoal <- None

  method private _retract offset lexicon_status grafite_status new_statements
   new_history
  =
   let cur_grafite_status,cur_lexicon_status =
    match history with s::_ -> s | [] -> assert false
   in
    LexiconSync.time_travel ~present:cur_lexicon_status ~past:lexicon_status;
    GrafiteSync.time_travel ~present:cur_grafite_status ~past:grafite_status;
    statements <- new_statements;
    history <- new_history;
    self#moveMark (- offset)

  method advance ?statement () =
    try
      self#_advance ?statement ();
      self#notify
    with 
    | Margin -> self#notify
    | Not_found -> assert false
    | Invalid_argument "Array.make" -> HLog.error "The script is too big!\n"
    | exc -> self#notify; raise exc

  method retract () =
    try
      let cmp,new_statements,new_history,(grafite_status,lexicon_status) =
       match statements,history with
          stat::statements, _::(status::_ as history) ->
           assert (Glib.Utf8.validate stat);
           Glib.Utf8.length stat, statements, history, status
       | [],[_] -> raise Margin
       | _,_ -> assert false
      in
       self#_retract cmp lexicon_status grafite_status new_statements
        new_history;
       self#notify
    with 
    | Margin -> self#notify
    | Invalid_argument "Array.make" -> HLog.error "The script is too big!\n"
    | exc -> self#notify; raise exc

  method private getFuture =
    buffer#get_text ~start:(buffer#get_iter_at_mark (`MARK locked_mark))
      ~stop:buffer#end_iter ()

      
  (** @param rel_offset relative offset from current position of locked_mark *)
  method private moveMark rel_offset =
    let mark = `MARK locked_mark in
    let old_insert = buffer#get_iter_at_mark `INSERT in
    buffer#remove_tag locked_tag ~start:buffer#start_iter ~stop:buffer#end_iter;
    let current_mark_pos = buffer#get_iter_at_mark mark in
    let new_mark_pos =
      match rel_offset with
      | 0 -> current_mark_pos
      | n when n > 0 -> current_mark_pos#forward_chars n
      | n (* when n < 0 *) -> current_mark_pos#backward_chars (abs n)
    in
    buffer#move_mark mark ~where:new_mark_pos;
    buffer#apply_tag locked_tag ~start:buffer#start_iter ~stop:new_mark_pos;
    buffer#move_mark `INSERT old_insert;
    let mark_position = buffer#get_iter_at_mark mark in
    if source_view#move_mark_onscreen mark then
     begin
      buffer#move_mark mark mark_position;
      source_view#scroll_to_mark ~use_align:true ~xalign:1.0 ~yalign:0.1 mark;
     end;
    while Glib.Main.pending () do ignore(Glib.Main.iteration false); done

  method clean_dirty_lock =
    let lock_mark_iter = buffer#get_iter_at_mark (`MARK locked_mark) in
    buffer#remove_tag locked_tag ~start:buffer#start_iter ~stop:buffer#end_iter;
    buffer#apply_tag locked_tag ~start:buffer#start_iter ~stop:lock_mark_iter

  val mutable observers = []

  method addObserver (o: LexiconEngine.status -> GrafiteTypes.status -> unit) =
    observers <- o :: observers

  method private notify =
    let lexicon_status = self#lexicon_status in
    let grafite_status = self#grafite_status in
    List.iter (fun o -> o lexicon_status grafite_status) observers

  method loadFromString s =
    buffer#set_text s;
    self#reset_buffer;
    buffer#set_modified true

  method loadFromFile f =
    buffer#set_text (HExtlib.input_file f);
    self#reset_buffer;
    buffer#set_modified false
    
  method assignFileName file =
    let abspath = MatitaMisc.absolute_path file in
    let dirname = Filename.dirname abspath in
    let devel = MatitamakeLib.development_for_dir dirname in
    guistuff.filenamedata <- Some abspath, devel;
    let include_ = 
     match MatitamakeLib.development_for_dir dirname with
        None -> []
      | Some devel -> [MatitamakeLib.root_for_development devel] in
    let include_ =
     include_ @ (Helm_registry.get_list Helm_registry.string "matita.includes")
    in
     include_paths <- include_
    
  method saveToFile () =
    let oc = open_out self#getFilename in
    output_string oc (buffer#get_text ~start:buffer#start_iter
                        ~stop:buffer#end_iter ());
    close_out oc;
    buffer#set_modified false
  
  method private _saveToBackupFile () =
    if buffer#modified then
      begin
        let f = self#ppFilename ^ "~" in
        let oc = open_out f in
        output_string oc (buffer#get_text ~start:buffer#start_iter
                            ~stop:buffer#end_iter ());
        close_out oc;
        HLog.debug ("backup " ^ f ^ " saved")                    
      end
  
  method private goto_top =
    let grafite_status,lexicon_status = 
      let rec last x = function 
      | [] -> x
      | hd::tl -> last hd tl
      in
      last (self#grafite_status,self#lexicon_status) history
    in
    (* FIXME: this is not correct since there is no undo for 
     * library_objects.set_default... *)
    GrafiteSync.time_travel ~present:self#grafite_status ~past:grafite_status;
    LexiconSync.time_travel ~present:self#lexicon_status ~past:lexicon_status

  method private reset_buffer = 
    statements <- [];
    history <- [ initial_statuses () ];
    userGoal <- None;
    self#notify;
    buffer#remove_tag locked_tag ~start:buffer#start_iter ~stop:buffer#end_iter;
    buffer#move_mark (`MARK locked_mark) ~where:buffer#start_iter

  method reset () =
    self#reset_buffer;
    source_buffer#begin_not_undoable_action ();
    buffer#delete ~start:buffer#start_iter ~stop:buffer#end_iter;
    source_buffer#end_not_undoable_action ();
    buffer#set_modified false;
  
  method template () =
    let template = HExtlib.input_file BuildTimeConf.script_template in 
    buffer#insert ~iter:(buffer#get_iter `START) template;
    let development = MatitamakeLib.development_for_dir (Unix.getcwd ()) in
    guistuff.filenamedata <- (None,development);
    let include_ = 
     match development with
        None -> []
      | Some devel -> [MatitamakeLib.root_for_development devel ]
    in
    let include_ =
     include_ @ (Helm_registry.get_list Helm_registry.string "matita.includes")
    in
     include_paths <- include_ ;
     buffer#set_modified false;
     set_star (Filename.basename self#ppFilename) false

  method goto (pos: [`Top | `Bottom | `Cursor]) () =
  try  
    let old_locked_mark =
     `MARK
       (buffer#create_mark ~name:"old_locked_mark"
         ~left_gravity:true (buffer#get_iter_at_mark (`MARK locked_mark))) in
    let getpos _ = buffer#get_iter_at_mark (`MARK locked_mark) in 
    let getoldpos _ = buffer#get_iter_at_mark old_locked_mark in 
    let dispose_old_locked_mark () = buffer#delete_mark old_locked_mark in
    match pos with
    | `Top -> 
        dispose_old_locked_mark (); 
        self#goto_top; 
        self#reset_buffer;
        self#notify
    | `Bottom ->
        (try 
          let rec dowhile () =
            self#_advance ();
            let newpos = getpos () in
            if (getoldpos ())#compare newpos < 0 then
              begin
                buffer#move_mark old_locked_mark newpos;
                dowhile ()
              end
          in
          dowhile ();
          dispose_old_locked_mark ();
          self#notify 
        with 
        | Margin -> dispose_old_locked_mark (); self#notify
        | exc -> dispose_old_locked_mark (); self#notify; raise exc)
    | `Cursor ->
        let locked_iter () = buffer#get_iter_at_mark (`NAME "locked") in
        let cursor_iter () = buffer#get_iter_at_mark `INSERT in
        let remember =
         `MARK
           (buffer#create_mark ~name:"initial_insert"
             ~left_gravity:true (cursor_iter ())) in
        let dispose_remember () = buffer#delete_mark remember in
        let remember_iter () =
         buffer#get_iter_at_mark (`NAME "initial_insert") in
        let cmp () = (locked_iter ())#offset - (remember_iter ())#offset in
        let icmp = cmp () in
        let forward_until_cursor () = (* go forward until locked > cursor *)
          let rec aux () =
            self#_advance ();
            if cmp () < 0 && (getoldpos ())#compare (getpos ()) < 0 
            then
             begin
              buffer#move_mark old_locked_mark (getpos ());
              aux ()
             end
          in
          aux ()
        in
        let rec back_until_cursor len = (* go backward until locked < cursor *)
         function
            statements, ((grafite_status,lexicon_status)::_ as history)
            when len <= 0 ->
             self#_retract (icmp - len) lexicon_status grafite_status statements
              history
          | statement::tl1, _::tl2 ->
             back_until_cursor (len - MatitaGtkMisc.utf8_string_length statement) (tl1,tl2)
          | _,_ -> assert false
        in
        (try
          begin
           if icmp < 0 then       (* locked < cursor *)
             (forward_until_cursor (); self#notify)
           else if icmp > 0 then  (* locked > cursor *)
             (back_until_cursor icmp (statements,history); self#notify)
           else                  (* cursor = locked *)
               ()
          end ;
          dispose_remember ();
          dispose_old_locked_mark ();
        with 
        | Margin -> dispose_remember (); dispose_old_locked_mark (); self#notify
        | exc -> dispose_remember (); dispose_old_locked_mark ();
                 self#notify; raise exc)
  with Invalid_argument "Array.make" ->
     HLog.error "The script is too big!\n"
  
  method onGoingProof () =
    match self#grafite_status.proof_status with
    | No_proof | Proof _ -> false
    | Incomplete_proof _ -> true
    | Intermediate _ -> assert false

(*   method proofStatus = MatitaTypes.get_proof_status self#status *)
  method proofMetasenv = GrafiteTypes.get_proof_metasenv self#grafite_status

  method proofContext =
   match userGoal with
      None -> []
    | Some n -> GrafiteTypes.get_proof_context self#grafite_status n

  method proofConclusion =
   match userGoal with
      None -> assert false
    | Some n ->
       GrafiteTypes.get_proof_conclusion self#grafite_status n

  method stack = GrafiteTypes.get_stack self#grafite_status
  method setGoal n = userGoal <- n
  method goal = userGoal

  method eos = 
    let rec is_there_only_comments lexicon_status s = 
      if Pcre.pmatch ~rex:only_dust_RE s then raise Margin;
      let lexicon_status,st =
       GrafiteParser.parse_statement (Ulexing.from_utf8_string s)
        ~include_paths lexicon_status
      in
      match st with
      | GrafiteParser.LSome (GrafiteAst.Comment (loc,_)) -> 
          let _,parsed_text_length = MatitaGtkMisc.utf8_parsed_text s loc in
          (* CSC: why +1 in the following lines ???? *)
          let parsed_text_length = parsed_text_length + 1 in
prerr_endline ("## " ^ string_of_int parsed_text_length);
          let remain_len = String.length s - parsed_text_length in
          let next = String.sub s parsed_text_length remain_len in
          is_there_only_comments lexicon_status next
      | GrafiteParser.LNone _
      | GrafiteParser.LSome (GrafiteAst.Executable _) -> false
    in
    try
      is_there_only_comments self#lexicon_status self#getFuture
    with 
    | LexiconEngine.IncludedFileNotCompiled _
    | HExtlib.Localized _
    | CicNotationParser.Parse_error _ -> false
    | Margin | End_of_file -> true
    | Invalid_argument "Array.make" -> false

  (* debug *)
  method dump () =
    HLog.debug "script status:";
    HLog.debug ("history size: " ^ string_of_int (List.length history));
    HLog.debug (sprintf "%d statements:" (List.length statements));
    List.iter HLog.debug statements;
    HLog.debug ("Current file name: " ^
      (match guistuff.filenamedata with 
      |None,_ -> "[ no name ]" 
      | Some f,_ -> f));

end

let _script = ref None

let script ~source_view ~mathviewer ~urichooser ~develcreator ~ask_confirmation ~set_star ()
=
  let s = new script 
    ~source_view ~mathviewer ~ask_confirmation ~urichooser ~develcreator ~set_star () 
  in
  _script := Some s;
  s

let current () = match !_script with None -> assert false | Some s -> s

