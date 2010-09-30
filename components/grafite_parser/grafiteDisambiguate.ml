(*
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

exception BaseUriNotSetYet

type tactic = 
 (CicNotationPt.term, CicNotationPt.term, 
  CicNotationPt.term GrafiteAst.reduction, string) 
   GrafiteAst.tactic
   
type lazy_tactic = 
  (Cic.term, Cic.lazy_term, Cic.lazy_term GrafiteAst.reduction, string) 
    GrafiteAst.tactic

let singleton msg = function
  | [x], _ -> x
  | l, _   ->
      let debug = 
         Printf.sprintf "GrafiteDisambiguate.singleton (%s): %u interpretations"
         msg (List.length l)
      in
      prerr_endline debug; assert false

let __Implicit = "__Implicit__"
let __Closed_Implicit = "__Closed_Implicit__"

let cic_mk_choice = function
  | LexiconAst.Symbol_alias (name, _, dsc) ->
     if name = __Implicit then
       dsc, `Sym_interp (fun _ -> Cic.Implicit None)
     else if name = __Closed_Implicit then 
       dsc, `Sym_interp (fun _ -> Cic.Implicit (Some `Closed))
     else
       DisambiguateChoices.cic_lookup_symbol_by_dsc name dsc
  | LexiconAst.Number_alias (_, dsc) ->
     DisambiguateChoices.lookup_num_by_dsc dsc
  | LexiconAst.Ident_alias (name, uri) -> 
     uri, `Sym_interp 
      (fun l->assert(l = []);CicUtil.term_of_uri (UriManager.uri_of_string uri))
;;

let ncic_mk_choice = function
  | LexiconAst.Symbol_alias (name, _, dsc) ->
     if name = __Implicit then
       dsc, `Sym_interp (fun _ -> NCic.Implicit `Term)
     else if name = __Closed_Implicit then 
       dsc, `Sym_interp (fun _ -> NCic.Implicit `Closed)
     else
       DisambiguateChoices.lookup_symbol_by_dsc 
        ~mk_implicit:(function 
           | true -> NCic.Implicit `Closed
           | false -> NCic.Implicit `Term)
        ~mk_appl:(function 
           (NCic.Appl l)::tl -> NCic.Appl (l@tl) | l -> NCic.Appl l)
        ~term_of_uri:(fun uri ->
           fst (OCic2NCic.convert_term uri (CicUtil.term_of_uri uri)))
        ~term_of_nref:(fun nref -> NCic.Const nref)
       name dsc
  | LexiconAst.Number_alias (_, dsc) -> 
     (try
       let desc,f = DisambiguateChoices.nlookup_num_by_dsc dsc in
        desc, `Num_interp
         (fun num -> match f with `Num_interp f -> f num | _ -> assert false)
      with
       DisambiguateChoices.Choice_not_found _ ->
        let desc,f = DisambiguateChoices.lookup_num_by_dsc dsc in
        desc, `Num_interp
         (fun num -> 
            fst (OCic2NCic.convert_term 
              (UriManager.uri_of_string "cic:/xxx/x.con") 
              (match f with `Num_interp f -> f num | _ -> assert false))))
  | LexiconAst.Ident_alias (name, uri) -> 
     uri, `Sym_interp 
      (fun l->assert(l = []);
        try
         let nref = NReference.reference_of_string uri in
          NCic.Const nref
        with
         NReference.IllFormedReference _ ->
          let uri = UriManager.uri_of_string uri in
           fst (OCic2NCic.convert_term uri (CicUtil.term_of_uri uri)))
;;


let mk_implicit b =
  match b with
  | false -> 
      LexiconAst.Symbol_alias (__Implicit,-1,"Fake Implicit")
  | true -> 
      LexiconAst.Symbol_alias (__Closed_Implicit,-1,"Fake Closed Implicit")
;;

let lookup_in_library 
  interactive_user_uri_choice input_or_locate_uri item 
=
  let mk_ident_alias id u =
    LexiconAst.Ident_alias (id,UriManager.string_of_uri u)
  in
  let mk_num_alias instance = 
    List.map 
     (fun dsc,_ -> LexiconAst.Number_alias (instance,dsc)) 
     (DisambiguateChoices.lookup_num_choices())
  in
  let mk_symbol_alias symb ino (dsc, _,_) =
     LexiconAst.Symbol_alias (symb,ino,dsc)
  in
  let dbd = LibraryDb.instance () in
  let choices_of_id id =
    let uris = Whelp.locate ~dbd id in
     match uris with
      | [] ->
         (match 
           (input_or_locate_uri 
             ~title:("URI matching \"" ^ id ^ "\" unknown.") 
             ?id:(Some id) ()) 
         with
         | None -> []
         | Some uri -> [uri])
      | [uri] -> [uri]
      | _ ->
          interactive_user_uri_choice ~selection_mode:`MULTIPLE
           ?ok:(Some "Try selected.") 
           ?enable_button_for_non_vars:(Some true)
           ~title:"Ambiguous input."
           ~msg: ("Ambiguous input \"" ^ id ^
              "\". Please, choose one or more interpretations:")
           ~id
           uris
  in
  match item with
  | DisambiguateTypes.Id id -> 
      let uris = choices_of_id id in
      List.map (mk_ident_alias id) uris
  | DisambiguateTypes.Symbol (symb, ino) ->
   (try
     List.map (mk_symbol_alias symb ino) 
      (TermAcicContent.lookup_interpretations symb)
    with
     TermAcicContent.Interpretation_not_found -> [])
  | DisambiguateTypes.Num instance -> mk_num_alias instance
;;

let nlookup_in_library 
  interactive_user_uri_choice input_or_locate_uri item 
=
  match item with
  | DisambiguateTypes.Id id -> 
     (try
       let references = NCicLibrary.resolve id in
        List.map
         (fun u -> LexiconAst.Ident_alias (id,NReference.string_of_reference u)
         ) references @
        lookup_in_library interactive_user_uri_choice input_or_locate_uri item
      with
       NCicEnvironment.ObjectNotFound _ ->
        lookup_in_library interactive_user_uri_choice input_or_locate_uri item)
  | _ -> lookup_in_library interactive_user_uri_choice input_or_locate_uri item 
;;

let fix_instance item l =
 match item with
    DisambiguateTypes.Symbol (_,n) ->
     List.map
      (function
          LexiconAst.Symbol_alias (s,_,d) -> LexiconAst.Symbol_alias (s,n,d)
        | _ -> assert false
      ) l
  | DisambiguateTypes.Num n ->
     List.map
      (function
          LexiconAst.Number_alias (_,d) -> LexiconAst.Number_alias (n,d)
        | _ -> assert false
      ) l
  | DisambiguateTypes.Id _ -> l
;;


  (** @param term not meaningful when context is given *)
let disambiguate_term expty text prefix_len lexicon_status_ref context metasenv
term =
  let lexicon_status = !lexicon_status_ref in
  let (diff, metasenv, subst, cic, _) =
    singleton "first"
      (CicDisambiguate.disambiguate_term
        ~aliases:lexicon_status#lstatus.LexiconEngine.aliases
        ~expty ~universe:(Some lexicon_status#lstatus.LexiconEngine.multi_aliases)
        ~lookup_in_library
        ~mk_choice:cic_mk_choice
        ~mk_implicit ~fix_instance
        ~description_of_alias:LexiconAst.description_of_alias
        ~context ~metasenv ~subst:[] (text,prefix_len,term))
  in
  let lexicon_status = LexiconEngine.set_proof_aliases lexicon_status diff in
  lexicon_status_ref := lexicon_status;
  metasenv,(*subst,*) cic
;;

let disambiguate_nterm expty estatus context metasenv subst thing
=
  let diff, metasenv, subst, cic =
    singleton "first"
      (NCicDisambiguate.disambiguate_term
        ~rdb:estatus
        ~aliases:estatus#lstatus.LexiconEngine.aliases
        ~expty 
        ~universe:(Some estatus#lstatus.LexiconEngine.multi_aliases)
        ~lookup_in_library:nlookup_in_library
        ~mk_choice:ncic_mk_choice
        ~mk_implicit ~fix_instance
        ~description_of_alias:LexiconAst.description_of_alias
        ~context ~metasenv ~subst thing)
  in
  let estatus = LexiconEngine.set_proof_aliases estatus diff in
   metasenv, subst, estatus, cic
;;


  (** disambiguate_lazy_term (circa): term -> (unit -> status) * lazy_term
   * rationale: lazy_term will be invoked in different context to obtain a term,
   * each invocation will disambiguate the term and can add aliases. Once all
   * disambiguations have been performed, the first returned function can be
   * used to obtain the resulting aliases *)
let disambiguate_lazy_term expty text prefix_len lexicon_status_ref term =
  (fun context metasenv ugraph ->
    let lexicon_status = !lexicon_status_ref in
    let (diff, metasenv, _, cic, ugraph) =
      singleton "second"
        (CicDisambiguate.disambiguate_term 
          ~lookup_in_library
          ~mk_choice:cic_mk_choice
          ~mk_implicit ~fix_instance
          ~description_of_alias:LexiconAst.description_of_alias
          ~initial_ugraph:ugraph ~aliases:lexicon_status#lstatus.LexiconEngine.aliases
          ~universe:(Some lexicon_status#lstatus.LexiconEngine.multi_aliases)
          ~context ~metasenv ~subst:[] 
          (text,prefix_len,term) ~expty) in
    let lexicon_status = LexiconEngine.set_proof_aliases lexicon_status diff in
    lexicon_status_ref := lexicon_status;
    cic, metasenv, ugraph)
;;

let disambiguate_pattern 
  text prefix_len lexicon_status_ref (wanted, hyp_paths, goal_path) 
=
  let interp path =CicDisambiguate.interpretate_path [] path in
  let goal_path = HExtlib.map_option interp goal_path in
  let hyp_paths = List.map (fun (name, path) -> name, interp path) hyp_paths in
  let wanted =
   match wanted with
      None -> None
    | Some wanted ->
       let wanted = 
         disambiguate_lazy_term None text prefix_len lexicon_status_ref wanted 
       in
       Some wanted
  in
  (wanted, hyp_paths, goal_path)
;;

type pattern = 
  CicNotationPt.term Disambiguate.disambiguator_input option * 
  (string * NCic.term) list * NCic.term option

let disambiguate_npattern (text, prefix_len, (wanted, hyp_paths, goal_path)) =
  let interp path = NCicDisambiguate.disambiguate_path path in
  let goal_path = HExtlib.map_option interp goal_path in
  let hyp_paths = List.map (fun (name, path) -> name, interp path) hyp_paths in
  let wanted = 
    match wanted with None -> None | Some x -> Some (text,prefix_len,x)
  in
   (wanted, hyp_paths, goal_path)
;;

let disambiguate_reduction_kind text prefix_len lexicon_status_ref = function
  | `Unfold (Some t) ->
      let t = 
         disambiguate_lazy_term None text prefix_len lexicon_status_ref t in
      `Unfold (Some t)
  | `Normalize
  | `Simpl
  | `Unfold None
  | `Whd as kind -> kind
;;

let disambiguate_auto_params 
  disambiguate_term metasenv context (oterms, params) 
=
  match oterms with 
    | None -> metasenv, (None, params)
    | Some terms ->
	let metasenv, terms = 
	  List.fold_right 
	    (fun t (metasenv, terms) ->
               let metasenv,t = disambiguate_term context metasenv t in
		 metasenv,t::terms) terms (metasenv, [])
	in
	  metasenv, (Some terms, params)
;;

let disambiguate_just disambiguate_term context metasenv =
 function
    `Term t ->
      let metasenv,t = disambiguate_term context metasenv t in
       metasenv, `Term t
  | `Auto params ->
      let metasenv,params = disambiguate_auto_params disambiguate_term metasenv
       context params
      in
       metasenv, `Auto params
;;
      
let rec disambiguate_tactic 
  lexicon_status_ref context metasenv goal (text,prefix_len,tactic) 
=
  let disambiguate_term_hint = 
    let _,_,expty = 
      List.find (fun (x,_,_) -> Some x = goal) metasenv
    in
    disambiguate_term (Some expty) text prefix_len lexicon_status_ref in
  let disambiguate_term = 
    disambiguate_term None text prefix_len lexicon_status_ref in
  let disambiguate_pattern = 
    disambiguate_pattern text prefix_len lexicon_status_ref in
  let disambiguate_reduction_kind = 
    disambiguate_reduction_kind text prefix_len lexicon_status_ref in
  let disambiguate_lazy_term = 
    disambiguate_lazy_term None text prefix_len lexicon_status_ref in
  let disambiguate_tactic metasenv tac =
   disambiguate_tactic lexicon_status_ref context metasenv goal (text,prefix_len,tac)
  in
  let disambiguate_auto_params m p = 
    disambiguate_auto_params disambiguate_term m context p
  in
   match tactic with
    (* Higher  order tactics *)
    | GrafiteAst.Progress (loc,tac) ->
        let metasenv,tac = disambiguate_tactic metasenv tac in
        metasenv,GrafiteAst.Progress (loc,tac)
    | GrafiteAst.Solve (loc,tacl) ->
        let metasenv,tacl =
         List.fold_right
          (fun tac (metasenv,tacl) ->
            let metasenv,tac = disambiguate_tactic metasenv tac in
             metasenv,tac::tacl
          ) tacl (metasenv,[])
        in
         metasenv,GrafiteAst.Solve (loc,tacl)
    | GrafiteAst.Try (loc,tac) ->
        let metasenv,tac = disambiguate_tactic metasenv tac in
        metasenv,GrafiteAst.Try (loc,tac)
    | GrafiteAst.First (loc,tacl) ->
        let metasenv,tacl =
         List.fold_right
          (fun tac (metasenv,tacl) ->
            let metasenv,tac = disambiguate_tactic metasenv tac in
             metasenv,tac::tacl
          ) tacl (metasenv,[])
        in
         metasenv,GrafiteAst.First (loc,tacl)
    | GrafiteAst.Seq (loc,tacl) ->
        let metasenv,tacl =
         List.fold_right
          (fun tac (metasenv,tacl) ->
            let metasenv,tac = disambiguate_tactic metasenv tac in
             metasenv,tac::tacl
          ) tacl (metasenv,[])
        in
         metasenv,GrafiteAst.Seq (loc,tacl)
    | GrafiteAst.Repeat (loc,tac) ->
        let metasenv,tac = disambiguate_tactic metasenv tac in
        metasenv,GrafiteAst.Repeat (loc,tac)
    | GrafiteAst.Do (loc,n,tac) ->
        let metasenv,tac = disambiguate_tactic metasenv tac in
        metasenv,GrafiteAst.Do (loc,n,tac)
    | GrafiteAst.Then (loc,tac,tacl) ->
        let metasenv,tac = disambiguate_tactic metasenv tac in
        let metasenv,tacl =
         List.fold_right
          (fun tac (metasenv,tacl) ->
            let metasenv,tac = disambiguate_tactic metasenv tac in
             metasenv,tac::tacl
          ) tacl (metasenv,[])
        in
         metasenv,GrafiteAst.Then (loc,tac,tacl)
    (* First order tactics *)
    | GrafiteAst.Absurd (loc, term) -> 
        let metasenv,cic = disambiguate_term context metasenv term in
        metasenv,GrafiteAst.Absurd (loc, cic)
    | GrafiteAst.Apply (loc, term) ->
        let metasenv,cic = disambiguate_term context metasenv term in
        metasenv,GrafiteAst.Apply (loc, cic)
    | GrafiteAst.ApplyRule (loc, term) ->
        let metasenv,cic = disambiguate_term_hint context metasenv term in
        metasenv,GrafiteAst.ApplyRule (loc, cic)
    | GrafiteAst.ApplyP (loc, term) ->
        let metasenv,cic = disambiguate_term context metasenv term in
        metasenv,GrafiteAst.ApplyP (loc, cic)
    | GrafiteAst.ApplyS (loc, term, params) ->
        let metasenv, params = disambiguate_auto_params metasenv params in
        let metasenv,cic = disambiguate_term context metasenv term in
        metasenv,GrafiteAst.ApplyS (loc, cic, params)
    | GrafiteAst.Assumption loc ->
        metasenv,GrafiteAst.Assumption loc
    | GrafiteAst.AutoBatch (loc,params) ->
        let metasenv, params = disambiguate_auto_params metasenv params in
        metasenv,GrafiteAst.AutoBatch (loc,params)
    | GrafiteAst.Cases (loc, what, pattern, idents) ->
        let metasenv,what = disambiguate_term context metasenv what in
        let pattern = disambiguate_pattern pattern in
        metasenv,GrafiteAst.Cases (loc, what, pattern, idents)
    | GrafiteAst.Change (loc, pattern, with_what) -> 
        let with_what = disambiguate_lazy_term with_what in
        let pattern = disambiguate_pattern pattern in
        metasenv,GrafiteAst.Change (loc, pattern, with_what)
    | GrafiteAst.Clear (loc,id) ->
        metasenv,GrafiteAst.Clear (loc,id)
    | GrafiteAst.ClearBody (loc,id) ->
       metasenv,GrafiteAst.ClearBody (loc,id)
    | GrafiteAst.Compose (loc, t1, t2, times, spec) ->
        let metasenv,t1 = disambiguate_term context metasenv t1 in
        let metasenv,t2 = 
          match t2 with
          | None -> metasenv, None
          | Some t2 -> 
              let m, t2 = disambiguate_term context metasenv t2 in
              m, Some t2
        in
        metasenv,   GrafiteAst.Compose (loc, t1, t2, times, spec)
    | GrafiteAst.Constructor (loc,n) ->
        metasenv,GrafiteAst.Constructor (loc,n)
    | GrafiteAst.Contradiction loc ->
        metasenv,GrafiteAst.Contradiction loc
    | GrafiteAst.Cut (loc, ident, term) -> 
        let metasenv,cic = disambiguate_term context metasenv term in
        metasenv,GrafiteAst.Cut (loc, ident, cic)
    | GrafiteAst.Decompose (loc, names) ->
         metasenv,GrafiteAst.Decompose (loc, names)
    | GrafiteAst.Demodulate (loc, params) ->
        let metasenv, params = disambiguate_auto_params metasenv params in
        metasenv,GrafiteAst.Demodulate (loc, params)
    | GrafiteAst.Destruct (loc, Some terms) ->
        let map term (metasenv, terms) =
           let metasenv, term = disambiguate_term context metasenv term in
           metasenv, term :: terms
        in
        let metasenv, terms = List.fold_right map terms (metasenv, []) in 
        metasenv, GrafiteAst.Destruct(loc, Some terms)
    | GrafiteAst.Destruct (loc, None) ->
        metasenv,GrafiteAst.Destruct(loc,None)
    | GrafiteAst.Exact (loc, term) -> 
        let metasenv,cic = disambiguate_term context metasenv term in
        metasenv,GrafiteAst.Exact (loc, cic)
    | GrafiteAst.Elim (loc, what, Some using, pattern, specs) ->
        let metasenv,what = disambiguate_term context metasenv what in
        let metasenv,using = disambiguate_term context metasenv using in
        let pattern = disambiguate_pattern pattern in
        metasenv,GrafiteAst.Elim (loc, what, Some using, pattern, specs)
    | GrafiteAst.Elim (loc, what, None, pattern, specs) ->
        let metasenv,what = disambiguate_term context metasenv what in
        let pattern = disambiguate_pattern pattern in
        metasenv,GrafiteAst.Elim (loc, what, None, pattern, specs)
    | GrafiteAst.ElimType (loc, what, Some using, specs) ->
        let metasenv,what = disambiguate_term context metasenv what in
        let metasenv,using = disambiguate_term context metasenv using in
        metasenv,GrafiteAst.ElimType (loc, what, Some using, specs)
    | GrafiteAst.ElimType (loc, what, None, specs) ->
        let metasenv,what = disambiguate_term context metasenv what in
        metasenv,GrafiteAst.ElimType (loc, what, None, specs)
    | GrafiteAst.Exists loc ->
        metasenv,GrafiteAst.Exists loc 
    | GrafiteAst.Fail loc ->
        metasenv,GrafiteAst.Fail loc
    | GrafiteAst.Fold (loc,red_kind, term, pattern) ->
        let pattern = disambiguate_pattern pattern in
        let term = disambiguate_lazy_term term in
        let red_kind = disambiguate_reduction_kind red_kind in
        metasenv,GrafiteAst.Fold (loc, red_kind, term, pattern)
    | GrafiteAst.FwdSimpl (loc, hyp, names) ->
       metasenv,GrafiteAst.FwdSimpl (loc, hyp, names)  
    | GrafiteAst.Fourier loc ->
       metasenv,GrafiteAst.Fourier loc
    | GrafiteAst.Generalize (loc,pattern,ident) ->
        let pattern = disambiguate_pattern pattern in
        metasenv,GrafiteAst.Generalize (loc,pattern,ident)
    | GrafiteAst.IdTac loc ->
        metasenv,GrafiteAst.IdTac loc
    | GrafiteAst.Intros (loc, specs) ->
        metasenv,GrafiteAst.Intros (loc, specs)
    | GrafiteAst.Inversion (loc, term) ->
       let metasenv,term = disambiguate_term context metasenv term in
        metasenv,GrafiteAst.Inversion (loc, term)
    | GrafiteAst.LApply (loc, linear, depth, to_what, what, ident) ->
       let f term (metasenv, to_what) =
          let metasenv, term = disambiguate_term context metasenv term in
          metasenv, term :: to_what
       in
       let metasenv, to_what = List.fold_right f to_what (metasenv, []) in 
       let metasenv, what = disambiguate_term context metasenv what in
       metasenv,GrafiteAst.LApply (loc, linear, depth, to_what, what, ident)
    | GrafiteAst.Left loc ->
       metasenv,GrafiteAst.Left loc
    | GrafiteAst.LetIn (loc, term, name) ->
        let metasenv,term = disambiguate_term context metasenv term in
        metasenv,GrafiteAst.LetIn (loc,term,name)
    | GrafiteAst.Reduce (loc, red_kind, pattern) ->
        let pattern = disambiguate_pattern pattern in
        let red_kind = disambiguate_reduction_kind red_kind in
        metasenv,GrafiteAst.Reduce(loc, red_kind, pattern)
    | GrafiteAst.Reflexivity loc ->
        metasenv,GrafiteAst.Reflexivity loc
    | GrafiteAst.Replace (loc, pattern, with_what) -> 
        let pattern = disambiguate_pattern pattern in
        let with_what = disambiguate_lazy_term with_what in
        metasenv,GrafiteAst.Replace (loc, pattern, with_what)
    | GrafiteAst.Rewrite (loc, dir, t, pattern, names) ->
        let metasenv,term = disambiguate_term context metasenv t in
        let pattern = disambiguate_pattern pattern in
        metasenv,GrafiteAst.Rewrite (loc, dir, term, pattern, names)
    | GrafiteAst.Right loc ->
        metasenv,GrafiteAst.Right loc
    | GrafiteAst.Ring loc ->
        metasenv,GrafiteAst.Ring loc
    | GrafiteAst.Split loc ->
        metasenv,GrafiteAst.Split loc
    | GrafiteAst.Symmetry loc ->
        metasenv,GrafiteAst.Symmetry loc
    | GrafiteAst.Transitivity (loc, term) -> 
        let metasenv,cic = disambiguate_term context metasenv term in
        metasenv,GrafiteAst.Transitivity (loc, cic)
      (* Nuovi casi *)
    | GrafiteAst.Assume (loc, id, term) -> 
        let metasenv,cic = disambiguate_term context metasenv term in
        metasenv,GrafiteAst.Assume (loc, id, cic)
    | GrafiteAst.Suppose (loc, term, id, term') ->
        let metasenv,cic = disambiguate_term context metasenv term in
        let metasenv,cic' =
           match term' with
              None -> metasenv,None
            | Some t ->
                  let metasenv,t = disambiguate_term context metasenv t in
                  metasenv,Some t in
        metasenv,GrafiteAst.Suppose (loc, cic, id, cic')
    | GrafiteAst.Bydone (loc,just) ->
        let metasenv,just =
         disambiguate_just disambiguate_term context metasenv just
        in
         metasenv,GrafiteAst.Bydone (loc, just)
    | GrafiteAst.We_need_to_prove (loc,term,id,term') ->
        let metasenv,cic = disambiguate_term context metasenv term in
        let metasenv,cic' = 
            match term' with
              None -> metasenv,None
            | Some t ->
                  let metasenv,t = disambiguate_term context metasenv t in
                  metasenv,Some t in
        metasenv,GrafiteAst.We_need_to_prove (loc,cic,id,cic')
    | GrafiteAst.By_just_we_proved (loc,just,term',id,term'') ->
        let metasenv,just =
         disambiguate_just disambiguate_term context metasenv just in
        let metasenv,cic' = disambiguate_term context metasenv term' in
        let metasenv,cic'' = 
            match term'' with
              None -> metasenv,None
           |  Some t ->  
                    let metasenv,t = disambiguate_term context metasenv t in
                     metasenv,Some t in
        metasenv,GrafiteAst.By_just_we_proved (loc,just,cic',id,cic'')
    | GrafiteAst.We_proceed_by_cases_on (loc, term, term') ->
        let metasenv,cic = disambiguate_term context metasenv term in
        let metasenv,cic' = disambiguate_term context metasenv term' in
        metasenv,GrafiteAst.We_proceed_by_cases_on (loc, cic, cic')
    | GrafiteAst.We_proceed_by_induction_on (loc, term, term') ->
        let metasenv,cic = disambiguate_term context metasenv term in
        let metasenv,cic' = disambiguate_term context metasenv term' in
        metasenv,GrafiteAst.We_proceed_by_induction_on (loc, cic, cic')
   | GrafiteAst.Byinduction (loc, term, id) ->
        let metasenv,cic = disambiguate_term context metasenv term in
        metasenv,GrafiteAst.Byinduction(loc, cic, id)
   | GrafiteAst.Thesisbecomes (loc, term) ->
        let metasenv,cic = disambiguate_term context metasenv term in
        metasenv,GrafiteAst.Thesisbecomes (loc, cic)
   | GrafiteAst.ExistsElim (loc, just, id1, term1, id2, term2) ->
        let metasenv,just =
         disambiguate_just disambiguate_term context metasenv just in
        let metasenv,cic' = disambiguate_term context metasenv term1 in
        let cic''= disambiguate_lazy_term term2 in
        metasenv,GrafiteAst.ExistsElim(loc, just, id1, cic', id2, cic'')
   | GrafiteAst.AndElim (loc, just, id, term1, id1, term2) ->
        let metasenv,just =
         disambiguate_just disambiguate_term context metasenv just in
        let metasenv,cic'= disambiguate_term context metasenv term1 in
        let metasenv,cic''= disambiguate_term context metasenv term2 in
        metasenv,GrafiteAst.AndElim(loc, just, id, cic', id1, cic'')   
   | GrafiteAst.Case (loc, id, params) ->
        let metasenv,params' =
         List.fold_right
          (fun (id,term) (metasenv,params) ->
            let metasenv,cic = disambiguate_term context metasenv term in
             metasenv,(id,cic)::params
          ) params (metasenv,[])
        in
        metasenv,GrafiteAst.Case(loc, id, params')   
   | GrafiteAst.RewritingStep (loc, term1, term2, term3, cont) ->
        let metasenv,cic =
         match term1 with
            None -> metasenv,None
          | Some (start,t) -> 
             let metasenv,t = disambiguate_term context metasenv t in
              metasenv,Some (start,t) in
        let metasenv,cic'= disambiguate_term context metasenv term2 in
        let metasenv,cic'' =
         match term3 with
          | `SolveWith term ->
             let metasenv,term = disambiguate_term context metasenv term in
             metasenv, `SolveWith term
          | `Auto params -> 
              let metasenv, params = disambiguate_auto_params metasenv params in
              metasenv,`Auto params
          | `Term t -> 
             let metasenv,t = disambiguate_term context metasenv t in
              metasenv,`Term t
          | `Proof as t -> metasenv,t in
        metasenv,GrafiteAst.RewritingStep (loc, cic, cic', cic'', cont)   

let disambiguate_obj estatus ?baseuri metasenv (text,prefix_len,obj) =
  let uri =
   let baseuri = 
     match baseuri with Some x -> x | None -> raise BaseUriNotSetYet
   in
   let name = 
     match obj with
     | CicNotationPt.Inductive (_,(name,_,_,_)::_)
     | CicNotationPt.Record (_,name,_,_) -> name ^ ".ind"
     | CicNotationPt.Theorem (_,name,_,_,_) -> name ^ ".con"
     | CicNotationPt.Inductive _ -> assert false
   in
     UriManager.uri_of_string (baseuri ^ "/" ^ name)
  in
(*
 let _try_new cic =
  (NCicLibrary.clear_cache ();
   NCicEnvironment.invalidate ();
   OCic2NCic.clear ();
   let graph = 
     match cic with
     | Some (Cic.CurrentProof (_,metasenv, _, ty,_,_)) ->
         let _, ugraph = 
           CicTypeChecker.type_of_aux' metasenv [] ty CicUniv.empty_ugraph
         in
           ugraph
     | Some (Cic.Constant (_,_, ty,_,_)) ->
         let _, ugraph = 
                 CicTypeChecker.type_of_aux' [] [] ty CicUniv.empty_ugraph
         in
           ugraph
     | _ -> CicUniv.empty_ugraph
   in

(*
   prerr_endline "PRIMA COERCIONS";
   let _,l = CicUniv.do_rank graph in
   List.iter (fun k -> 
     prerr_endline (CicUniv.string_of_universe k ^ " = " ^ string_of_int
     (CicUniv.get_rank k))) l;
*)

   let graph =
       List.fold_left 
         (fun graph (_,_,l) ->
           List.fold_left
             (fun graph (uri,_,_) ->
                let _,g = CicTypeChecker.typecheck uri in
                CicUniv.merge_ugraphs ~base_ugraph:graph ~increment:(g,uri))
             graph l)
       graph (CoercDb.to_list (CoercDb.dump ()))
   in
   ignore(CicUniv.do_rank graph);


(*
   prerr_endline "DOPO COERCIONS";
   let _,l = CicUniv.do_rank graph in
   List.iter (fun k -> 
     prerr_endline (CicUniv.string_of_universe k ^ " = " ^ string_of_int
     (CicUniv.get_rank k))) l;
*)


   prerr_endline "INIZIO NUOVA DISAMBIGUAZIONE";
   let time = Unix.gettimeofday () in
       (try
         (match 
          NCicDisambiguate.disambiguate_obj
           ~rdb:estatus
           ~lookup_in_library:nlookup_in_library
           ~description_of_alias:LexiconAst.description_of_alias
           ~mk_choice:ncic_mk_choice
           ~mk_implicit
           ~uri:(OCic2NCic.nuri_of_ouri uri)
           ~aliases:estatus#lstatus.LexiconEngine.aliases
           ~universe:(Some estatus#lstatus.LexiconEngine.multi_aliases)
           (text,prefix_len,obj)
         with
         | [_,_,_,obj],_ ->
          let time = Unix.gettimeofday () -. time in
(*           NCicTypeChecker.typecheck_obj obj; *)
          prerr_endline ("NUOVA DISAMBIGUAZIONE OK: "^ string_of_float time);
(*
          let obj = 
            let u,i,m,_,o = obj in
            u,i,m,[],o
          in
*)
          prerr_endline (NCicPp.ppobj obj)
         | _ ->
          prerr_endline ("NUOVA DISAMBIGUAZIONE AMBIGUO!!!!!!!!!  "))
       with 
       | MultiPassDisambiguator.DisambiguationError (_,s) ->
        prerr_endline ("ERRORE NUOVA DISAMBIGUAZIONE ("
          ^UriManager.string_of_uri uri^
          "):\n" ^
         String.concat "\n" 
          (List.map (fun _,_,x,_ -> snd (Lazy.force x)) (List.flatten s)))
(*        | exn -> prerr_endline (Printexc.to_string exn) *)
       )
  )
 in 
*)


 try
(*   let time = Unix.gettimeofday () in  *)


  let (diff, metasenv, _, cic, _) =
    singleton "third"
      (CicDisambiguate.disambiguate_obj 
        ~lookup_in_library 
        ~mk_choice:cic_mk_choice
        ~mk_implicit ~fix_instance
        ~description_of_alias:LexiconAst.description_of_alias
        ~aliases:estatus#lstatus.LexiconEngine.aliases
        ~universe:(Some estatus#lstatus.LexiconEngine.multi_aliases) 
        ~uri:(Some uri)
        (text,prefix_len,obj)) 
  in


(*
  let time = Unix.gettimeofday () -. time in
  prerr_endline ("VECCHIA DISAMBIGUAZIONE ("^
    UriManager.string_of_uri uri ^"): " ^ string_of_float time);
*)
(*    try_new (Some cic);   *)


  let estatus = LexiconEngine.set_proof_aliases estatus diff in
   estatus, metasenv, cic

 with 
 | Sys.Break as exn -> raise exn
 | exn ->
(*    try_new None; *)
   raise exn
;;

let disambiguate_nobj estatus ?baseuri (text,prefix_len,obj) =
  let uri =
   let baseuri = 
     match baseuri with Some x -> x | None -> raise BaseUriNotSetYet
   in
   let name = 
     match obj with
     | CicNotationPt.Inductive (_,(name,_,_,_)::_)
     | CicNotationPt.Record (_,name,_,_) -> name ^ ".ind"
     | CicNotationPt.Theorem (_,name,_,_,_) -> name ^ ".con"
     | CicNotationPt.Inductive _ -> assert false
   in
     UriManager.uri_of_string (baseuri ^ "/" ^ name)
  in
  let diff, _, _, cic =
   singleton "third"
    (NCicDisambiguate.disambiguate_obj
      ~lookup_in_library:nlookup_in_library
      ~description_of_alias:LexiconAst.description_of_alias
      ~mk_choice:ncic_mk_choice
      ~mk_implicit ~fix_instance
      ~uri:(OCic2NCic.nuri_of_ouri uri)
      ~rdb:estatus
      ~aliases:estatus#lstatus.LexiconEngine.aliases
      ~universe:(Some estatus#lstatus.LexiconEngine.multi_aliases) 
      (text,prefix_len,obj)) in
  let estatus = LexiconEngine.set_proof_aliases estatus diff in
   estatus, cic
;;
  
let disambiguate_command estatus ?baseuri metasenv (text,prefix_len,cmd)=
  match cmd with
   | GrafiteAst.Index(loc,key,uri) ->
       let lexicon_status_ref = ref estatus in 
       let disambiguate_term =
         disambiguate_term None text prefix_len lexicon_status_ref [] in
       let disambiguate_term_option metasenv =
         function
             None -> metasenv,None
           | Some t ->
               let metasenv,t = disambiguate_term metasenv t in
                 metasenv, Some t
       in
       let metasenv,key = disambiguate_term_option metasenv key in
        !lexicon_status_ref,metasenv,GrafiteAst.Index(loc,key,uri)
   | GrafiteAst.Select (loc,uri) -> 
        estatus, metasenv, GrafiteAst.Select(loc,uri)
   | GrafiteAst.Pump(loc,i) -> 
        estatus, metasenv, GrafiteAst.Pump(loc,i)
   | GrafiteAst.PreferCoercion (loc,t) -> 
       let lexicon_status_ref = ref estatus in 
       let disambiguate_term =
         disambiguate_term None text prefix_len lexicon_status_ref [] in
      let metasenv,t = disambiguate_term metasenv t in
       !lexicon_status_ref, metasenv, GrafiteAst.PreferCoercion (loc,t)
   | GrafiteAst.Coercion (loc,t,b,a,s) -> 
       let lexicon_status_ref = ref estatus in 
       let disambiguate_term =
         disambiguate_term None text prefix_len lexicon_status_ref [] in
      let metasenv,t = disambiguate_term metasenv t in
       !lexicon_status_ref, metasenv, GrafiteAst.Coercion (loc,t,b,a,s)
   | GrafiteAst.Inverter (loc,n,indty,params) ->
       let lexicon_status_ref = ref estatus in
       let disambiguate_term = 
         disambiguate_term None text prefix_len lexicon_status_ref [] in
       let metasenv,indty = disambiguate_term metasenv indty in
        !lexicon_status_ref, metasenv, GrafiteAst.Inverter (loc,n,indty,params)
   | GrafiteAst.Default _
   | GrafiteAst.Drop _
   | GrafiteAst.Include _
   | GrafiteAst.Print _
   | GrafiteAst.Qed _
   | GrafiteAst.Set _ as cmd ->
       estatus,metasenv,cmd
   | GrafiteAst.Obj (loc,obj) ->
       let estatus,metasenv,obj =
        disambiguate_obj estatus ?baseuri metasenv (text,prefix_len,obj)in
       estatus, metasenv, GrafiteAst.Obj (loc,obj)
   | GrafiteAst.Relation (loc,id,a,aeq,refl,sym,trans) ->
      let lexicon_status_ref = ref estatus in 
      let disambiguate_term =
       disambiguate_term None text prefix_len lexicon_status_ref [] in
      let disambiguate_term_option metasenv =
       function
          None -> metasenv,None
       | Some t ->
          let metasenv,t = disambiguate_term metasenv t in
           metasenv, Some t
      in
      let metasenv,a = disambiguate_term metasenv a in
      let metasenv,aeq = disambiguate_term metasenv aeq in
      let metasenv,refl = disambiguate_term_option metasenv refl in
      let metasenv,sym = disambiguate_term_option metasenv sym in
      let metasenv,trans = disambiguate_term_option metasenv trans in
       !lexicon_status_ref, metasenv,
        GrafiteAst.Relation (loc,id,a,aeq,refl,sym,trans)

let disambiguate_macro 
  lexicon_status_ref metasenv context (text,prefix_len, macro) 
=
 let disambiguate_term = disambiguate_term None text prefix_len lexicon_status_ref in
  let disambiguate_reduction_kind = 
    disambiguate_reduction_kind text prefix_len lexicon_status_ref in
  match macro with
   | GrafiteAst.WMatch (loc,term) ->
      let metasenv,term = disambiguate_term context metasenv term in
       metasenv,GrafiteAst.WMatch (loc,term)
   | GrafiteAst.WInstance (loc,term) ->
      let metasenv,term = disambiguate_term context metasenv term in
       metasenv,GrafiteAst.WInstance (loc,term)
   | GrafiteAst.WElim (loc,term) ->
      let metasenv,term = disambiguate_term context metasenv term in
       metasenv,GrafiteAst.WElim (loc,term)
   | GrafiteAst.WHint (loc,term) ->
      let metasenv,term = disambiguate_term context metasenv term in
       metasenv,GrafiteAst.WHint (loc,term)
   | GrafiteAst.Check (loc,term) ->
      let metasenv,term = disambiguate_term context metasenv term in
       metasenv,GrafiteAst.Check (loc,term)
   | GrafiteAst.Eval (loc,kind,term) ->
      let metasenv, term = disambiguate_term context metasenv term in
      let kind = disambiguate_reduction_kind kind in
       metasenv,GrafiteAst.Eval (loc,kind,term)
   | GrafiteAst.AutoInteractive (loc, params) -> 
      let metasenv, params = 
        disambiguate_auto_params disambiguate_term metasenv context params in
      metasenv, GrafiteAst.AutoInteractive (loc, params)
   | GrafiteAst.Hint _
   | GrafiteAst.WLocate _
   | GrafiteAst.Inline _ as macro ->
      metasenv,macro
