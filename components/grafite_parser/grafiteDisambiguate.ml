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
        ~term_of_uri:(fun _ -> assert false)
        ~term_of_nref:(fun nref -> NCic.Const nref)
       name dsc
  | LexiconAst.Number_alias (_, dsc) -> 
     let desc,f = DisambiguateChoices.nlookup_num_by_dsc dsc in
      desc, `Num_interp
       (fun num -> match f with `Num_interp f -> f num | _ -> assert false)
  | LexiconAst.Ident_alias (name, uri) -> 
     uri, `Sym_interp 
      (fun l->assert(l = []);
        let nref = NReference.reference_of_string uri in
         NCic.Const nref)
;;


let mk_implicit b =
  match b with
  | false -> 
      LexiconAst.Symbol_alias (__Implicit,-1,"Fake Implicit")
  | true -> 
      LexiconAst.Symbol_alias (__Closed_Implicit,-1,"Fake Closed Implicit")
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
         ) references
      with
       NCicEnvironment.ObjectNotFound _ -> [])
  | _ -> []
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
  | `Unfold (Some t) -> assert false (* MATITA 1.0 *)
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
     NUri.uri_of_string (baseuri ^ "/" ^ name)
  in
  let diff, _, _, cic =
   singleton "third"
    (NCicDisambiguate.disambiguate_obj
      ~lookup_in_library:nlookup_in_library
      ~description_of_alias:LexiconAst.description_of_alias
      ~mk_choice:ncic_mk_choice
      ~mk_implicit ~fix_instance
      ~uri
      ~rdb:estatus
      ~aliases:estatus#lstatus.LexiconEngine.aliases
      ~universe:(Some estatus#lstatus.LexiconEngine.multi_aliases) 
      (text,prefix_len,obj)) in
  let estatus = LexiconEngine.set_proof_aliases estatus diff in
   estatus, cic
;;
let disambiguate_command estatus ?baseuri (text,prefix_len,cmd)=
  match cmd with
   | GrafiteAst.Index(loc,key,uri) -> (* MATITA 1.0 *) assert false
   | GrafiteAst.Select (loc,uri) -> 
        estatus, GrafiteAst.Select(loc,uri)
   | GrafiteAst.PreferCoercion (loc,t) -> (* MATITA 1.0 *) assert false
   | GrafiteAst.Coercion (loc,t,b,a,s) -> (* MATITA 1.0 *) assert false
   | GrafiteAst.Inverter (loc,n,indty,params) -> (* MATITA 1.0 *) assert false
   | GrafiteAst.Default _
   | GrafiteAst.Drop _
   | GrafiteAst.Include _
   | GrafiteAst.Print _
   | GrafiteAst.Qed _
   | GrafiteAst.Set _ as cmd ->
       estatus,cmd
   | GrafiteAst.Obj (loc,obj) -> (* MATITA 1.0 *) assert false
   | GrafiteAst.Relation (loc,id,a,aeq,refl,sym,trans) -> (* MATITA 1.0 *) assert false
