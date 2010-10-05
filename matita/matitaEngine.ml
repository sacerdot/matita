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

module G = GrafiteAst

let debug = false ;;
let debug_print = if debug then prerr_endline else ignore ;;

let disambiguate_command lexicon_status_ref grafite_status cmd =
 let baseuri = grafite_status#baseuri in
 let lexicon_status,metasenv,cmd =
  GrafiteDisambiguate.disambiguate_command ~baseuri
   !lexicon_status_ref (GrafiteTypes.get_proof_metasenv grafite_status) cmd
 in
  lexicon_status_ref := lexicon_status;
  GrafiteTypes.set_metasenv metasenv grafite_status,cmd

let eval_macro_screenshot (status : GrafiteTypes.status) name =
  let _,_,metasenv,subst,_ = status#obj in
  let sequent = List.hd metasenv in
  let mathml = 
    ApplyTransformation.nmml_of_cic_sequent 
      status metasenv subst sequent 
  in
  let domImpl = Gdome.domImplementation () in
  ignore(domImpl#saveDocumentToFile 
    ~name:(name^".xml") ~doc:mathml ());
  ignore(Sys.command ("mathmlsvg --verbose=1 --font-size=20 --cut-filename=no " ^ 
    Filename.quote (name^".xml")));
  ignore(Sys.command ("convert " ^ 
    Filename.quote (name^".svg") ^ " " ^ 
    Filename.quote (name^".png")));
  HLog.debug ("generated " ^ name ^ ".png");
  status, `New []
;;

let eval_ast ?do_heavy_checks status (text,prefix_len,ast) =
 let dump = not (Helm_registry.get_bool "matita.moo") in
 let lexicon_status_ref = ref (status :> LexiconEngine.status) in
 let baseuri = status#baseuri in
 let new_status,new_objs =
  match ast with 
     | G.Executable (_, G.Command (_, G.Coercion _)) when dump ->
(* FG: some commands can not be executed when mmas are parsed *************)
(* To be removed when mmas will be executed                               *)
        status, `Old []
     | ast -> 
  GrafiteEngine.eval_ast
   ~disambiguate_tactic:((* MATITA 1.0*) fun _ -> assert false)
   ~disambiguate_command:(disambiguate_command lexicon_status_ref)
   ~disambiguate_macro:((* MATITA 1.0*) fun _ -> assert false)
   ?do_heavy_checks status (text,prefix_len,ast)
 in
 let new_status =
  if !lexicon_status_ref#lstatus != status#lstatus then
   new_status#set_lstatus (!lexicon_status_ref#lstatus)
  else
   new_status in
 let new_status = LexiconSync.add_aliases_for_objs new_status new_objs in
 let new_aliases = LexiconSync.alias_diff ~from:status new_status in
 let _,intermediate_states = 
  List.fold_left
   (fun (status,acc) (k,value) -> 
     let v = LexiconAst.description_of_alias value in
     let b =
      try
       (* this hack really sucks! *)
       UriManager.buri_of_uri (UriManager.uri_of_string v) = baseuri
      with
       UriManager.IllFormedUri _ ->
        try
         (* this too! *)
         let NReference.Ref (uri,_) = NReference.reference_of_string v in
         let ouri = NCic2OCic.ouri_of_nuri uri in
          UriManager.buri_of_uri ouri = baseuri
        with
         NReference.IllFormedReference _ ->
          false (* v is a description, not a URI *)
     in
      if b then 
       status,acc
      else
       let new_status =
        LexiconEngine.set_proof_aliases status [k,value]
       in
        new_status, (new_status ,Some (k,value))::acc
   ) (status,[]) new_aliases
 in
  ((new_status),None)::intermediate_states
;;

exception TryingToAdd of string
exception EnrichedWithStatus of exn * GrafiteTypes.status

let eval_from_stream ~first_statement_only ~include_paths 
 ?do_heavy_checks ?(enforce_no_new_aliases=true)
 ?(watch_statuses=fun _ -> ()) status str cb 
=
 let matita_debug = Helm_registry.get_bool "matita.debug" in
 let rec loop status statuses =
  let loop =
   if first_statement_only then fun _ statuses -> statuses
   else loop
  in
  let stop,g,s = 
   try
     let cont =
       try Some (GrafiteParser.parse_statement ~include_paths str status)
       with End_of_file -> None in
     match cont with
     | None -> true, status, statuses
     | Some (status,ast) ->
       (match ast with
           GrafiteParser.LNone _ ->
            watch_statuses status ;
            false, status, ((status,None)::statuses)
         | GrafiteParser.LSome ast ->
            cb status ast;
            let new_statuses = eval_ast ?do_heavy_checks status ("",0,ast) in
            if enforce_no_new_aliases then
             List.iter 
              (fun (_,alias) ->
                match alias with
                  None -> ()
                | Some (k,value) ->
                   let newtxt = LexiconAstPp.pp_alias value in
                    raise (TryingToAdd newtxt)) new_statuses;
            let status =
             match new_statuses with
                [] -> assert false
              | (s,_)::_ -> s
            in
             watch_statuses status ;
             false, status, (new_statuses @ statuses))
   with exn when not matita_debug ->
     raise (EnrichedWithStatus (exn, status))
  in
  if stop then s else loop g s
 in
  loop status []
;;
