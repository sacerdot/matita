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

open Printf

let debug = false ;;
let debug_print = if debug then prerr_endline else ignore ;;

let disambiguate_tactic text prefix_len lexicon_status_ref grafite_status goal tac =
 let metasenv,tac =
  GrafiteDisambiguate.disambiguate_tactic
   lexicon_status_ref
   (GrafiteTypes.get_proof_context grafite_status goal)
   (GrafiteTypes.get_proof_metasenv grafite_status)
   tac
 in
  GrafiteTypes.set_metasenv metasenv grafite_status,tac

let disambiguate_command lexicon_status_ref grafite_status cmd =
 let baseuri = GrafiteTypes.get_baseuri grafite_status in
 let lexicon_status,metasenv,cmd =
  GrafiteDisambiguate.disambiguate_command ~baseuri
   !lexicon_status_ref (GrafiteTypes.get_proof_metasenv grafite_status) cmd
 in
  lexicon_status_ref := lexicon_status;
  GrafiteTypes.set_metasenv metasenv grafite_status,cmd

let disambiguate_macro lexicon_status_ref grafite_status macro context =
 let metasenv,macro =
  GrafiteDisambiguate.disambiguate_macro
   lexicon_status_ref
   (GrafiteTypes.get_proof_metasenv grafite_status)
   context macro
 in
  GrafiteTypes.set_metasenv metasenv grafite_status,macro

let eval_ast ?do_heavy_checks lexicon_status
 grafite_status (text,prefix_len,ast)
=
 let lexicon_status_ref = ref lexicon_status in
 let baseuri = GrafiteTypes.get_baseuri grafite_status in
 let new_grafite_status,new_objs =
  GrafiteEngine.eval_ast
   ~disambiguate_tactic:(disambiguate_tactic text prefix_len lexicon_status_ref)
   ~disambiguate_command:(disambiguate_command lexicon_status_ref)
   ~disambiguate_macro:(disambiguate_macro lexicon_status_ref)
   ?do_heavy_checks grafite_status (text,prefix_len,ast) in
 let new_lexicon_status =
  LexiconSync.add_aliases_for_objs !lexicon_status_ref new_objs in
 let new_aliases =
  LexiconSync.alias_diff ~from:lexicon_status new_lexicon_status in
 let _,intermediate_states = 
  List.fold_left
   (fun (lexicon_status,acc) (k,((v,_) as value)) -> 
     let b =
      try
       (* this hack really sucks! *)
       UriManager.buri_of_uri (UriManager.uri_of_string v) = 
       baseuri
      with
       UriManager.IllFormedUri _ -> false (* v is a description, not a URI *)
     in
      if b then 
       lexicon_status,acc
      else

       let new_lexicon_status =
        LexiconEngine.set_proof_aliases lexicon_status [k,value]
       in
        new_lexicon_status,
         ((grafite_status,new_lexicon_status),Some (k,value))::acc
   ) (lexicon_status,[]) new_aliases
 in
  ((new_grafite_status,new_lexicon_status),None)::intermediate_states

exception TryingToAdd of string
exception EnrichedWithLexiconStatus of exn * LexiconEngine.status

let out = ref ignore 

let set_callback f = out := f

let eval_from_stream ~first_statement_only ~include_paths 
 ?do_heavy_checks ?(enforce_no_new_aliases=true)
 ?(watch_statuses=fun _ _ -> ()) lexicon_status grafite_status str cb 
=
 let rec loop lexicon_status grafite_status statuses =
  let loop =
   if first_statement_only then fun _ _ statuses -> statuses
   else loop
  in
  let stop,l,g,s = 
   try
     let cont =
       try
         Some (GrafiteParser.parse_statement ~include_paths str lexicon_status)
       with
         End_of_file -> None
     in
     match cont with
     | None -> true, lexicon_status, grafite_status, statuses
     | Some (lexicon_status,ast) ->
       (match ast with
           GrafiteParser.LNone _ ->
            watch_statuses lexicon_status grafite_status ;
            false, lexicon_status, grafite_status,
             (((grafite_status,lexicon_status),None)::statuses)
         | GrafiteParser.LSome ast ->
            !out ast;
            cb grafite_status ast;
            let new_statuses =
             eval_ast ?do_heavy_checks lexicon_status
              grafite_status ("",0,ast) in
            if enforce_no_new_aliases then
             List.iter 
              (fun (_,alias) ->
                match alias with
                  None -> ()
                | Some (k,((v,_) as value)) ->
                   let newtxt =
                    DisambiguatePp.pp_environment
                     (DisambiguateTypes.Environment.add k value
                       DisambiguateTypes.Environment.empty)
                   in
                    raise (TryingToAdd newtxt)) new_statuses;
            let grafite_status,lexicon_status =
             match new_statuses with
                [] -> assert false
              | (s,_)::_ -> s
            in
             watch_statuses lexicon_status grafite_status ;
             false, lexicon_status, grafite_status, (new_statuses @ statuses))
   with exn when (not (Helm_registry.get_bool "matita.debug")) ->
     raise (EnrichedWithLexiconStatus (exn, lexicon_status))
  in
  if stop then s else loop l g s
 in
  loop lexicon_status grafite_status []
;;
