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

let disambiguate_tactic lexicon_status_ref grafite_status goal tac =
 let metasenv,tac =
  GrafiteDisambiguate.disambiguate_tactic
   lexicon_status_ref
   (GrafiteTypes.get_proof_context grafite_status goal)
   (GrafiteTypes.get_proof_metasenv grafite_status)
   tac
 in
  GrafiteTypes.set_metasenv metasenv grafite_status,tac

let disambiguate_command lexicon_status_ref grafite_status cmd =
 let lexicon_status,metasenv,cmd =
  GrafiteDisambiguate.disambiguate_command
   ~baseuri:(
     try
      Some (GrafiteTypes.get_string_option grafite_status "baseuri")
     with
      GrafiteTypes.Option_error _ -> None)
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

let eval_ast ?do_heavy_checks ?clean_baseuri lexicon_status
 grafite_status ast
=
 let lexicon_status_ref = ref lexicon_status in
 let new_grafite_status,new_objs =
  GrafiteEngine.eval_ast
   ~disambiguate_tactic:(disambiguate_tactic lexicon_status_ref)
   ~disambiguate_command:(disambiguate_command lexicon_status_ref)
   ~disambiguate_macro:(disambiguate_macro lexicon_status_ref)
   ?do_heavy_checks ?clean_baseuri grafite_status ast in
 let new_lexicon_status =
  LexiconSync.add_aliases_for_objs !lexicon_status_ref new_objs in
 let new_aliases =
  LexiconSync.alias_diff ~from:lexicon_status new_lexicon_status in
 let _,intermediate_states = 
  let baseuri = GrafiteTypes.get_string_option new_grafite_status "baseuri" in
  List.fold_left
   (fun (lexicon_status,acc) (k,((v,_) as value)) -> 
     let b =
      try
       UriManager.buri_of_uri (UriManager.uri_of_string v) = baseuri
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

let eval_from_stream ~first_statement_only ~include_paths ?(prompt=false)
 ?do_heavy_checks ?clean_baseuri lexicon_status grafite_status str cb 
=
 let rec loop lexicon_status grafite_status statuses =
  let loop =
   if first_statement_only then
    fun _ _ _ -> raise End_of_file
   else
    loop
  in
   if prompt then (print_string "matita> "; flush stdout);
   try
    let lexicon_status,ast =
     GrafiteParser.parse_statement ~include_paths str lexicon_status
    in
     (match ast with
         GrafiteParser.LNone _ ->
          loop lexicon_status grafite_status
           (((grafite_status,lexicon_status),None)::statuses)
       | GrafiteParser.LSome ast ->
          cb grafite_status ast;
          let new_statuses =
           eval_ast ?do_heavy_checks ?clean_baseuri lexicon_status
            grafite_status ast in
          let grafite_status,lexicon_status =
           match new_statuses with
              [] -> assert false
            | (s,_)::_ -> s
          in
           loop lexicon_status grafite_status (new_statuses @ statuses))
   with
    End_of_file -> statuses
 in
  loop lexicon_status grafite_status []
;;

let eval_string ~first_statement_only ~include_paths ?do_heavy_checks
 ?clean_baseuri lexicon_status status str
=
 eval_from_stream ~first_statement_only ~include_paths ?do_heavy_checks
  ?clean_baseuri lexicon_status status (Ulexing.from_utf8_string str)
  (fun _ _ -> ())
