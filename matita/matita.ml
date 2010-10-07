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

open MatitaGtkMisc
open GrafiteTypes

(** {2 Initialization} *)

let _ = 
  MatitaInit.add_cmdline_spec
    ["-tptppath",Arg.String 
      (fun s -> Helm_registry.set_string "matita.tptppath" s),
      "Where to find the Axioms/ and Problems/ directory"];
  MatitaInit.initialize_all ()
;;

(* let _ = Saturation.init () (* ALB to link paramodulation *) *)

(** {2 GUI callbacks} *)

let gui = MatitaGui.instance ()

let script =
  let s = 
    MatitaScript.script 
      ~source_view:gui#sourceView
      ~mathviewer:(MatitaMathView.mathViewer ())
      ~urichooser:(fun uris ->
        try
          MatitaGui.interactive_uri_choice ~selection_mode:`SINGLE
          ~title:"Matita: URI chooser" 
          ~msg:"Select the URI" ~hide_uri_entry:true
          ~hide_try:true ~ok_label:"_Apply" ~ok_action:`SELECT
          ~copy_cb:(fun s -> gui#sourceView#buffer#insert ("\n"^s^"\n"))
          () ~id:"boh?" uris
        with MatitaTypes.Cancel -> [])
      ~set_star:gui#setStar
      ~ask_confirmation:
        (fun ~title ~message -> 
            MatitaGtkMisc.ask_confirmation ~title ~message 
            ~parent:gui#main#toplevel ())
      ()
  in
  Predefined_virtuals.load_predefined_virtuals ();
  Predefined_virtuals.load_predefined_classes ();
  gui#sourceView#source_buffer#begin_not_undoable_action ();
  s#reset (); 
  s#template (); 
  gui#sourceView#source_buffer#end_not_undoable_action ();
  s
  
  (* math viewers *)
let _ =
  let cic_math_view = MatitaMathView.cicMathView_instance () in
  let sequents_viewer = MatitaMathView.sequentsViewer_instance () in
  sequents_viewer#load_logo;
  cic_math_view#set_href_callback
    (Some (fun uri ->
      let uri =
       try
        `Uri (UriManager.uri_of_string uri)
       with
        UriManager.IllFormedUri _ ->
         `NRef (NReference.reference_of_string uri)
      in
      (MatitaMathView.cicBrowser ())#load uri));
  let browser_observer _ = MatitaMathView.refresh_all_browsers () in
  let sequents_observer grafite_status =
    sequents_viewer#reset;
    match grafite_status#ng_mode with
       `ProofMode ->
        sequents_viewer#nload_sequents grafite_status;
        (try
          script#setGoal
           (Some (Continuationals.Stack.find_goal grafite_status#stack));
          let goal =
           match script#goal with
              None -> assert false
            | Some n -> n
          in
           sequents_viewer#goto_sequent grafite_status goal
        with Failure _ -> script#setGoal None);
     | `CommandMode -> sequents_viewer#load_logo
  in
  script#addObserver sequents_observer;
  script#addObserver browser_observer

  (** {{{ Debugging *)
let _ =
  if BuildTimeConf.debug ||
     Helm_registry.get_bool "matita.debug_menu" 
  then begin
    gui#main#debugMenu#misc#show ();
    let addDebugItem label callback =
      let item =
        GMenu.menu_item ~packing:gui#main#debugMenu_menu#append ~label () in
      ignore (item#connect#activate callback) 
    in
    let addDebugCheckbox label ?(init=false) callback =
      let item =
        GMenu.check_menu_item 
          ~packing:gui#main#debugMenu_menu#append ~label () in
      item#set_active init;
      ignore (item#connect#toggled (callback item)) 
    in
    let addDebugSeparator () =
      ignore (GMenu.separator_item ~packing:gui#main#debugMenu_menu#append ())
    in
    addDebugItem "dump aliases" (fun _ ->
      let status = script#grafite_status in
      LexiconEngine.dump_aliases prerr_endline "" status);
(* FG: DEBUGGING   
    addDebugItem "dump interpretations" (fun _ ->
      let status = script#lexicon_status in
      let filter = 
       List.filter (function LexiconAst.Interpretation _ -> true | _ -> false)
      in
      HLog.debug (String.concat "\n"
       (List.fold_right
         (fun x l -> (LexiconAstPp.pp_command x)::l)
         (filter status.LexiconEngine.lexicon_content_rev) [])));
*)
    addDebugSeparator ();
    addDebugCheckbox "high level pretty printer" ~init:true
      (fun mi () -> assert false (* MATITA 1.0 *));
    addDebugSeparator ();
    addDebugItem "always show all disambiguation errors"
      (fun _ -> MatitaGui.all_disambiguation_passes := true);
    addDebugItem "prune disambiguation errors"
      (fun _ -> MatitaGui.all_disambiguation_passes := false);
    addDebugSeparator ();
    addDebugCheckbox "multiple disambiguation passes" ~init:true
      (fun mi () -> MultiPassDisambiguator.only_one_pass := mi#active);
    addDebugCheckbox "tactics logging" 
      (fun mi () -> NTacStatus.debug := mi#active);
    addDebugCheckbox "disambiguation/refiner/unification/metasubst logging"
      (fun mi () -> NCicRefiner.debug := mi#active; NCicUnification.debug :=
              mi#active; MultiPassDisambiguator.debug := mi#active; NCicMetaSubst.debug := mi#active);
    addDebugCheckbox "reduction logging"
      (fun mi () -> NCicReduction.debug := mi#active; CicReduction.ndebug := mi#active);
    addDebugSeparator ();
    addDebugItem "Expand virtuals"
    (fun _ -> (MatitaScript.current ())#expandAllVirtuals);
  end
  (** Debugging }}} *)

  (** {2 Main} *)

let _ =
  at_exit (fun () -> print_endline "\nThanks for using Matita!\n");
  Sys.catch_break true;
  let args = Helm_registry.get_list Helm_registry.string "matita.args" in
  (try gui#loadScript (List.hd args) with Failure _ -> ());
  gui#main#mainWin#show ();
  try
   GtkThread.main ()
  with Sys.Break ->
   Sys.set_signal Sys.sigint
    (Sys.Signal_handle
      (fun _ ->
        prerr_endline "Still cleaning the library: don't be impatient!"));
   prerr_endline "Matita is cleaning up. Please wait.";
   let baseuri = 
    (MatitaScript.current ())#grafite_status#baseuri
   in
     LibraryClean.clean_baseuris [baseuri]

(* vim:set foldmethod=marker: *)
