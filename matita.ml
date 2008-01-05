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
      ~develcreator:gui#createDevelopment
      ()
  in
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
    (Some (fun uri -> (MatitaMathView.cicBrowser ())#load
      (`Uri (UriManager.uri_of_string uri))));
  let browser_observer _ _ = MatitaMathView.refresh_all_browsers () in
  let sequents_observer _ grafite_status =
    sequents_viewer#reset;
    match grafite_status.proof_status with
    | Incomplete_proof ({ stack = stack } as incomplete_proof) ->
        sequents_viewer#load_sequents incomplete_proof;
        (try
          script#setGoal (Some (Continuationals.Stack.find_goal stack));
          let goal =
           match script#goal with
              None -> assert false
            | Some n -> n
          in
           sequents_viewer#goto_sequent goal
        with Failure _ -> script#setGoal None);
    | Proof proof -> sequents_viewer#load_logo_with_qed
    | No_proof -> sequents_viewer#load_logo
    | Intermediate _ -> assert false (* only the engine may be in this state *)
  in
  script#addObserver sequents_observer;
  script#addObserver browser_observer

  (** {{{ Debugging *)
let _ =
  if BuildTimeConf.debug then begin
    gui#main#debugMenu#misc#show ();
    let addDebugItem ~label callback =
      let item =
        GMenu.menu_item ~packing:gui#main#debugMenu_menu#append ~label () in
      ignore (item#connect#activate callback) in
    let addDebugSeparator () =
      ignore (GMenu.separator_item ~packing:gui#main#debugMenu_menu#append ())
    in
    addDebugItem "dump environment to \"env.dump\"" (fun _ ->
      let oc = open_out "env.dump" in
      CicEnvironment.dump_to_channel oc;
      close_out oc);
    addDebugItem "load environment from \"env.dump\"" (fun _ ->
      let ic = open_in "env.dump" in
      CicEnvironment.restore_from_channel ic;
      close_in ic);
    addDebugItem "dump universes" (fun _ ->
      List.iter (fun (u,_,g) -> 
        prerr_endline (UriManager.string_of_uri u); 
        CicUniv.print_ugraph g) (CicEnvironment.list_obj ())
      );
    addDebugItem "dump environment content" (fun _ ->
      List.iter (fun (u,_,_) -> 
        prerr_endline (UriManager.string_of_uri u)) 
        (CicEnvironment.list_obj ()));
    addDebugItem "dump script status" script#dump;
    addDebugItem "dump configuration file to ./foo.conf.xml" (fun _ ->
      Helm_registry.save_to "./foo.conf.xml");
    addDebugItem "dump metasenv"
      (fun _ ->
         if script#onGoingProof () then
           HLog.debug (CicMetaSubst.ppmetasenv [] script#proofMetasenv));
    addDebugItem "print top-level grammar entries"
      CicNotationParser.print_l2_pattern;
    addDebugItem "dump moo to stderr" (fun _ ->
      let grafite_status = (MatitaScript.current ())#grafite_status in
      let moo = grafite_status.moo_content_rev in
      List.iter
        (fun cmd ->
          prerr_endline
           (GrafiteAstPp.pp_command
             ~term_pp:(fun _ -> assert false)
             ~obj_pp:(fun _ -> assert false)
             cmd))
        (List.rev moo));
    addDebugItem "print metasenv goals and stack to stderr"
      (fun _ ->
        prerr_endline ("metasenv goals: " ^ String.concat " "
          (List.map (fun (g, _, _) -> string_of_int g)
            (MatitaScript.current ())#proofMetasenv));
        prerr_endline ("stack: " ^ Continuationals.Stack.pp
          (GrafiteTypes.get_stack (MatitaScript.current ())#grafite_status)));
     addDebugItem "Print current proof term" 
       (fun _ -> 
        HLog.debug
          (CicPp.ppterm 
            (match 
            (MatitaScript.current ())#grafite_status.GrafiteTypes.proof_status
            with
            | GrafiteTypes.No_proof -> (Cic.Implicit None)
            | Incomplete_proof i -> let _,_,_subst,p,_, _ = i.GrafiteTypes.proof in p
            | Proof p -> let _,_,_subst,p,_, _ = p in p
            | Intermediate _ -> assert false)));
     addDebugItem "Print current proof (natural language) to stderr" 
       (fun _ -> 
        prerr_endline 
          (ApplyTransformation.txt_of_cic_object 120 GrafiteAst.Declarative "" 
            ~map_unicode_to_tex:(Helm_registry.get_bool
              "matita.paste_unicode_as_tex")
            (match 
            (MatitaScript.current ())#grafite_status.GrafiteTypes.proof_status
            with
            | GrafiteTypes.No_proof -> assert false
            | Incomplete_proof i -> 
                let _,m,_subst,p,ty, attrs = i.GrafiteTypes.proof in 
                Cic.CurrentProof ("current (incomplete) proof",m,p,ty,[],attrs)
            | Proof (_,m,_subst,p,ty, attrs) -> 
                Cic.CurrentProof ("current proof",m,p,ty,[],attrs)
            | Intermediate _ -> assert false)));
(*     addDebugItem "ask record choice"
      (fun _ ->
        HLog.debug (string_of_int
          (MatitaGtkMisc.ask_record_choice ~gui ~title:"title" ~message:"msg"
          ~fields:["a"; "b"; "c"]
          ~records:[
            ["0"; "0"; "0"]; ["0"; "0"; "1"]; ["0"; "1"; "0"]; ["0"; "1"; "1"];
            ["1"; "0"; "0"]; ["1"; "0"; "1"]; ["1"; "1"; "0"]; ["1"; "1"; "1"]]
          ()))); *)
(*     addDebugItem "rotate light bulbs"
      (fun _ ->
         let nb = gui#main#hintNotebook in
         nb#goto_page ((nb#current_page + 1) mod 3)); *)
    addDebugSeparator ();
(*
    addDebugItem "meets between L and R" 
      (fun _ -> 
        let l = CoercDb.coerc_carr_of_term (CicUtil.term_of_uri
          (UriManager.uri_of_string "cic:/matita/test/L.ind#xpointer(1/1)" )) 
        in
        let r = CoercDb.coerc_carr_of_term (CicUtil.term_of_uri
          (UriManager.uri_of_string "cic:/matita/test/R.ind#xpointer(1/1)" )) 
        in
        let meets = CoercGraph.meets l r in
        prerr_endline "MEETS:";
        List.iter (fun carr -> prerr_endline (CicPp.ppterm (CoercDb.term_of_carr
        carr))) meets
    );
    addDebugSeparator ();
*)
    addDebugItem "disable high level pretty printer"
      (fun _ -> CicMetaSubst.use_low_level_ppterm_in_context := true);
    addDebugItem "enable high level pretty printer"
      (fun _ -> CicMetaSubst.use_low_level_ppterm_in_context := false);
(* ZACK moved to the View menu
    addDebugItem "disable all (pretty printing) notations"
      (fun _ -> CicNotation.set_active_notations []);
    addDebugItem "enable all (pretty printing) notations"
      (fun _ ->
        CicNotation.set_active_notations
          (List.map fst (CicNotation.get_all_notations ())));
*)
    addDebugSeparator ();
    addDebugItem "enable multiple disambiguation passes (default)"
      (fun _ -> GrafiteDisambiguator.only_one_pass := false);
    addDebugItem "enable only one disambiguation pass"
      (fun _ -> GrafiteDisambiguator.only_one_pass := true);
    addDebugItem "always show all disambiguation errors"
      (fun _ -> MatitaGui.all_disambiguation_passes := true);
    addDebugItem "prune disambiguation errors"
      (fun _ -> MatitaGui.all_disambiguation_passes := false);
    addDebugSeparator ();
(* ZACK moved to the View menu
    addDebugItem "enable coercions hiding"
      (fun _ -> Acic2content.hide_coercions := true);
    addDebugItem "disable coercions hiding"
      (fun _ -> Acic2content.hide_coercions := false);
*)
    addDebugItem "show coercions graph" (fun _ ->
      let c = MatitaMathView.cicBrowser () in
      c#load (`About `Coercions));
    addDebugItem "show coercions graph (full)" (fun _ ->
      let c = MatitaMathView.cicBrowser () in
      c#load (`About `CoercionsFull));
    addDebugItem "dump coercions Db" (fun _ ->
      List.iter
      (fun (s,t,ul) -> 
          HLog.debug
           ((String.concat ","
              (List.map
                (fun u,saturations ->
                  UriManager.name_of_uri u ^
                   "(" ^ string_of_int saturations ^ ")")
                ul)) ^ ":"
             ^ CoercDb.name_of_carr s ^ " -> " ^ CoercDb.name_of_carr t))
        (CoercDb.to_list ()));
    addDebugSeparator ();
    let mview () = (MatitaMathView.sequentsViewer_instance ())#cicMathView in
(*     addDebugItem "save (sequent) MathML to matita.xml"
      (fun _ -> ignore ((Gdome.domImplementation ())#saveDocumentToFile
        ~doc:(HExtlib.unopt (mview ())#get_document) ~name:"matita.xml" ())); *)
    addDebugItem "load (sequent) MathML from matita.xml"
      (fun _ -> (mview ())#load_uri ~filename:"matita.xml");
    addDebugItem "autoWin"
    (fun _ -> MatitaAutoGui.auto_dialog Auto.get_auto_status);
  end
  (** Debugging }}} *)

  (** {2 Command line parsing} *)

let set_matita_mode () =
  let matita_mode =
    if Filename.basename Sys.argv.(0) = "cicbrowser" || 
       Filename.basename Sys.argv.(0) = "cicbrowser.opt"
    then "cicbrowser"
    else "matita"
  in
  Helm_registry.set "matita.mode" matita_mode

  (** {2 Main} *)

let _ =
  set_matita_mode ();
  at_exit (fun () -> print_endline "\nThanks for using Matita!\n");
  Sys.catch_break true;
  let args = Helm_registry.get_list Helm_registry.string "matita.args" in
  if Helm_registry.get "matita.mode" = "cicbrowser" then  (* cicbrowser *)
    let browser = MatitaMathView.cicBrowser () in
    let uri = match args with [] -> "cic:/" | _ -> String.concat " " args in
    browser#loadInput uri
  else begin  (* matita *)
    (try gui#loadScript (List.hd args) with Failure _ -> ());
    gui#main#mainWin#show ();
  end;
  try
    GtkThread.main ()
  with Sys.Break ->
   Sys.set_signal Sys.sigint
    (Sys.Signal_handle
      (fun _ ->
        prerr_endline "Still cleaning the library: don't be impatient!"));
   prerr_endline "Matita is cleaning up. Please wait.";
   let baseuri = 
     GrafiteTypes.get_baseuri (MatitaScript.current ())#grafite_status
   in
     LibraryClean.clean_baseuris [baseuri]

(* vim:set foldmethod=marker: *)
