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

(* $Id: matitacLib.ml 7090 2006-12-12 14:04:59Z fguidi $ *)

open Printf

open GrafiteTypes

exception AttemptToInsertAnAlias


(** {2 Initialization} *)

let grafite_status = (ref None : GrafiteTypes.status option ref)
let lexicon_status = (ref None : LexiconEngine.status option ref)

let run_script is eval_function  =
  let lexicon_status',grafite_status' = 
    match !lexicon_status,!grafite_status with
    | Some ss, Some s -> ss,s
    | _,_ -> assert false
  in
  let cb = fun _ _ -> () in
  let matita_debug = Helm_registry.get_bool "matita.debug" in
  try
   match eval_function lexicon_status' grafite_status' is cb with
      [] -> raise End_of_file
    | ((grafite_status'',lexicon_status''),None)::_ ->
       lexicon_status := Some lexicon_status'';
       grafite_status := Some grafite_status''
    | (s,Some _)::_ -> raise AttemptToInsertAnAlias
  with
  | GrafiteEngine.Drop  
  | End_of_file
  | CicNotationParser.Parse_error _
  | HExtlib.Localized _ as exn -> raise exn
  | exn -> 
      if not matita_debug then
       HLog.error (snd (MatitaExcPp.to_string exn)) ;
      raise exn

let clean_exit n =
 let opt_exit =
  function
     None -> ()
   | Some n -> exit n
 in
  match !grafite_status with
     None -> opt_exit n
   | Some grafite_status ->
      try
       let baseuri = GrafiteTypes.get_string_option grafite_status "baseuri" in
       LibraryClean.clean_baseuris ~verbose:false [baseuri];
       opt_exit n
      with GrafiteTypes.Option_error("baseuri", "not found") ->
       (* no baseuri ==> nothing to clean yet *)
       opt_exit n

let terminate () =
 let terminator = String.make 1 (Char.chr 249) in
  print_endline terminator;
  prerr_endline terminator
;;
  
let rec interactive_loop () = 
  (* every loop is terminated by a terminator both on stdout and stderr *)
  let interactive_loop () = terminate(); interactive_loop () in
  let str = Ulexing.from_utf8_channel stdin in
  let watch_statuses lexicon_status grafite_status =
   match grafite_status.GrafiteTypes.proof_status with
      GrafiteTypes.Incomplete_proof
       {GrafiteTypes.proof = uri,metasenv,bo,ty,attrs ;
        GrafiteTypes.stack = stack } ->
        let open_goals = Continuationals.Stack.open_goals stack in
        print_endline
         (String.concat "\n"
           (List.map
             (fun i ->
               ApplyTransformation.txt_of_cic_sequent 80 metasenv
                (List.find (fun (j,_,_) -> j=i) metasenv)
             ) open_goals))
    | _ -> ()
  in
  let include_paths =
   Helm_registry.get_list Helm_registry.string "matita.includes" in
  try
    run_script str 
      (MatitaEngine.eval_from_stream ~first_statement_only:true ~prompt:false
      ~include_paths ~watch_statuses) ;
    interactive_loop ()
  with 
  | GrafiteEngine.Macro (floc,_) ->
     let x, y = HExtlib.loc_of_floc floc in
      HLog.error
       (sprintf "A macro has been found in a script at %d-%d" x y);
      interactive_loop ()
  | Sys.Break -> HLog.error "user break!"; interactive_loop ()
  | GrafiteTypes.Command_error _ -> interactive_loop ()
  | HExtlib.Localized (floc,CicNotationParser.Parse_error err) ->
     let x, y = HExtlib.loc_of_floc floc in
      HLog.error (sprintf "Parse error at %d-%d: %s" x y err);
      interactive_loop ()
  | End_of_file as exn -> raise exn
  | exn -> HLog.error (Printexc.to_string exn); interactive_loop ()


let main () = 
  MatitaInit.initialize_all ();
  (* must be called after init since args are set by cmdline parsing *)
  let system_mode =  Helm_registry.get_bool "matita.system" in
  Helm_registry.set_int "matita.verbosity" 0;
  let include_paths =
   Helm_registry.get_list Helm_registry.string "matita.includes" in
  grafite_status := Some (GrafiteSync.init ());
  lexicon_status :=
   Some (CicNotation2.load_notation ~include_paths
    BuildTimeConf.core_notation_script);
  Sys.catch_break true;
  let origcb = HLog.get_log_callback () in
  let origcb t s = origcb t ((if system_mode then "[S] " else "") ^ s) in
  let newcb tag s =
    match tag with
    | `Debug -> ()
    | `Message | `Warning | `Error -> origcb tag s
  in
  HLog.set_log_callback newcb;
  let matita_debug = Helm_registry.get_bool "matita.debug" in
  try
    (try
      interactive_loop ()
     with
      | End_of_file -> ()
      | GrafiteEngine.Drop -> clean_exit (Some 1)
    );
    let proof_status,moo_content_rev,metadata,lexicon_content_rev = 
      match !lexicon_status,!grafite_status with
      | Some ss, Some s ->
         s.proof_status, s.moo_content_rev, ss.LexiconEngine.metadata,
          ss.LexiconEngine.lexicon_content_rev
      | _,_ -> assert false
    in
    if proof_status <> GrafiteTypes.No_proof then
     begin
      HLog.error
       "there are still incomplete proofs at the end of the script";
      clean_exit (Some 2)
     end
    else
     begin
       let baseuri =
        GrafiteTypes.get_string_option
         (match !grafite_status with
             None -> assert false
           | Some s -> s) "baseuri" in
       let moo_fname = 
         LibraryMisc.obj_file_of_baseuri 
           ~must_exist:false ~baseuri ~writable:true 
       in
       let lexicon_fname= 
         LibraryMisc.lexicon_file_of_baseuri 
          ~must_exist:false ~baseuri ~writable:true 
       in
       let metadata_fname =
        LibraryMisc.metadata_file_of_baseuri 
          ~must_exist:false ~baseuri ~writable:true
       in
       GrafiteMarshal.save_moo moo_fname moo_content_rev;
       LibraryNoDb.save_metadata metadata_fname metadata;
       LexiconMarshal.save_lexicon lexicon_fname lexicon_content_rev;
       exit 0
     end
  with 
  | exn ->
      if matita_debug then raise exn;
      clean_exit (Some 3)
