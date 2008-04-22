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

let grafite_status = (ref [] : GrafiteTypes.status list ref)
let lexicon_status = (ref [] : LexiconEngine.status list ref)

let run_script is eval_function  =
  let lexicon_status',grafite_status' = 
    match !lexicon_status,!grafite_status with
    | ss::_, s::_ -> ss,s
    | _,_ -> assert false
  in
  let cb = fun _ _ -> () in
  let matita_debug = Helm_registry.get_bool "matita.debug" in
  try
   match eval_function lexicon_status' grafite_status' is cb with
      [] -> raise End_of_file
    | ((grafite_status'',lexicon_status''),None)::_ ->
       lexicon_status := lexicon_status''::!lexicon_status;
       grafite_status := grafite_status''::!grafite_status
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
  match !grafite_status with
     [] -> exit n
   | grafite_status::_ ->
       let baseuri = GrafiteTypes.get_baseuri grafite_status in
       LibraryClean.clean_baseuris ~verbose:false [baseuri];
       exit n

let terminate n =
 let terminator = String.make 1 (Char.chr 249) in
 let prompt =
  (match n with
     None -> "-1"
   | Some n -> string_of_int n) ^ terminator
 in
  print_endline prompt;
  prerr_endline prompt
;;

let outer_syntax_parser () =
 let text = ref "" in
 let tag = ref `Do in
 let callbacks =
  { XmlPushParser.default_callbacks with
    XmlPushParser.start_element =
     (Some
       (fun name attrs ->
         match name with
            "pgip" -> ()
          | "doitem" -> tag := `Do
          | "undoitem" -> tag := `Undo
          | _ -> assert false)) ;
    XmlPushParser.character_data =
     (Some (fun s -> text := !text ^ s)) ;
    XmlPushParser.end_element =
     (Some
       (function
           "pgip" -> raise (XmlPushParser.Parse_error "EOC")
         | "doitem"
         | "undoitem" -> ()
         | _ -> assert false))
  }
 in
  let parse = XmlPushParser.create_parser callbacks in
    try
     XmlPushParser.parse parse (`Channel stdin) ;
     raise End_of_file
    with
       XmlPushParser.Parse_error "no element found" -> raise End_of_file
     | XmlPushParser.Parse_error "EOC" ->
        match !tag with
           `Do -> `Do !text
         | `Undo ->
             try
              `Undo (int_of_string !text)
             with
              Failure _ -> assert false
;;

let include_paths =
 lazy (Helm_registry.get_list Helm_registry.string "matita.includes")
;;
  
let rec interactive_loop () = 
  (* every loop is terminated by a terminator both on stdout and stderr *)
  let interactive_loop n = terminate n; interactive_loop () in
  try
   match outer_syntax_parser () with
      `Undo n ->
        let rec drop =
         function
            0,l -> l
          | n,_::l -> drop (n-1,l)
          | _,[] -> assert false
        in
         let to_be_dropped = List.length !lexicon_status - n in
         let safe_hd = function [] -> assert false | he::_ -> he in
         let cur_lexicon_status = safe_hd !lexicon_status in
         let cur_grafite_status = safe_hd !grafite_status in
          lexicon_status := drop (to_be_dropped, !lexicon_status) ;
          grafite_status := drop (to_be_dropped, !grafite_status) ;
          let lexicon_status = safe_hd !lexicon_status in
          let grafite_status = safe_hd !grafite_status in
           LexiconSync.time_travel
            ~present:cur_lexicon_status ~past:lexicon_status;
           GrafiteSync.time_travel
            ~present:cur_grafite_status ~past:grafite_status;
           interactive_loop (Some n)
    | `Do command ->
        let str = Ulexing.from_utf8_string command in
        let watch_statuses lexicon_status grafite_status =
         match grafite_status.GrafiteTypes.proof_status with
            GrafiteTypes.Incomplete_proof
             {GrafiteTypes.proof = uri,metasenv,_subst,bo,ty,attrs ;
              GrafiteTypes.stack = stack } ->
              let open_goals = Continuationals.Stack.open_goals stack in
              print_endline
               (String.concat "\n"
                 (List.map
                   (fun i ->
                     ApplyTransformation.txt_of_cic_sequent 80 metasenv
                      ~map_unicode_to_tex:(Helm_registry.get_bool
                        "matita.paste_unicode_as_tex")
                      (List.find (fun (j,_,_) -> j=i) metasenv)
                   ) open_goals))
          | _ -> ()
        in
         run_script str 
           (MatitaEngine.eval_from_stream ~first_statement_only:true 
           ~include_paths:(Lazy.force include_paths) ~watch_statuses) ;
         interactive_loop (Some (List.length !lexicon_status))
  with 
   | GrafiteEngine.Macro (floc,_) ->
      let x, y = HExtlib.loc_of_floc floc in
       HLog.error
        (sprintf "A macro has been found in a script at %d-%d" x y);
       interactive_loop None
   | Sys.Break -> HLog.error "user break!"; interactive_loop None
   | GrafiteTypes.Command_error _ -> interactive_loop None
   | HExtlib.Localized (floc,CicNotationParser.Parse_error err) ->
      let x, y = HExtlib.loc_of_floc floc in
       HLog.error (sprintf "Parse error at %d-%d: %s" x y err);
       interactive_loop None
   | End_of_file as exn -> raise exn
   | exn -> HLog.error (Printexc.to_string exn); interactive_loop None


let main () = 
  MatitaInit.initialize_all ();
  HLog.set_log_callback
   (fun tag msg ->
     let s =
      match tag with
         `Debug -> "<div style='color:blue'>Debug: " ^ msg ^ "</div><br/>\n"
       | `Message -> "<div style='color:green'>Info: " ^ msg ^ "</div><br/>\n"
       | `Warning -> "<div style='color:yellow'>Warn: " ^ msg ^ "</div><br/>\n"
       | `Error -> "<div style='color:red'>Error: " ^ msg ^ "</div><br/>\n"
     in
      output_string stderr s;
      flush stderr
   );
  (* must be called after init since args are set by cmdline parsing *)
  let system_mode =  Helm_registry.get_bool "matita.system" in
  let include_paths =
   Helm_registry.get_list Helm_registry.string "matita.includes" in
  grafite_status := [GrafiteSync.init "cic:/matita/tests/"];
  lexicon_status :=
   [CicNotation2.load_notation ~include_paths
     BuildTimeConf.core_notation_script] ;
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
      | GrafiteEngine.Drop -> clean_exit 1
    );
    let proof_status,moo_content_rev,lexicon_content_rev = 
      match !lexicon_status,!grafite_status with
      | ss::_, s::_ ->
         s.proof_status, s.moo_content_rev,
          ss.LexiconEngine.lexicon_content_rev
      | _,_ -> assert false
    in
    if proof_status <> GrafiteTypes.No_proof then
     begin
      HLog.error
       "there are still incomplete proofs at the end of the script";
      clean_exit 2
     end
    else
     begin
       let baseuri =
        GrafiteTypes.get_baseuri 
           (match !grafite_status with
             [] -> assert false
           | s::_ -> s)
       in
       let moo_fname = 
         LibraryMisc.obj_file_of_baseuri 
           ~must_exist:false ~baseuri ~writable:true 
       in
       let lexicon_fname= 
         LibraryMisc.lexicon_file_of_baseuri 
          ~must_exist:false ~baseuri ~writable:true 
       in
       GrafiteMarshal.save_moo moo_fname moo_content_rev;
       LexiconMarshal.save_lexicon lexicon_fname lexicon_content_rev;
       exit 0
     end
  with 
  | exn ->
      if matita_debug then raise exn;
      clean_exit 3
