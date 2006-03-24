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

exception AttemptToInsertAnAlias

let pp_ast_statement =
  GrafiteAstPp.pp_statement ~term_pp:CicNotationPp.pp_term
    ~lazy_term_pp:CicNotationPp.pp_term ~obj_pp:CicNotationPp.pp_obj

(** {2 Initialization} *)

let grafite_status = (ref None : GrafiteTypes.status option ref)
let lexicon_status = (ref None : LexiconEngine.status option ref)

let run_script is eval_function  =
  let lexicon_status',grafite_status' = 
    match !lexicon_status,!grafite_status with
    | Some ss, Some s -> ss,s
    | _,_ -> assert false
  in
  let slash_n_RE = Pcre.regexp "\\n" in
  let cb = 
    if Helm_registry.get_int "matita.verbosity" < 1 then 
      (fun _ _ -> ())
    else 
      (fun grafite_status stm ->
        (* dump_status grafite_status; *)
        let stm = pp_ast_statement stm in
        let stm = Pcre.replace ~rex:slash_n_RE stm in
        let stm =
          if String.length stm > 50 then
            String.sub stm 0 50 ^ " ..."
          else
            stm
        in
        HLog.debug ("Executing: ``" ^ stm ^ "''"))
  in
  try
   let grafite_status'', lexicon_status'' =
    match eval_function lexicon_status' grafite_status' is cb with
       [] -> assert false
     | (s,None)::_ -> s
     | (s,Some _)::_ -> raise AttemptToInsertAnAlias
   in
    lexicon_status := Some lexicon_status'';
    grafite_status := Some grafite_status''
  with
  | GrafiteEngine.Drop  
  | End_of_file
  | CicNotationParser.Parse_error _ as exn -> raise exn
  | exn -> 
      HLog.error (snd (MatitaExcPp.to_string exn));
      raise exn

let fname () =
  let rec aux = function
  | ""::tl -> aux tl
  | [x] -> x
  | [] -> MatitaInit.die_usage ()
  | l -> 
      prerr_endline 
        ("Wrong commands: " ^ 
          String.concat " " (List.map (fun x -> "'" ^ x ^ "'") l));
      MatitaInit.die_usage ()
  in
  aux (Helm_registry.get_list Helm_registry.string "matita.args")

let pp_ocaml_mode () = 
  HLog.message "";
  HLog.message "                      ** Entering Ocaml mode ** ";
  HLog.message "";
  HLog.message "Type 'go ();;' to enter an interactive matitac";
  HLog.message ""
  
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
  
let rec interactive_loop () = 
  let str = Ulexing.from_utf8_channel stdin in
  try
    run_script str 
      (MatitaEngine.eval_from_stream ~first_statement_only:false ~prompt:true
      ~include_paths:(Helm_registry.get_list Helm_registry.string
        "matita.includes"))
  with 
  | GrafiteEngine.Drop -> pp_ocaml_mode ()
  | GrafiteEngine.Macro (floc,_) ->
     let x, y = HExtlib.loc_of_floc floc in
      HLog.error
       (sprintf "A macro has been found in a script at %d-%d" x y);
      interactive_loop ()
  | Sys.Break -> HLog.error "user break!"; interactive_loop ()
  | GrafiteTypes.Command_error _ -> interactive_loop ()
  | End_of_file ->
     print_newline ();
     clean_exit (Some 0)
  | HExtlib.Localized (floc,CicNotationParser.Parse_error err) ->
     let x, y = HExtlib.loc_of_floc floc in
      HLog.error (sprintf "Parse error at %d-%d: %s" x y err);
      interactive_loop ()
  | exn -> HLog.error (Printexc.to_string exn); interactive_loop ()

let go () =
  Helm_registry.load_from BuildTimeConf.matita_conf;
  Http_getter.init ();
  MetadataTypes.ownerize_tables (Helm_registry.get "matita.owner");
  LibraryDb.create_owner_environment ();
  CicEnvironment.set_trust (* environment trust *)
    (let trust =
      Helm_registry.get_opt_default Helm_registry.get_bool
        ~default:true "matita.environment_trust" in
     fun _ -> trust);
  let include_paths =
   Helm_registry.get_list Helm_registry.string "matita.includes" in
  grafite_status := Some (GrafiteSync.init ());
  lexicon_status :=
   Some (CicNotation2.load_notation ~include_paths
    BuildTimeConf.core_notation_script);
  Sys.catch_break true;
  interactive_loop ()

let pp_times fname bench_mode rc big_bang = 
  if bench_mode then
    begin
      let { Unix.tms_utime = u ; Unix.tms_stime = s} = Unix.times () in
      let r = Unix.gettimeofday () -. big_bang in
      let extra = try Sys.getenv "BENCH_EXTRA_TEXT" with Not_found -> "" in
      let cc = 
        if Str.string_match (Str.regexp ".*opt$") Sys.argv.(0) 0 then 
          "matitac.opt" 
        else 
          "matitac" 
      in
      let rc = if rc then "[0;32mOK[0m" else "[0;31mFAIL[0m" in
      let times = 
        let fmt t = 
          let seconds = int_of_float t in
          let cents = int_of_float ((t -. floor t) *. 100.0) in
          let minutes = seconds / 60 in
          let seconds = seconds mod 60 in
          Printf.sprintf "%dm%02d.%02ds" minutes seconds cents
        in
        Printf.sprintf "%s %s %s" (fmt r) (fmt u) (fmt s)
      in
      let fname = 
        match MatitamakeLib.development_for_dir (Filename.dirname fname) with
        | None -> fname
        | Some d -> 
            let rootlen = String.length(MatitamakeLib.root_for_development d)in
            let fnamelen = String.length fname in
            assert (fnamelen > rootlen); 
            String.sub fname rootlen (fnamelen - rootlen)           
      in
      let fname = 
        if fname.[0] = '/' then
          String.sub fname 1 (String.length fname - 1)
        else
          fname
      in
      let s = Printf.sprintf "%s %-35s %-4s %s %s" cc fname rc times extra in
      print_endline s;
      flush stdout
    end
;;

let main ~mode = 
  let big_bang = Unix.gettimeofday () in
  MatitaInit.initialize_all ();
  (* must be called after init since args are set by cmdline parsing *)
  let fname = fname () in
  let system_mode =  Helm_registry.get_bool "matita.system" in
  let bench_mode =  Helm_registry.get_bool "matita.bench" in
  if bench_mode then
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
    | `Debug | `Message -> ()
    | `Warning | `Error -> origcb tag s
  in
  if Helm_registry.get_int "matita.verbosity" < 1 then
    HLog.set_log_callback newcb;
  if bench_mode then MatitaMisc.shutup ();
  let matita_debug = Helm_registry.get_bool "matita.debug" in
  try
    let time = Unix.time () in
    if Helm_registry.get_int "matita.verbosity" < 1 && not bench_mode then
      origcb `Message ("compiling " ^ Filename.basename fname ^ "...")
    else
      HLog.message (sprintf "execution of %s started:" fname);
    let is =
      Ulexing.from_utf8_channel
        (match fname with
        | "stdin" -> stdin
        | fname -> open_in fname) in
    let include_paths =
     Helm_registry.get_list Helm_registry.string "matita.includes" in
    (try
      run_script is 
       (MatitaEngine.eval_from_stream ~first_statement_only:false ~include_paths
         ~clean_baseuri:(not (Helm_registry.get_bool "matita.preserve")))
     with End_of_file -> ());
    let elapsed = Unix.time () -. time in
    let tm = Unix.gmtime elapsed in
    let sec = string_of_int tm.Unix.tm_sec ^ "''" in
    let min = 
      if tm.Unix.tm_min > 0 then (string_of_int tm.Unix.tm_min ^ "' ") else "" 
    in
    let hou = 
      if tm.Unix.tm_hour > 0 then (string_of_int tm.Unix.tm_hour ^ "h ") else ""
    in
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
      pp_times fname bench_mode true big_bang;
      clean_exit (Some 2)
     end
    else
     begin
       let baseuri =
        DependenciesParser.baseuri_of_script ~include_paths fname in
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
       HLog.message 
         (sprintf "execution of %s completed in %s." fname (hou^min^sec));
       pp_times fname bench_mode true big_bang;
       exit 0
     end
  with 
  | Sys.Break ->
      HLog.error "user break!";
      pp_times fname bench_mode false big_bang;
      if mode = `COMPILER then
        clean_exit (Some ~-1)
      else
        pp_ocaml_mode ()
  | GrafiteEngine.Drop ->
      if mode = `COMPILER then 
        begin
          pp_times fname bench_mode false big_bang;
          clean_exit (Some 1)
        end
      else 
        pp_ocaml_mode ()
  | GrafiteEngine.Macro (floc,_) ->
     let x, y = HExtlib.loc_of_floc floc in
      HLog.error
       (sprintf "A macro has been found in a script at %d-%d" x y);
      if mode = `COMPILER then 
        begin
          pp_times fname bench_mode false big_bang;
          clean_exit (Some 1)
        end
      else 
        pp_ocaml_mode ()
  | HExtlib.Localized (floc,CicNotationParser.Parse_error err) ->
     let (x, y) = HExtlib.loc_of_floc floc in
     HLog.error (sprintf "Parse error at %d-%d: %s" x y err);
     if mode = `COMPILER then
       begin
         pp_times fname bench_mode false big_bang;
         clean_exit (Some 1)
       end
     else
       pp_ocaml_mode ()
  | exn ->
      if matita_debug then raise exn;
      if mode = `COMPILER then 
        begin
          pp_times fname bench_mode false big_bang;
          clean_exit (Some 3)
        end
      else 
        pp_ocaml_mode ()

