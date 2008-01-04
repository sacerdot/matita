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

let out = ref ignore 

let set_callback f = out := f

let pp_ast_statement st =
  GrafiteAstPp.pp_statement
    ~map_unicode_to_tex:(Helm_registry.get_bool "matita.paste_unicode_as_tex")
    ~term_pp:CicNotationPp.pp_term
    ~lazy_term_pp:CicNotationPp.pp_term ~obj_pp:(CicNotationPp.pp_obj CicNotationPp.pp_term) st

(* NOBODY EVER USER matitatop 

let pp_ocaml_mode () = 
  HLog.message "";
  HLog.message "                      ** Entering Ocaml mode ** ";
  HLog.message "";
  HLog.message "Type 'go ();;' to enter an interactive matitac";
  HLog.message ""
  
let rec interactive_loop () = 
  let str = Ulexing.from_utf8_channel stdin in
  try
    run_script str 
      (MatitaEngine.eval_from_stream ~first_statement_only:false ~prompt:true
      ~include_paths:(Helm_registry.get_list Helm_registry.string
        "matita.includes"))
  with 
  | GrafiteEngine.Drop -> pp_ocaml_mode ()
  | GrafiteEngine.Macro (floc, f) ->
      begin match f (get_macro_context !grafite_status) with 
       | _, GrafiteAst.Inline (_, style, suri, prefix) ->
         let str =
          ApplyTransformation.txt_of_inline_macro style suri prefix
           ~map_unicode_to_tex:(Helm_registry.get_bool
             "matita.paste_unicode_as_tex")
         in
          !out str;
	  interactive_loop ()
       | _ ->
         let x, y = HExtlib.loc_of_floc floc in
         HLog.error (sprintf "A macro has been found in a script at %d-%d" x y);
         interactive_loop ()
      end
  | Sys.Break -> HLog.error "user break!"; interactive_loop ()
  | GrafiteTypes.Command_error _ -> interactive_loop ()
  | End_of_file ->
     print_newline ();
     clean_exit fname (Some 0)
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
;;
*)

(* snippet for extraction, should be moved to the build function 
  if false then
   (let baseuri =
    (* This does not work yet :-(
       let baseuri =
        GrafiteTypes.get_string_option
        (match !grafite_status with None -> assert false | Some s -> s)
        "baseuri" in*)
    lazy
      (let _root, buri, _fname = Librarian.baseuri_of_script ~include_paths:[] fname in
      buri)
   in
   let mangled_baseuri =
    lazy
     ( let baseuri = Lazy.force baseuri in
       let baseuri = String.sub baseuri 5 (String.length baseuri - 5) in
       let baseuri = Pcre.replace ~pat:"/" ~templ:"_" baseuri in
        String.uncapitalize baseuri
     ) in
   let f =
    lazy
     (open_out
       (Filename.dirname fname ^ "/" ^ Lazy.force mangled_baseuri ^ ".ml")) in
    LibrarySync.set_object_declaration_hook
     (fun _ obj ->
       output_string (Lazy.force f)
        (CicExportation.ppobj (Lazy.force baseuri) obj);
       flush (Lazy.force f)));
*)

(** {2 Initialization} *)

let slash_n_RE = Pcre.regexp "\\n" ;;

let run_script is lexicon_status' grafite_status' eval_function  =
  let print_cb =
    if Helm_registry.get_int "matita.verbosity" < 1 then 
      (fun _ _ -> ())
    else 
      (fun grafite_status stm ->
        let stm = pp_ast_statement stm in
        let stm = Pcre.replace ~rex:slash_n_RE stm in
        let stm =
          if String.length stm > 50 then String.sub stm 0 50 ^ " ..."
          else stm
        in
        HLog.debug ("Executing: ``" ^ stm ^ "''"))
  in
  match eval_function lexicon_status' grafite_status' is print_cb with
  | [] -> raise End_of_file
  | ((grafite_status'',lexicon_status''),None)::_ ->
     grafite_status'', lexicon_status''
  | (s,Some _)::_ -> raise AttemptToInsertAnAlias
;;

let clean_exit baseuri rc =
  LibraryClean.clean_baseuris ~verbose:false [baseuri]; rc
;;

let get_macro_context = function
   | Some {GrafiteTypes.proof_status = GrafiteTypes.No_proof} -> []
   | Some status                ->
      let stack = GrafiteTypes.get_stack status in
      let goal = Continuationals.Stack.find_goal stack in
      GrafiteTypes.get_proof_context status goal
   | None                       -> assert false
;;
   
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

let rec compiler_loop fname =
  (* initialization, MOVE OUTSIDE *)
  let matita_debug = Helm_registry.get_bool "matita.debug" in
  let bench_mode =  Helm_registry.get_bool "matita.bench" in
  let clean_baseuri = not (Helm_registry.get_bool "matita.preserve") in    
  let include_paths = 
    Helm_registry.get_list Helm_registry.string "matita.includes" 
  in
  (* sanity checks *)
  let _,baseuri,fname = Librarian.baseuri_of_script ~include_paths fname in
  let moo_fname = 
   LibraryMisc.obj_file_of_baseuri ~must_exist:false ~baseuri ~writable:true
  in
  let lexicon_fname= 
   LibraryMisc.lexicon_file_of_baseuri ~must_exist:false ~baseuri ~writable:true
  in
  if Http_getter_storage.is_read_only baseuri then 
    HLog.error 
      (Printf.sprintf "uri %s belongs to a read-only repository" baseuri);
  (* cleanup of previously compiled objects *)
  if (not (Http_getter_storage.is_empty ~local:true baseuri) ||
      LibraryClean.db_uris_of_baseuri baseuri <> []) && clean_baseuri
    then begin
    HLog.message ("baseuri " ^ baseuri ^ " is not empty");
    HLog.message ("cleaning baseuri " ^ baseuri);
    LibraryClean.clean_baseuris [baseuri];
    assert (Http_getter_storage.is_empty ~local:true baseuri);
  end;
  (* create dir for XML files *)
  if not (Helm_registry.get_opt_default Helm_registry.bool "matita.nodisk"
            ~default:false) 
  then
    HExtlib.mkdir 
      (Filename.dirname 
        (Http_getter.filename ~local:true ~writable:true (baseuri ^
        "foo.con")));
  (* begin of compilation *)
  let grafite_status = GrafiteSync.init baseuri in
  let lexicon_status = 
    CicNotation2.load_notation ~include_paths:[]
      BuildTimeConf.core_notation_script 
  in
  let big_bang = Unix.gettimeofday () in
  let time = Unix.time () in
  HLog.message ("compiling " ^ Filename.basename fname ^ " in " ^ baseuri);
  let buf = Ulexing.from_utf8_channel (open_in fname) in
  try
    let grafite_status, lexicon_status =
     run_script buf lexicon_status grafite_status 
      (MatitaEngine.eval_from_stream ~first_statement_only:false ~include_paths)
    in
    let elapsed = Unix.time () -. time in
    let proof_status,moo_content_rev,lexicon_content_rev = 
      grafite_status.proof_status, grafite_status.moo_content_rev, 
       lexicon_status.LexiconEngine.lexicon_content_rev
    in
    if proof_status <> GrafiteTypes.No_proof then
     (HLog.error
      "there are still incomplete proofs at the end of the script"; 
     pp_times fname bench_mode false big_bang;
     clean_exit baseuri false)
    else
     (if Helm_registry.get_bool "matita.moo" then begin
        (* FG: we do not generate .moo when dumping .mma files *)
        GrafiteMarshal.save_moo moo_fname moo_content_rev;
        LexiconMarshal.save_lexicon lexicon_fname lexicon_content_rev;
     end;
     let tm = Unix.gmtime elapsed in
     let sec = string_of_int tm.Unix.tm_sec ^ "''" in
     let min = 
       if tm.Unix.tm_min > 0 then (string_of_int tm.Unix.tm_min^"' ") else "" 
     in
     let hou = 
       if tm.Unix.tm_hour > 0 then (string_of_int tm.Unix.tm_hour^"h ") else ""
     in
     HLog.message 
       (sprintf "execution of %s completed in %s." fname (hou^min^sec));
     pp_times fname bench_mode true big_bang;
     true)
  with 
  | End_of_file -> HLog.error "End_of_file?!"; clean_exit baseuri false
  | Sys.Break as exn ->
     if matita_debug then raise exn;
     HLog.error "user break!";
     pp_times fname bench_mode false big_bang;
     clean_exit baseuri false
  | GrafiteEngine.Macro (floc, f) ->
      ((* THIS CODE IS NOW BROKEN *) HLog.warn "Codice da rivedere";
      match f (get_macro_context (Some grafite_status)) with 
      | _, GrafiteAst.Inline (_, style, suri, prefix) ->
        let str =
         ApplyTransformation.txt_of_inline_macro style suri prefix
          ~map_unicode_to_tex:(Helm_registry.get_bool
            "matita.paste_unicode_as_tex") in
        print_endline str;
        compiler_loop fname 
      | _ ->
        let x, y = HExtlib.loc_of_floc floc in
        HLog.error (sprintf "A macro has been found at %d-%d" x y);
        pp_times fname bench_mode false big_bang;
        clean_exit baseuri false)
  | HExtlib.Localized (floc,CicNotationParser.Parse_error err) ->
      let (x, y) = HExtlib.loc_of_floc floc in
      HLog.error (sprintf "Parse error at %d-%d: %s" x y err);
      pp_times fname bench_mode false big_bang;
      clean_exit baseuri false
  | exn ->
       if matita_debug then raise exn;
       HLog.error (snd (MatitaExcPp.to_string exn));
       pp_times fname bench_mode false big_bang;
       clean_exit baseuri false
;;

let main () =
  MatitaInit.initialize_all ();
  (* targets and deps *)
  let targets = Helm_registry.get_list Helm_registry.string "matita.args" in
  let deps = 
    match targets with
    | [] ->
      (match Librarian.find_roots_in_dir (Sys.getcwd ()) with
      | [x] -> 
         HLog.message ("Using the following root: " ^ x);
         Make.load_deps_file (Filename.dirname x ^ "/depends") 
      | [] -> 
         HLog.error "No targets and no root found"; exit 1
      | roots -> 
         HLog.error ("Too many roots found, move into one and retry: "^
           String.concat ", " roots);exit 1);
    | hd::_ -> 
      let root, _, _ = Librarian.baseuri_of_script hd in
      HLog.message ("Using the following root: " ^ root);
      Make.load_deps_file (root ^ "/depends") 
  in
  (* must be called after init since args are set by cmdline parsing *)
  let system_mode =  Helm_registry.get_bool "matita.system" in
  let bench_mode =  Helm_registry.get_bool "matita.bench" in
  if bench_mode then Helm_registry.set_int "matita.verbosity" 0;
  if system_mode then HLog.message "Compiling in system space";
  if bench_mode then MatitaMisc.shutup ();
  (* here we go *)
  let module F = 
    struct 
      type source_object = string
      type target_object = string
      let string_of_source_object s = s;;
      let string_of_target_object s = s;;

      let target_of mafile = 
        let _,baseuri,_ = Librarian.baseuri_of_script mafile in
        LibraryMisc.obj_file_of_baseuri 
          ~must_exist:false ~baseuri ~writable:true 
      ;;
  
      let mtime_of_source_object s =
        try Some (Unix.stat s).Unix.st_mtime
        with Unix.Unix_error (Unix.ENOENT, "stat", f) when f = s -> 
          raise (Failure ("Unable to stat a source file: " ^ s)) 
      ;;
  
      let mtime_of_target_object s =
        try Some (Unix.stat s).Unix.st_mtime
        with Unix.Unix_error (Unix.ENOENT, "stat", f) when f = s -> None
      ;;
  
      let build fname = 
        let oldfname = 
          Helm_registry.get_opt
           Helm_registry.string "matita.filename"
        in
        Helm_registry.set_string "matita.filename" fname;
        let rc = compiler_loop fname in
        (match oldfname with
        | Some n -> Helm_registry.set_string "matita.filename" n;
        | _ -> Helm_registry.unset "matita.filename");
        rc
      ;;
    end 
  in
  let module Make = Make.Make(F) in
  Make.make deps targets

