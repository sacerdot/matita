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

exception AttemptToInsertAnAlias of LexiconEngine.status

let out = ref ignore 
let set_callback f = out := f

let slash_n_RE = Pcre.regexp "\\n" ;;

let pp_ast_statement grafite_status stm =
  let stm = GrafiteAstPp.pp_statement
    ~map_unicode_to_tex:(Helm_registry.get_bool "matita.paste_unicode_as_tex")
    ~term_pp:CicNotationPp.pp_term
    ~lazy_term_pp:CicNotationPp.pp_term ~obj_pp:(CicNotationPp.pp_obj
    CicNotationPp.pp_term) stm
  in
  let stm = Pcre.replace ~rex:slash_n_RE stm in
  let stm =
      if String.length stm > 50 then String.sub stm 0 50 ^ " ..."
      else stm
  in
    HLog.debug ("Executing: ``" ^ stm ^ "''")
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
   
let pp_times fname rc big_bang = 
  if not (Helm_registry.get_bool "matita.verbose") then
    let { Unix.tms_utime = u ; Unix.tms_stime = s} = Unix.times () in
    let r = Unix.gettimeofday () -. big_bang in
    let extra = try Sys.getenv "BENCH_EXTRA_TEXT" with Not_found -> "" in
    let rc,rcascii = 
      if rc then "[0;32mOK[0m","Ok" else "[0;31mFAIL[0m","Fail" in
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
    let s = Printf.sprintf "%-4s %s %s" rc times extra in
    print_endline s;
    flush stdout;
    HLog.message ("Compilation of "^Filename.basename fname^": "^rc)
;;

let cut prefix s = 
  let lenp = String.length prefix in
  let lens = String.length s in
  assert (lens > lenp);
  assert (String.sub s 0 lenp = prefix);
  String.sub s lenp (lens-lenp)
;;

let get_include_paths options =
  let include_paths = 
    try List.assoc "include_paths" options with Not_found -> "" 
  in
  let include_paths = Str.split (Str.regexp " ") include_paths in
  let include_paths = 
    include_paths @ 
    Helm_registry.get_list Helm_registry.string "matita.includes" 
  in
    include_paths
;;

let compile options fname =
  let matita_debug = Helm_registry.get_bool "matita.debug" in
  let include_paths = get_include_paths options in
  let root,baseuri,fname,_tgt = 
    Librarian.baseuri_of_script ~include_paths fname in
  let grafite_status = GrafiteSync.init baseuri in
  let lexicon_status = 
    CicNotation2.load_notation ~include_paths:[]
      BuildTimeConf.core_notation_script 
  in
  let initial_lexicon_status = lexicon_status in
  let big_bang = Unix.gettimeofday () in
  let time = Unix.time () in
  try
    (* sanity checks *)
    let moo_fname = 
     LibraryMisc.obj_file_of_baseuri ~must_exist:false ~baseuri ~writable:true
    in
    let lexicon_fname= 
     LibraryMisc.lexicon_file_of_baseuri 
       ~must_exist:false ~baseuri ~writable:true
    in
    if Http_getter_storage.is_read_only baseuri then 
      HLog.error 
        (Printf.sprintf "uri %s belongs to a read-only repository" baseuri);
    (* cleanup of previously compiled objects *)
    if (not (Http_getter_storage.is_empty ~local:true baseuri) ||
        LibraryClean.db_uris_of_baseuri baseuri <> []) 
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
    HLog.message ("compiling " ^ Filename.basename fname ^ " in " ^ baseuri);
    if not (Helm_registry.get_bool "matita.verbose") then
      (let cc = 
        let rex = Str.regexp ".*opt$" in
        if Str.string_match rex Sys.argv.(0) 0 then "matitac.opt"
        else "matitac" 
      in
      let s = Printf.sprintf "%s %-35s " cc (cut (root^"/") fname) in
      print_string s; flush stdout);
    let buf = Ulexing.from_utf8_channel (open_in fname) in
    let print_cb =
      if not (Helm_registry.get_bool "matita.verbose") then (fun _ _ -> ())
      else pp_ast_statement
    in
    let grafite_status, lexicon_status =
     let rec aux_for_dump x =
     try
      match
       MatitaEngine.eval_from_stream ~first_statement_only:false ~include_paths
        lexicon_status grafite_status buf x
      with
      | [] -> grafite_status, lexicon_status 
      | ((grafite,lexicon),None)::_ -> grafite, lexicon
      | ((_,l),Some _)::_ -> raise (AttemptToInsertAnAlias l)

     with MatitaEngine.EnrichedWithLexiconStatus 
            (GrafiteEngine.Macro (floc, f), lex_status) as exn ->
            match f (get_macro_context (Some grafite_status)) with 
            | _, GrafiteAst.Inline (_, style, suri, prefix) ->
              let str =
               ApplyTransformation.txt_of_inline_macro style suri prefix
                ~map_unicode_to_tex:(Helm_registry.get_bool
                  "matita.paste_unicode_as_tex") in
              !out str;
              aux_for_dump x
            |_-> raise exn
     in
       aux_for_dump print_cb
    in
    let elapsed = Unix.time () -. time in
    let proof_status,moo_content_rev,lexicon_content_rev = 
      grafite_status.proof_status, grafite_status.moo_content_rev, 
       lexicon_status.LexiconEngine.lexicon_content_rev
    in
    if proof_status <> GrafiteTypes.No_proof then
     (HLog.error
      "there are still incomplete proofs at the end of the script"; 
     pp_times fname false big_bang;
     LexiconSync.time_travel 
       ~present:lexicon_status ~past:initial_lexicon_status;
     clean_exit baseuri false)
    else
     (if not (Helm_registry.get_bool "matita.moo" && 
              Filename.check_suffix fname ".mma") then begin
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
     pp_times fname true big_bang;
     LexiconSync.time_travel 
       ~present:lexicon_status ~past:initial_lexicon_status;
     true)
  with 
  (* all exceptions should be wrapped to allow lexicon-undo (LS.time_travel) *)
  | AttemptToInsertAnAlias lexicon_status -> 
     pp_times fname false big_bang;
     LexiconSync.time_travel 
       ~present:lexicon_status ~past:initial_lexicon_status;
     clean_exit baseuri false
  | MatitaEngine.EnrichedWithLexiconStatus (exn, lex_stat) ->
      (match exn with
      | Sys.Break -> HLog.error "user break!"
      | HExtlib.Localized (floc,CicNotationParser.Parse_error err) ->
          let (x, y) = HExtlib.loc_of_floc floc in
          HLog.error (sprintf "Parse error at %d-%d: %s" x y err)
      | exn -> HLog.error (snd (MatitaExcPp.to_string exn)));
      LexiconSync.time_travel ~present:lex_stat ~past:initial_lexicon_status;
      pp_times fname false big_bang;
      clean_exit baseuri false
  | Sys.Break as exn ->
     if matita_debug then raise exn; 
     HLog.error "user break!";
     pp_times fname false big_bang;
     clean_exit baseuri false
  | exn ->
       if matita_debug then raise exn; 
       HLog.error 
         ("Unwrapped exception, please fix: "^ snd (MatitaExcPp.to_string exn));
       pp_times fname false big_bang;
       clean_exit baseuri false
;;

module F = 
  struct 
    type source_object = string
    type target_object = string
    let string_of_source_object s = s;;
    let string_of_target_object s = s;;

    let root_of opts s = 
      try
        let include_paths = get_include_paths opts in
        let root,_,_,_ = Librarian.baseuri_of_script ~include_paths s in
        Some root
      with Librarian.NoRootFor x -> None
    ;;

    let target_of opts mafile = 
      let include_paths = get_include_paths opts in
      let _,baseuri,_,_ = Librarian.baseuri_of_script ~include_paths mafile in
      LibraryMisc.obj_file_of_baseuri 
        ~must_exist:false ~baseuri ~writable:true 
    ;;

    let mtime_of_source_object s =
      try Some (Unix.stat s).Unix.st_mtime
      with Unix.Unix_error (Unix.ENOENT, "stat", f) when f = s -> None
    ;;

    let mtime_of_target_object s =
      try Some (Unix.stat s).Unix.st_mtime
      with Unix.Unix_error (Unix.ENOENT, "stat", f) when f = s -> None
    ;;

    let build = compile;;

    let load_deps_file = Librarian.load_deps_file;;

  end 

module Make = Librarian.Make(F) 

