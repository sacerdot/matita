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

let slash_n_RE = Pcre.regexp "\\n" ;;

let pp_ast_statement grafite_status stm =
  let stm = GrafiteAstPp.pp_statement stm
    ~map_unicode_to_tex:(Helm_registry.get_bool "matita.paste_unicode_as_tex")
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

let dump f =
   let module G = GrafiteAst in
   let module L = LexiconAst in
   let module H = HExtlib in
   let floc = H.dummy_floc in
   let nl_ast = G.Comment (floc, G.Note (floc, "")) in
   let pp_statement stm =
     GrafiteAstPp.pp_statement stm        
       ~map_unicode_to_tex:(Helm_registry.get_bool
         "matita.paste_unicode_as_tex")
   in
   let pp_lexicon = LexiconAstPp.pp_command in
   let och = open_out f in
   let nl () =  output_string och (pp_statement nl_ast) in
   MatitaMisc.out_preamble och;
   let grafite_parser_cb = function
      | G.Executable (loc, G.Command (_, G.Include (_,_))) -> ()
      | stm ->
         output_string och (pp_statement stm); nl (); nl ()
   in
   let lexicon_parser_cb cmd =
         output_string och (pp_lexicon cmd); nl (); nl ()
   in
   begin fun () ->
      Helm_registry.set_bool "matita.moo" false;
      GrafiteParser.set_grafite_callback grafite_parser_cb;
      GrafiteParser.set_lexicon_callback lexicon_parser_cb
   end, 
   begin fun x ->
      close_out och;
      GrafiteParser.set_grafite_callback (fun _ -> ());
      GrafiteParser.set_lexicon_callback (fun _ -> ());
      Helm_registry.set_bool "matita.moo" true;
      x
   end
;;

let get_macro_context = function _ -> []
;;
   
let pp_times fname rc big_bang big_bang_u big_bang_s = 
  if not (Helm_registry.get_bool "matita.verbose") then
    let { Unix.tms_utime = u ; Unix.tms_stime = s} = Unix.times () in
    let r = Unix.gettimeofday () -. big_bang in
    let u = u -. big_bang_u in
    let s = s -. big_bang_s in
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

let activate_extraction baseuri fname =
  ()
  (* MATITA 1.0
 if Helm_registry.get_bool "matita.extract" then
  let mangled_baseuri =
   let baseuri = String.sub baseuri 5 (String.length baseuri - 5) in
     let baseuri = Pcre.replace ~pat:"/" ~templ:"_" baseuri in
      String.uncapitalize baseuri in
  let f =
    open_out
     (Filename.dirname fname ^ "/" ^ mangled_baseuri ^ ".ml") in
   LibrarySync.add_object_declaration_hook
    (fun ~add_obj ~add_coercion _ obj ->
      output_string f (CicExportation.ppobj baseuri obj);
      flush f; []);
      *)
;;

let compile atstart options fname =
  let matita_debug = Helm_registry.get_bool "matita.debug" in
  let include_paths = get_include_paths options in
  let root,baseuri,fname,_tgt = 
    Librarian.baseuri_of_script ~include_paths fname in
  if Http_getter_storage.is_read_only baseuri then assert false;
  activate_extraction baseuri fname ;
  let lexicon_status = 
    CicNotation2.load_notation ~include_paths:[] (new LexiconEngine.status)
      BuildTimeConf.core_notation_script 
  in
  atstart (); (* FG: do not invoke before loading the core notation script *)  
  let grafite_status =
   (new GrafiteTypes.status baseuri)#set_lstatus lexicon_status#lstatus in
  let big_bang = Unix.gettimeofday () in
  let { Unix.tms_utime = big_bang_u ; Unix.tms_stime = big_bang_s} = 
    Unix.times () 
  in
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
    (* cleanup of previously compiled objects *)
    if (not (Http_getter_storage.is_empty ~local:true baseuri))
      then begin
      HLog.message ("baseuri " ^ baseuri ^ " is not empty");
      HLog.message ("cleaning baseuri " ^ baseuri);
      LibraryClean.clean_baseuris [baseuri];
    end;
    HLog.message ("compiling " ^ Filename.basename fname ^ " in " ^ baseuri);
    if not (Helm_registry.get_bool "matita.verbose") then
      (let cc = 
        let rex = Str.regexp ".*opt$" in
        if Str.string_match rex Sys.argv.(0) 0 then "matitac.opt"
        else "matitac" 
      in
      let s = Printf.sprintf "%s %-35s " cc (cut (root^"/") fname) in
      print_string s; flush stdout);
    (* we dalay this error check until we print 'matitac file ' *)
    assert (Http_getter_storage.is_empty ~local:true baseuri);
    (* create dir for XML files *)
    if not (Helm_registry.get_opt_default Helm_registry.bool "matita.nodisk"
              ~default:false) 
    then
      HExtlib.mkdir 
        (Filename.dirname 
          (Http_getter.filename ~local:true ~writable:true (baseuri ^
          "foo.con")));
    let buf = Ulexing.from_utf8_channel (open_in fname) in
    let print_cb =
      if not (Helm_registry.get_bool "matita.verbose") then (fun _ _ -> ())
      else pp_ast_statement
    in
    let grafite_status =
     let rec aux_for_dump x grafite_status =
      match
       MatitaEngine.eval_from_stream ~first_statement_only:false ~include_paths
        grafite_status buf x
      with
      | [] -> grafite_status
      | (g,None)::_ -> g
      | (g,Some _)::_ ->
         raise (AttemptToInsertAnAlias (g :> LexiconEngine.status))
     in
       aux_for_dump print_cb grafite_status
    in
    let elapsed = Unix.time () -. time in
    let moo_content_rev,lexicon_content_rev = 
      grafite_status#moo_content_rev, 
       grafite_status#lstatus.LexiconEngine.lexicon_content_rev
    in
     (if Helm_registry.get_bool "matita.moo" then begin
        (* FG: we do not generate .moo when dumping .mma files *)
        GrafiteMarshal.save_moo moo_fname moo_content_rev;
        LexiconMarshal.save_lexicon lexicon_fname lexicon_content_rev;
        NCicLibrary.Serializer.serialize ~baseuri:(NUri.uri_of_string baseuri)
         grafite_status#dump
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
     pp_times fname true big_bang big_bang_u big_bang_s;
(*
     LexiconSync.time_travel 
       ~present:lexicon_status ~past:initial_lexicon_status;
*)
     true)
  with 
  (* all exceptions should be wrapped to allow lexicon-undo (LS.time_travel) *)
  | AttemptToInsertAnAlias lexicon_status -> 
     pp_times fname false big_bang big_bang_u big_bang_s;
(*
     LexiconSync.time_travel 
       ~present:lexicon_status ~past:initial_lexicon_status;
*)
     clean_exit baseuri false
  | MatitaEngine.EnrichedWithStatus (exn, _grafite) as exn' ->
      (match exn with
      | Sys.Break -> HLog.error "user break!"
      | HExtlib.Localized (floc,CicNotationParser.Parse_error err) ->
          let (x, y) = HExtlib.loc_of_floc floc in
          HLog.error (sprintf "Parse error at %d-%d: %s" x y err)
      | exn when matita_debug -> raise exn'
      | exn -> HLog.error (snd (MatitaExcPp.to_string exn))
      );
(*       LexiconSync.time_travel ~present:lexicon ~past:initial_lexicon_status;
 *       *)
      pp_times fname false big_bang big_bang_u big_bang_s;
      clean_exit baseuri false
  | Sys.Break when not matita_debug ->
     HLog.error "user break!";
     pp_times fname false big_bang big_bang_u big_bang_s;
     clean_exit baseuri false
  | exn when not matita_debug ->
       HLog.error 
         ("Unwrapped exception, please fix: "^ snd (MatitaExcPp.to_string exn));
       pp_times fname false big_bang big_bang_u big_bang_s;
       clean_exit baseuri false

module F = 
  struct 
    type source_object = string
    type target_object = string
    let string_of_source_object s = s;;
    let string_of_target_object s = s;;

    let is_readonly_buri_of opts file = 
     let buri = List.assoc "baseuri" opts in
     Http_getter_storage.is_read_only (Librarian.mk_baseuri buri file)
    ;;

    let root_and_target_of opts mafile = 
      try
        let include_paths = get_include_paths opts in
        let root,baseuri,_,relpath =
          Librarian.baseuri_of_script ~include_paths mafile 
        in
        let obj_writeable, obj_read_only =
           if Filename.check_suffix mafile ".mma" then 
              Filename.chop_suffix mafile ".mma" ^ ".ma",
              Filename.chop_suffix mafile ".mma" ^ ".ma"
           else
              LibraryMisc.obj_file_of_baseuri 
                        ~must_exist:false ~baseuri ~writable:true,
              LibraryMisc.obj_file_of_baseuri 
                        ~must_exist:false ~baseuri ~writable:false
        in
        Some root, relpath, obj_writeable, obj_read_only
      with Librarian.NoRootFor x -> None, "", "", ""
    ;;

    let mtime_of_source_object s =
      try Some (Unix.stat s).Unix.st_mtime
      with Unix.Unix_error (Unix.ENOENT, "stat", f) when f = s -> None
    ;;

    let mtime_of_target_object s =
      try Some (Unix.stat s).Unix.st_mtime
      with Unix.Unix_error (Unix.ENOENT, "stat", f) when f = s -> None
    ;;

(* FG: a problem was noticed in relising memory between subsequent *)
(*     invocations of the compiler. The following might help       *)
    let compact r = Gc.compact (); r

    let build options fname =
      let matita_debug = Helm_registry.get_bool "matita.debug" in
      let compile atstart opts fname =
        try
          GrafiteParser.push ();
          let rc = compile atstart opts fname in
          GrafiteParser.pop ();
          rc
        with 
        | Sys.Break ->
            GrafiteParser.pop ();
            false
        | exn when not matita_debug ->
            HLog.error ("Unexpected " ^ snd(MatitaExcPp.to_string exn));
            assert false
      in
      if Filename.check_suffix fname ".mma" then 
         let generated = Filename.chop_suffix fname ".mma" ^ ".ma" in
         let atstart, atexit = dump generated in
         let res = compile atstart options fname in
         let r = compact (atexit res) in
         if r then r else begin
(*            Sys.remove generated; *)
            Printf.printf "rm %s\n" generated; flush stdout; r
         end
      else
         compact (compile ignore options fname)
    ;;

    let load_deps_file = Librarian.load_deps_file;;

  end 

module Make = Librarian.Make(F) 
