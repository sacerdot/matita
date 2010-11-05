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

module G = GrafiteAst

let debug = false ;;
let debug_print = if debug then prerr_endline else ignore ;;

let eval_macro_screenshot (status : GrafiteTypes.status) name =
  assert false (* MATITA 1.0
  let _,_,metasenv,subst,_ = status#obj in
  let sequent = List.hd metasenv in
  let mathml = 
    ApplyTransformation.nmml_of_cic_sequent 
      status metasenv subst sequent 
  in
  let domImpl = Gdome.domImplementation () in
  ignore(domImpl#saveDocumentToFile 
    ~name:(name^".xml") ~doc:mathml ());
  ignore(Sys.command ("mathmlsvg --verbose=1 --font-size=20 --cut-filename=no " ^ 
    Filename.quote (name^".xml")));
  ignore(Sys.command ("convert " ^ 
    Filename.quote (name^".svg") ^ " " ^ 
    Filename.quote (name^".png")));
  HLog.debug ("generated " ^ name ^ ".png");
  status, `New []
  *)
;;

let eval_ast ~include_paths ?do_heavy_checks status (text,prefix_len,ast) =
 let baseuri = status#baseuri in
 let new_aliases,new_status =
  GrafiteDisambiguate.eval_with_new_aliases status
   (fun status ->
     GrafiteEngine.eval_ast ~include_paths ?do_heavy_checks status
      (text,prefix_len,ast)) in
 let _,intermediate_states = 
  List.fold_left
   (fun (status,acc) (k,value) -> 
     let v = GrafiteAst.description_of_alias value in
     let b =
      try
       let NReference.Ref (uri,_) = NReference.reference_of_string v in
        NUri.baseuri_of_uri uri = baseuri
      with
       NReference.IllFormedReference _ ->
        false (* v is a description, not a URI *)
     in
      if b then 
       status,acc
      else
       let status =
        GrafiteDisambiguate.set_proof_aliases status ~implicit_aliases:false
         GrafiteAst.WithPreferences [k,value]
       in
        status, (status ,Some (k,value))::acc
   ) (status,[]) new_aliases (* WARNING: this must be the old status! *)
 in
  (new_status,None)::intermediate_states
;;

exception TryingToAdd of string
exception EnrichedWithStatus of exn * GrafiteTypes.status

let eval_from_stream ~include_paths ?do_heavy_checks status str cb =
 let matita_debug = Helm_registry.get_bool "matita.debug" in
 let rec loop status =
  let stop,status = 
   try
     let cont =
       try Some (GrafiteParser.parse_statement status str)
       with End_of_file -> None in
     match cont with
     | None -> true, status
     | Some ast ->
        cb status ast;
        let new_statuses =
          eval_ast ~include_paths ?do_heavy_checks status ("",0,ast) in
        let status =
         match new_statuses with
            [s,None] -> s
          | _::(_,Some (_,value))::_ ->
                raise (TryingToAdd (GrafiteAstPp.pp_alias value))
          | _ -> assert false
        in
         false, status
   with exn when not matita_debug ->
     raise (EnrichedWithStatus (exn, status))
  in
  if stop then status else loop status
 in
  loop status
;;

(* EX MATITACLIB *)
open Printf

open GrafiteTypes

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

let compile options fname =
  let matita_debug = Helm_registry.get_bool "matita.debug" in
  let include_paths = get_include_paths options in
  let root,baseuri,fname,_tgt = 
    Librarian.baseuri_of_script ~include_paths fname in
  if Http_getter_storage.is_read_only baseuri then assert false;
  activate_extraction baseuri fname ;
  let grafite_status = new GrafiteTypes.status baseuri in
  let big_bang = Unix.gettimeofday () in
  let { Unix.tms_utime = big_bang_u ; Unix.tms_stime = big_bang_s} = 
    Unix.times () 
  in
  let time = Unix.time () in
  try
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
     eval_from_stream ~include_paths grafite_status buf print_cb
    in
    let elapsed = Unix.time () -. time in
     (if Helm_registry.get_bool "matita.moo" then begin
       GrafiteTypes.Serializer.serialize ~baseuri:(NUri.uri_of_string baseuri)
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
  | EnrichedWithStatus (exn, _grafite) as exn' ->
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
      let compile opts fname =
        try
        (* MATITA 1.0: c'erano le push/pop per il parser; ma per
         * l'environment nuovo? *)
         compile opts fname
        with 
        | Sys.Break -> false
        | exn when not matita_debug ->
            HLog.error ("Unexpected " ^ snd(MatitaExcPp.to_string exn));
            assert false
      in
       compact (compile options fname)
    ;;

    let load_deps_file = Librarian.load_deps_file;;

  end 

module Make = Librarian.Make(F) 

(* FINE EX MATITACLIB *)



(* this function calls the parser in a way that it does not perform inclusions,
 * so that we can ensure the inclusion is performed after the included file 
 * is compiled (if needed). matitac does not need that, since it compiles files
 * in the good order, here files may be compiled on demand. *)
let wrap_with_make include_paths f x = 
  match f x with
     (GrafiteAst.Executable
       (_,GrafiteAst.NCommand (_,GrafiteAst.Include (_,_,mafilename)))) as cmd
     ->
      let root, buri, _, tgt = 
        try Librarian.baseuri_of_script ~include_paths mafilename
        with Librarian.NoRootFor _ -> 
          HLog.error ("The included file '"^mafilename^"' has no root file,");
          HLog.error "please create it.";
          raise (Failure ("No root file for "^mafilename))
      in
      if Make.make root [tgt] then
       cmd
      else raise (Failure ("Compiling: " ^ tgt))
   | cmd -> cmd
;;

let toplevel status ~include_paths text =
 wrap_with_make include_paths
  (GrafiteParser.parse_statement status)
    (Ulexing.from_utf8_string text)
;;
