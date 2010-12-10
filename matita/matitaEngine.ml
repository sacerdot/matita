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
open GrafiteTypes
open Printf

exception TryingToAdd of string Lazy.t
exception EnrichedWithStatus of exn * GrafiteTypes.status
exception AlreadyLoaded of string Lazy.t
exception FailureCompiling of string * exn
exception CircularDependency of string

let debug = false ;;
let debug_print = if debug then prerr_endline else ignore ;;

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

let clean_exit baseuri exn =
  LibraryClean.clean_baseuris ~verbose:false [baseuri];
  raise (FailureCompiling (baseuri,exn))
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

let rec get_ast status ~compiling ~include_paths strm = 
  match GrafiteParser.parse_statement status strm with
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
       ignore (assert_ng ~compiling ~include_paths ~root tgt);
       cmd
   | cmd -> cmd

and eval_from_stream ~compiling ~include_paths ?do_heavy_checks status str cb =
 let matita_debug = Helm_registry.get_bool "matita.debug" in
 let rec loop status =
  let stop,status = 
   try
     let cont =
       try Some (get_ast status ~compiling ~include_paths str)
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
                raise (TryingToAdd (lazy (GrafiteAstPp.pp_alias value)))
          | _ -> assert false
        in
         false, status
   with exn when not matita_debug ->
     raise (EnrichedWithStatus (exn, status))
  in
  if stop then status else loop status
 in
  loop status

and compile ~compiling ~include_paths fname =
  if List.mem fname compiling then raise (CircularDependency fname);
  let compiling = fname::compiling in
  let matita_debug = Helm_registry.get_bool "matita.debug" in
  let root,baseuri,fname,_tgt = 
    Librarian.baseuri_of_script ~include_paths fname in
  if Http_getter_storage.is_read_only baseuri then assert false;
  activate_extraction baseuri fname ;
  (* MATITA 1.0: debbo fare time_travel sulla ng_library? *)
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
    let grammar = CicNotationParser.level2_ast_grammar grafite_status in
    let buf =
     Grammar.parsable grammar
      (Obj.magic (Ulexing.from_utf8_channel (open_in fname)))
    in
    let print_cb =
      if not (Helm_registry.get_bool "matita.verbose") then (fun _ _ -> ())
      else pp_ast_statement
    in
    let grafite_status =
     eval_from_stream ~compiling ~include_paths grafite_status buf print_cb in
    let elapsed = Unix.time () -. time in
     (if Helm_registry.get_bool "matita.moo" then begin
       GrafiteTypes.Serializer.serialize ~baseuri:(NUri.uri_of_string baseuri)
        ~dependencies:grafite_status#dependencies grafite_status#dump
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
     pp_times fname true big_bang big_bang_u big_bang_s
(* MATITA 1.0: debbo fare time_travel sulla ng_library?
     LexiconSync.time_travel 
       ~present:lexicon_status ~past:initial_lexicon_status;
*))
  with 
  (* all exceptions should be wrapped to allow lexicon-undo (LS.time_travel) *)
  | exn when not matita_debug ->
(* MATITA 1.0: debbo fare time_travel sulla ng_library?
       LexiconSync.time_travel ~present:lexicon ~past:initial_lexicon_status;
 *       *)
      pp_times fname false big_bang big_bang_u big_bang_s;
      clean_exit baseuri exn

(* BIG BUG: if a file recursively includes itself, anything can happen,
 * from divergence to inclusion of an old copy of itself *)
and assert_ng ~compiling ~include_paths ~root mapath =
 let root',baseuri,fullmapath,_ = Librarian.baseuri_of_script ~include_paths mapath in
 assert (root=root');
 let baseuri = NUri.uri_of_string baseuri in
 let ngpath = NCicLibrary.ng_path_of_baseuri baseuri in
 let ngtime =
  try
   Some (Unix.stat ngpath).Unix.st_mtime
  with Unix.Unix_error (Unix.ENOENT, "stat", f) when f = ngpath -> None in
 let matime =
  try (Unix.stat fullmapath).Unix.st_mtime
  with Unix.Unix_error (Unix.ENOENT, "stat", f) when f = fullmapath -> assert false
 in
 let to_be_compiled =
  match ngtime with
     Some ngtime ->
      let preamble = GrafiteTypes.Serializer.dependencies_of baseuri in
      let children_bad =
       List.exists (assert_ng ~compiling ~include_paths ~root) preamble
      in
       children_bad || matime > ngtime
   | None -> true
 in
  if not to_be_compiled then false
  else
   (* MATITA 1.0: SHOULD TAKE THIS FROM THE STATUS *)
   if List.mem baseuri (NCicLibrary.get_already_included ()) then
     (* maybe recompiling it I would get the same... *)
     raise (AlreadyLoaded (lazy mapath))
   else
    (compile ~compiling ~include_paths fullmapath; true)
;;

let assert_ng = assert_ng ~compiling:[]
let get_ast = get_ast ~compiling:[]
