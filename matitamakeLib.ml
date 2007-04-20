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

open Printf

let logger = fun mark -> 
  match mark with 
  | `Error -> HLog.error
  | `Warning -> HLog.warn
  | `Debug -> HLog.debug
  | `Message -> HLog.message

type development = 
  { root: string ; name: string }

let developments = ref []
  
let pool () = Helm_registry.get "matita.basedir" ^ "/matitamake/" ;;
let rootfile = "/root" ;;

let ls_dir dir = 
  try
    let d = Unix.opendir dir in
    let content = ref [] in
    try
      while true do
        let name = Unix.readdir d in
        if name <> "." && name <> ".." then
          content := name :: !content
      done;
      Some []
    with End_of_file -> Unix.closedir d; Some !content
  with Unix.Unix_error _ -> None

let initialize () = 
  (* create a base env if none *)
  HExtlib.mkdir (pool ());
  (* load developments *)
  match ls_dir (pool ()) with
  | None -> logger `Error ("Unable to list directory " ^ pool ()) 
  | Some l -> 
      List.iter 
        (fun name -> 
          let root = 
            try 
              Some (HExtlib.input_file (pool () ^ name ^ rootfile))
            with Unix.Unix_error _ -> 
              logger `Warning ("Malformed development " ^ name);
              None
          in 
          match root with 
          | None -> ()
          | Some root -> 
              developments := {root = root ; name = name} :: !developments) 
      l

(* finds the makefile path for development devel *)
let makefile_for_development devel =
  let develdir = pool () ^ devel.name in
  develdir ^ "/makefile"

let dot_for_development devel = 
  let dot_fname = pool () ^ devel.name ^ "/depend.dot" in
  if Sys.file_exists dot_fname then Some dot_fname else None

(* given a dir finds a development that is radicated in it or below *)
let development_for_dir dir =
  let is_prefix_of d1 d2 =
    let len1 = String.length d1 in
    let len2 = String.length d2 in
    if len2 < len1 then 
      false
    else
      let pref = String.sub d2 0 len1 in
      pref = d1 && d2.[len1] = '/'
  in
  try
    Some (List.find (fun d -> is_prefix_of d.root dir) !developments)
  with Not_found | Failure _ -> None

let development_for_name name =
  try 
    Some (List.find (fun d -> d.name = name) !developments)
  with Not_found -> None

(* dumps the deveopment to disk *)
let dump_development devel =
  let devel_dir = pool () ^ devel.name in 
  HExtlib.mkdir devel_dir;
  HExtlib.output_file ~filename:(devel_dir ^ rootfile) ~text:devel.root

let list_known_developments () = 
  List.map (fun r -> r.name,r.root) !developments

let am_i_opt = lazy (
  if Pcre.pmatch ~pat:"\\.opt$" Sys.argv.(0) then ".opt" else "")
  
let rebuild_makefile development = 
  let makefilepath = makefile_for_development development in
  let template = 
    HExtlib.input_file BuildTimeConf.matitamake_makefile_template 
  in
  let ext = Lazy.force am_i_opt in
  let cc = BuildTimeConf.runtime_base_dir ^ "/matitac" ^ ext in
  let rm = BuildTimeConf.runtime_base_dir ^ "/matitaclean" ^ ext in
  let mm = BuildTimeConf.runtime_base_dir ^ "/matitadep" ^ ext in
  let df = pool () ^ development.name ^ "/depend" in
  let template = Pcre.replace ~pat:"@ROOT@" ~templ:development.root template in
  let template = Pcre.replace ~pat:"@CC@" ~templ:cc template in
  let template = Pcre.replace ~pat:"@DEP@" ~templ:mm template in
  let template = Pcre.replace ~pat:"@DEPFILE@" ~templ:df template in
  let template = Pcre.replace ~pat:"@CLEAN@" ~templ:rm template in
  HExtlib.output_file ~filename:makefilepath ~text:template
  
let rebuild_makefile_devel development = 
  let path = development.root ^ "/makefile" in
  if not (Sys.file_exists path) then
    begin
      let template = 
        HExtlib.input_file BuildTimeConf.matitamake_makefile_template_devel
      in
      let template = 
        Pcre.replace ~pat:"@MATITA_RT_BASE_DIR@"
          ~templ:BuildTimeConf.runtime_base_dir template
      in
      HExtlib.output_file ~filename:path ~text:template
    end
  
(* creates a new development if possible *)
let initialize_development name dir =
  let name = Pcre.replace ~pat:" " ~templ:"_" name in 
  let dev = {name = name ; root = dir} in
  dump_development dev;
  rebuild_makefile dev;
  rebuild_makefile_devel dev;
  developments := dev :: !developments;
  Some dev

let make chdir args = 
  let old = Unix.getcwd () in
  try
    Unix.chdir chdir;
    let cmd = String.concat " " ("make" :: List.map Filename.quote args) in
    let rc = Unix.system cmd in
    Unix.chdir old;
    match rc with
    | Unix.WEXITED 0 -> true
    | Unix.WEXITED i -> logger `Error ("make returned " ^ string_of_int i);false
    | _ -> logger `Error "make STOPPED or SIGNALED!";false
  with Unix.Unix_error (_,cmd,err) -> 
    logger `Warning ("Unix Error: " ^ cmd ^ ": " ^ err);
    false
      
let call_make ?matita_flags development target make =
  let matita_flags = 
    let already_defined = 
      match matita_flags with 
      | None -> (try Sys.getenv "MATITA_FLAGS" with Not_found -> "")
      | Some s -> s 
    in
    already_defined ^ 
      if Helm_registry.get_bool "matita.bench" then "-bench" else ""
  in
  let csc = try ["SRC=" ^ Sys.getenv "SRC"] with Not_found -> [] in
  rebuild_makefile development;
  let makefile = makefile_for_development development in
  let nodb =
    Helm_registry.get_opt_default Helm_registry.bool ~default:false "db.nodb"
  in
  let flags = [] in 
  let flags = flags @ if nodb then ["NODB=true"] else [] in
  let flags =
    try
      flags @ [ sprintf "MATITA_FLAGS=\"%s\"" matita_flags ]
    with Not_found -> flags in
  let flags = flags @ csc in
  let args = 
    ["--no-print-directory"; "-s"; "-k"; "-f"; makefile; target] @ flags 
  in
 (*    prerr_endline (String.concat " " args);   *)
  make development.root args
      
let build_development ?matita_flags ?(target="all") development =
  call_make ?matita_flags development target make

(* not really good vt100 *)
let vt100 s =
  let rex = Pcre.regexp "\\[[0-9;]+m" in
  let rex_i = Pcre.regexp "^Info" in
  let rex_w = Pcre.regexp "^Warning" in
  let rex_e = Pcre.regexp "^Error" in
  let rex_d = Pcre.regexp "^Debug" in
  let rex_noendline = Pcre.regexp "\\n" in
  let s = Pcre.replace ~rex:rex_noendline s in
  let tokens = Pcre.split ~rex s in
  let logger = ref HLog.message in
  let rec aux = 
    function
    | [] -> ()
    | s::tl ->
        (if Pcre.pmatch ~rex:rex_i s then
          logger := HLog.message
        else if Pcre.pmatch ~rex:rex_w s then
          logger := HLog.warn
        else if Pcre.pmatch ~rex:rex_e s then
          logger := HLog.error
        else if Pcre.pmatch ~rex:rex_d s then
          logger := HLog.debug
        else 
          !logger s);
        aux tl
  in
  aux tokens
  

let mk_maker refresh_cb =
  (fun chdir args ->
    let out_r,out_w = Unix.pipe () in
    let err_r,err_w = Unix.pipe () in
    let pid = ref ~-1 in
    ignore(Sys.signal Sys.sigchld (Sys.Signal_ignore));
    try
(*       prerr_endline (String.concat " " args); *)
      let argv = Array.of_list ("make"::args) in
      pid := Unix.create_process "make" argv Unix.stdin out_w err_w;
      Unix.close out_w;
      Unix.close err_w;
      let buf = String.create 1024 in
      let rec aux = function 
        | f::tl ->
            let len = Unix.read f buf 0 1024 in
            if len = 0 then 
              raise 
                (Unix.Unix_error 
                  (Unix.EPIPE,"read","len = 0 (matita internal)"));
            vt100 (String.sub buf 0 len);
            aux tl
        | _ -> ()
      in
      while true do
        let r,_,_ = Unix.select [out_r; err_r] [] [] (-. 1.) in
        aux r;
        refresh_cb ()
      done;
      true
    with 
    | Unix.Unix_error (_,"read",_)
    | Unix.Unix_error (_,"select",_) -> true)

let build_development_in_bg ?matita_flags ?(target="all") refresh_cb development =
  call_make ?matita_flags development target (mk_maker refresh_cb)

let clean_development ?matita_flags development =
  call_make ?matita_flags development "clean" make

let clean_development_in_bg ?matita_flags  refresh_cb development =
  call_make development ?matita_flags  "clean" (mk_maker refresh_cb)

let destroy_development_aux development clean_development =
  let delete_development development = 
    let unlink = HExtlib.safe_remove in
    let rmdir dir =
      try
        Unix.rmdir dir 
      with Unix.Unix_error _ -> 
        logger `Warning ("Unable to remove dir " ^ dir);
        match ls_dir dir with
        | None -> logger `Error ("Unable to list directory " ^ dir) 
        | Some [] -> ()
        | Some l -> logger `Error ("The directory is not empty")
    in
    unlink (makefile_for_development development);
    unlink (pool () ^ development.name ^ rootfile);
    unlink (pool () ^ development.name ^ "/depend");
    unlink (pool () ^ development.name ^ "/depend.errors");
    unlink (pool () ^ development.name ^ "/depend.dot");
    rmdir (pool () ^ development.name);
    developments := 
      List.filter (fun d -> d.name <> development.name) !developments
  in
  if not(clean_development development) then
    begin
      logger `Warning "Unable to clean the development problerly.";
      logger `Warning "This may cause garbage."
    end;
  delete_development development 
 
let destroy_development ?matita_flags development = 
  destroy_development_aux development (clean_development ?matita_flags)

let destroy_development_in_bg ?matita_flags refresh development = 
  destroy_development_aux development 
    (clean_development_in_bg refresh ?matita_flags ) 
  
let root_for_development development = development.root
let name_for_development development = development.name

let publish_development_bstract build clean devel = 
  let matita_flags = "\"-system\"" in
  HLog.message "cleaning the development before publishing";
  if clean ~matita_flags:"" devel then
    begin
      HLog.message "rebuilding the development in 'system' space";
      if build ~matita_flags devel then
        begin
          HLog.message "publishing succeded";
          true
        end
      else
        begin
          HLog.error "building process failed, reverting";
          if not (clean ~matita_flags devel) then
            HLog.error "cleaning failed, end of the world (2)";
          false
        end
    end
  else
    (HLog.error "unable to clean the development, publishing failed"; false)
  
let publish_development devel = 
  publish_development_bstract 
    (fun ~matita_flags devel -> build_development ~matita_flags devel) 
    (fun ~matita_flags devel -> clean_development ~matita_flags devel) devel
let publish_development_in_bg cb devel = 
  publish_development_bstract 
    (fun ~matita_flags devel -> build_development_in_bg cb ~matita_flags devel)
    (fun ~matita_flags devel -> clean_development_in_bg cb ~matita_flags devel)
    devel

