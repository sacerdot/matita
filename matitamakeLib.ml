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
;;

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
;;

(* given a dir finds a development that is radicated in it or below *)
let development_for_dir dir =
  let is_prefix_of d1 d2 =
    let len1 = String.length d1 in
    let len2 = String.length d2 in
    if len2 < len1 then 
      false
    else
      let pref = String.sub d2 0 len1 in
      pref = d1
  in
  (* it must be unique *)
  try
    Some (List.find (fun d -> is_prefix_of d.root dir) !developments)
  with Not_found -> None
;;

let development_for_name name =
  try 
    Some (List.find (fun d -> d.name = name) !developments)
  with Not_found -> None

(* dumps the deveopment to disk *)
let dump_development devel =
  let devel_dir = pool () ^ devel.name in 
  HExtlib.mkdir devel_dir;
  HExtlib.output_file ~filename:(devel_dir ^ rootfile) ~text:devel.root
;;

let list_known_developments () = 
  List.map (fun r -> r.name,r.root) !developments

let am_i_opt () = 
  if Pcre.pmatch ~pat:"\\.opt$" Sys.argv.(0) then ".opt" else ""
  
let rebuild_makefile development = 
  let makefilepath = makefile_for_development development in
  let template = 
    HExtlib.input_file BuildTimeConf.matitamake_makefile_template 
  in
  let cc = BuildTimeConf.runtime_base_dir ^ "/matitac" ^ am_i_opt () in
  let rm = BuildTimeConf.runtime_base_dir ^ "/matitaclean" ^ am_i_opt () in
  let mm = BuildTimeConf.runtime_base_dir ^ "/matitadep" ^ am_i_opt () in
  let df = pool () ^ development.name ^ "/depend" in
  let template = Pcre.replace ~pat:"@ROOT@" ~templ:development.root template in
  let template = Pcre.replace ~pat:"@CC@" ~templ:cc template in
  let template = Pcre.replace ~pat:"@DEP@" ~templ:mm template in
  let template = Pcre.replace ~pat:"@DEPFILE@" ~templ:df template in
  let template = Pcre.replace ~pat:"@CLEAN@" ~templ:rm template in
  HExtlib.output_file ~filename:makefilepath ~text:template
  
(* creates a new development if possible *)
let initialize_development name dir =
  let name = Pcre.replace ~pat:" " ~templ:"_" name in 
  let dev = {name = name ; root = dir} in
  match development_for_dir dir with
  | Some d ->
      logger `Error 
        ("Directory " ^ dir ^ " is already handled by development " ^ d.name);
      logger `Error
        ("Development " ^ d.name ^ " is rooted in " ^ d.root); 
      logger `Error
        (dir ^ " is a subdir of " ^ d.root);
      None
  | None -> 
      dump_development dev;
      rebuild_makefile dev;
      developments := dev :: !developments;
      Some dev

let make chdir args = 
  let old = Unix.getcwd () in
  try
    Unix.chdir chdir;
    let rc = 
      Unix.system 
        (String.concat " " ("make"::(List.map Filename.quote args)))
    in
    Unix.chdir old;
    match rc with
    | Unix.WEXITED 0 -> true
    | Unix.WEXITED i -> logger `Error ("make returned " ^ string_of_int i);false
    | _ -> logger `Error "make STOPPED or SIGNALED!";false
  with Unix.Unix_error (_,cmd,err) -> 
    logger `Warning ("Unix Error: " ^ cmd ^ ": " ^ err);
    false
      
let call_make development target make =
  rebuild_makefile development;
  let makefile = makefile_for_development development in
  let nodb =
    Helm_registry.get_opt_default Helm_registry.bool ~default:false "db.nodb"
  in
  let flags = [] in
  let flags = flags @ if nodb then ["NODB=true"] else [] in
  let flags =
    try
      flags @ [ sprintf "MATITA_FLAGS=\"%s\"" (Sys.getenv "MATITA_FLAGS") ]
    with Not_found -> flags in
  make development.root 
    (["--no-print-directory"; "-s"; "-k"; "-f"; makefile; target]
    @ flags)
      
let build_development ?(target="all") development =
  call_make development target make

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

let build_development_in_bg ?(target="all") refresh_cb development =
  call_make development target (mk_maker refresh_cb)
;;

let clean_development development =
  call_make development "clean" make

let clean_development_in_bg refresh_cb development =
  call_make development "clean" (mk_maker refresh_cb)

let destroy_development_aux development clean_development =
  let delete_development development = 
    let unlink file =
      try 
        Unix.unlink file 
      with Unix.Unix_error _ -> logger `Debug ("Unable to delete " ^ file)
    in
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
 
let destroy_development development = 
  destroy_development_aux development clean_development

let destroy_development_in_bg refresh development = 
  destroy_development_aux development (clean_development_in_bg refresh) 
  
let root_for_development development = development.root
let name_for_development development = development.name

