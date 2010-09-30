(* Copyright (C) 2000, HELM Team.
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
 * http://cs.unibo.it/helm/.
 *)

module R  = Helm_registry
module X  = HExtlib
module HG = Http_getter
module GA = GrafiteAst

module T = Types
module G = Grafite
module O = Options

type script = {
   name    : string;
   is_ma   : bool;
   contents: T.items
}

type status = {
   heading_path: string;
   heading_lines: int;
   input_package: string;
   output_package: string;
   input_base_uri: string;
   output_base_uri: string;
   input_path: string;
   output_path: string;
   input_type: T.input_kind;
   output_type: T.output_kind;
   input_ext: string;
   remove_lines: int;
   excludes: string list;
   includes: (string * string) list;
   iparams: (string * string) list;
   coercions: (string * string) list;
   files: string list;
   requires: (string * string) list;
   scripts: script array
}

let default_script = { 
   name = ""; is_ma = false; contents = []
}

let default_scripts = 2

let suffix = ".conf.xml"

let load_registry registry =
   let registry = 
      if Filename.check_suffix registry suffix then registry
      else registry ^ suffix
   in
   Printf.eprintf "reading configuration %s ...\n" registry; flush stderr;
   R.load_from registry

let set_files st =
   let eof ich = try Some (input_line ich) with End_of_file -> None in
   let trim l = Filename.chop_extension (Str.string_after l 2) in 
   let cmd = Printf.sprintf "cd %s && find -name '*%s'" st.input_path st.input_ext in
   let ich = Unix.open_process_in cmd in
   let rec aux files = match eof ich with
      | None   -> List.rev files
      | Some l ->
	 let l = trim l in
	 if List.mem l st.excludes then aux files else 
	 if !O.sources = [] || List.mem l !O.sources then aux (l :: files) else
	 aux files
   in
   let files = aux [] in
   let _ = Unix.close_process_in ich in
   {st with files = files}

let set_requires st =
   let map file = (Filename.basename file, file) in
   let requires = List.rev_map map st.files in
   {st with requires = requires}

let init () = 
   let transcript_dir = Filename.dirname Sys.argv.(0) in
   let default_registry = Filename.concat transcript_dir "transcript" in
   let matita_registry = Filename.concat !O.cwd "matita" in
   load_registry default_registry;
   load_registry matita_registry;
   HG.init ()

let make registry =
   let id x = x in
   let get_pairs = R.get_list (R.pair id id) in 
   let get_input_type key1 key2 =
      match R.get_string key1, R.get_string key2 with
         | "gallina8", _ -> T.Gallina8, ".v", []
	 | "grafite", "" -> T.Grafite "", ".ma", []
	 | "grafite", s  -> T.Grafite s, ".ma", [s]
	 | s, _          -> failwith ("unknown input type: " ^ s)
   in
   let get_output_type key =
      match R.get_string key with
         | "procedural"  -> T.Procedural
	 | "declarative" -> T.Declarative
	 | s             -> failwith ("unknown output type: " ^ s)
   in
   load_registry registry;
   let input_type, input_ext, excludes = 
      get_input_type "package.input_type" "package.theory_file"
   in 
   let st = {
      heading_path = R.get_string "transcript.heading_path";
      heading_lines = R.get_int "transcript.heading_lines";
      input_package = R.get_string "package.input_name";
      output_package = R.get_string "package.output_name";
      input_base_uri = R.get_string "package.input_base_uri";
      output_base_uri = R.get_string "package.output_base_uri";
      input_path = R.get_string "package.input_path";
      output_path = R.get_string "package.output_path";
      input_type = input_type;
      output_type = get_output_type "package.output_type";
      input_ext = input_ext;
      remove_lines = R.get_int "package.heading_lines";
      excludes = excludes;
      includes = get_pairs "package.include";
      iparams = get_pairs "package.inline";
      coercions = get_pairs "package.coercion";
      files = [];
      requires = [];
      scripts = Array.make default_scripts default_script
   } in
   let st = {st with
      heading_path = Filename.concat !O.cwd st.heading_path;
      input_path = Filename.concat !O.cwd st.input_path;
      output_path = Filename.concat !O.cwd st.output_path
   } in
   prerr_endline "reading file names ...";
   let st = set_files st in
   let st = set_requires st in
   st

let get_index st name = 
   let rec get_index name i =
      if i >= Array.length st.scripts then None else 
      if st.scripts.(i).name = name then Some i else 
      get_index name (succ i)
   in
   match get_index name 0, get_index "" 0 with
      | Some i, _ | _, Some i -> i
      | None, None            -> failwith "not enought script entries"

let is_ma st name =
   let i = get_index st name in
   let script = st.scripts.(i) in
   st.scripts.(i) <- {script with is_ma = true}

let set_items st name items =
   let i = get_index st name in
   let script = st.scripts.(i) in
   let contents = List.rev_append (X.list_uniq items) script.contents in
   st.scripts.(i) <- {script with name = name; contents = contents}
   
let set_heading st name = 
   let heading = st.heading_path, st.heading_lines in
   set_items st name [T.Heading heading] 
   
let require st name moo inc =
   set_items st name [T.Include (moo, inc)]

let get_coercion st str =
   try List.assoc str st.coercions with Not_found -> ""

let make_path path =
   List.fold_left Filename.concat "" (List.rev path)

let make_prefix path =
   String.concat "__" (List.rev path) ^ "__"

let make_script_name st script name = 
   let ext = if script.is_ma then ".ma" else ".mma" in
   Filename.concat st.output_path (name ^ ext)

let get_iparams st name =
   let debug debug = GA.IPDebug debug in
   let map = function
      | "comments"   -> GA.IPComments
      | "nodefaults" -> GA.IPNoDefaults
      | "coercions"  -> GA.IPCoercions
      | "cr"         -> GA.IPCR
      | s            -> 
	 try Scanf.sscanf s "debug-%u" debug with
	    | Scanf.Scan_failure _
	    | Failure _
	    | End_of_file ->
	       failwith ("unknown inline parameter: " ^ s)
   in
   List.map map (X.list_assoc_all name st.iparams) 

let commit st name =
   let i = get_index st name in
   let script = st.scripts.(i) in
   let path = Filename.concat st.output_path (Filename.dirname name) in
   let name = make_script_name st script name in
   let cmd = Printf.sprintf "mkdir -p %s" path in
   let _ = Sys.command cmd in
   let och = open_out name in
   G.commit st.output_type och script.contents;
   close_out och;
   st.scripts.(i) <- default_script

let produce st =
   let init name = set_heading st name in
   let partition = function 
      | T.Coercion (false, _)
      | T.Notation (false, _) -> false
      | _                     -> true
   in
   let get_items = match st.input_type with
      | T.Gallina8  -> Gallina8Parser.items Gallina8Lexer.token
      | T.Grafite _ -> GrafiteParser.items GrafiteLexer.token
   in
   let produce st name =
      let in_base_uri = Filename.concat st.input_base_uri name in
      let out_base_uri = Filename.concat st.output_base_uri name in
      let filter path = function
         | T.Inline (b, k, obj, p, f, params)   -> 
	    let obj, p = 
	       if b then Filename.concat (make_path path) obj, make_prefix path
	       else obj, p
	    in
	    let ext = G.string_of_inline_kind k in
	    let s = Filename.concat in_base_uri (obj ^ ext) in
	    let params = 
	       params @
	       get_iparams st "*" @
	       get_iparams st ("*" ^ ext) @
	       get_iparams st (Filename.concat name obj)
	    in
	    path, Some (T.Inline (b, k, s, p, f, params))
	 | T.Include (moo, s)           ->
	    begin 
	       try path, Some (T.Include (moo, List.assoc s st.requires))
	       with Not_found -> path, None
	    end
	 | T.Coercion (b, obj)          ->
	    let str = get_coercion st obj in
	    if str <> "" then path, Some (T.Coercion (b, str)) else
	    let base_uri = if b then out_base_uri else in_base_uri in
	    let s = obj ^ G.string_of_inline_kind T.Con in
	    path, Some (T.Coercion (b, Filename.concat base_uri s))
	 | T.Section (b, id, _) as item ->
	    let path = if b then id :: path else List.tl path in
	    path, Some item
	 | T.Verbatim s                 ->
	    let pat, templ = st.input_base_uri, st.output_base_uri in
	    path, Some (T.Verbatim (Pcre.replace ~pat ~templ s)) 
	 | item                         -> path, Some item
      in
      let set_includes st name =
      	 try require st name true (List.assoc name st.includes) 
	 with Not_found -> ()
      in
      let rec remove_lines ich n =
         if n > 0 then let _ =  input_line ich in remove_lines ich (pred n)
      in
      Printf.eprintf "processing file name: %s ...\n" name; flush stderr;
      let file = Filename.concat st.input_path name in
      let ich = open_in (file ^ st.input_ext) in
      begin try remove_lines ich st.remove_lines with End_of_file -> () end;
      let lexbuf = Lexing.from_channel ich in
      try 
         let items = get_items lexbuf in close_in ich; 
	 let _, rev_items = X.list_rev_map_filter_fold filter [] items in
	 let items = List.rev rev_items in
	 let local_items, global_items = List.partition partition items in
	 let comment = T.Line (Printf.sprintf "From %s" name) in 
	 if global_items <> [] then 
	    set_items st st.input_package (comment :: global_items);
	 init name; 
	 begin match st.input_type with
	    | T.Grafite "" -> require st name false file
	    | _            -> require st name false st.input_package
	 end; 
	 set_includes st name; set_items st name local_items; commit st name
      with e -> 
         prerr_endline (Printexc.to_string e); close_in ich 
   in
   is_ma st st.input_package;
   init st.input_package; require st st.input_package false "preamble"; 
   match st.input_type with
      | T.Grafite "" ->
         List.iter (produce st) st.files
      | T.Grafite s  ->
         let theory = Filename.concat st.input_path s in
	 require st st.input_package false theory;
         List.iter (produce st) st.files;
         commit st st.input_package
      | _            ->
         List.iter (produce st) st.files;
         commit st st.input_package
