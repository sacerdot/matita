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

module GA = GrafiteAst 
module U = UriManager
                
let obj_file_of_baseuri writable baseuri = 
  try 
    LibraryMisc.obj_file_of_baseuri 
     ~must_exist:true ~baseuri ~writable
  with 
  | Http_getter_types.Unresolvable_URI _ 
  | Http_getter_types.Key_not_found _ ->  
    LibraryMisc.obj_file_of_baseuri 
     ~must_exist:false ~baseuri ~writable:true
;;

let main () =
  (* all are maps from "file" to "something" *)
  let include_deps = Hashtbl.create (Array.length Sys.argv) in
  let include_deps_dot = Hashtbl.create (Array.length Sys.argv) in
  let baseuri_of = Hashtbl.create (Array.length Sys.argv) in
  let baseuri_of_inv = Hashtbl.create (Array.length Sys.argv) in
  let uri_deps = Hashtbl.create (Array.length Sys.argv) in
  let buri alias = U.buri_of_uri (U.uri_of_string alias) in
  let resolve alias current_buri =
    let buri = buri alias in
    if buri <> current_buri then Some buri else None in
  MatitaInit.fill_registry ();
  let dot_file = ref "" in
  MatitaInit.add_cmdline_spec 
    ["-dot", Arg.Set_string dot_file,
      "<file> Save dependency graph in dot format to the given file"];
  MatitaInit.parse_cmdline ();
  MatitaInit.load_configuration_file ();
  let include_paths =
   Helm_registry.get_list Helm_registry.string "matita.includes" in
  let args = Helm_registry.get_list Helm_registry.string "matita.args" in
  if args = [] then
    begin
      prerr_endline "At least one .ma file must be specified";
      exit 1
    end;
  let ma_files = args in
  List.iter
   (fun ma_file -> 
    let ic = open_in ma_file in
      let istream = Ulexing.from_utf8_channel ic in
      let dependencies = DependenciesParser.parse_dependencies istream in
    close_in ic;
    List.iter 
     (function
       | DependenciesParser.UriDep uri -> 
          let uri = UriManager.string_of_uri uri in
          if not (Http_getter_storage.is_legacy uri) then
            Hashtbl.add uri_deps ma_file uri
       | DependenciesParser.BaseuriDep uri -> 
          let uri = Http_getter_misc.strip_trailing_slash uri in
          Hashtbl.add baseuri_of ma_file uri;
          Hashtbl.add baseuri_of_inv uri ma_file
       | DependenciesParser.IncludeDep path -> 
          try 
            let baseuri,_ =
              DependenciesParser.baseuri_of_script ~include_paths path in
            if not (Http_getter_storage.is_legacy baseuri) then
              (let moo_file = obj_file_of_baseuri false baseuri in
              Hashtbl.add include_deps ma_file moo_file;
              Hashtbl.add include_deps_dot ma_file baseuri)
          with Sys_error _ -> 
            HLog.warn 
              ("Unable to find " ^ path ^ " that is included in " ^ ma_file))
     dependencies)
   ma_files;
  Hashtbl.iter 
    (fun file alias -> 
      try 
        let dep = resolve alias (Hashtbl.find baseuri_of file) in
        match dep with 
        | None -> ()
        | Some u -> 
           Hashtbl.add include_deps file (obj_file_of_baseuri false u)
      with Not_found -> 
        prerr_endline ("File "^ file^" has no baseuri. Use set baseuri");
        exit 1)
  uri_deps;
  if !dot_file <> "" then (* generate dependency graph if required *)
    begin
      let oc = open_out !dot_file in
      let fmt = Format.formatter_of_out_channel oc in 
      GraphvizPp.Dot.header (* ~graph_attrs:["rankdir","LR"] *) fmt;
      let gcp x y = 
      (* explode and implode from the OCaml Expert FAQ. *)
        let explode s =
          let rec exp i l =
            if i < 0 then l else exp (i - 1) (s.[i] :: l) in
          exp (String.length s - 1) []
        in      
        let implode l =
          let res = String.create (List.length l) in
          let rec imp i = function
          | [] -> res
          | c :: l -> res.[i] <- c; imp (i + 1) l in
          imp 0 l
        in
        let rec aux = function
          | x::tl1,y::tl2 when x = y -> x::(aux (tl1,tl2))
          | _ -> [] 
        in
        implode (aux (explode x,explode y))
      in
      let max_path = List.hd ma_files in 
      let max_path = List.fold_left gcp max_path ma_files in
      let short x = Pcre.replace ~pat:("^"^max_path) x in
      List.iter
       (fun ma_file -> 
        let deps = Hashtbl.find_all include_deps_dot ma_file in
        let deps = 
          HExtlib.filter_map 
            (fun u -> 
              try Some (Hashtbl.find baseuri_of_inv u) 
              with Not_found -> None) 
            deps 
        in
        let deps = List.fast_sort Pervasives.compare deps in
        let deps = HExtlib.list_uniq deps in
        GraphvizPp.Dot.node (short ma_file) fmt;
        List.iter (fun dep -> GraphvizPp.Dot.edge (short ma_file) (short dep) fmt) deps)
       ma_files;
      GraphvizPp.Dot.trailer fmt;
      close_out oc
    end;
  List.iter (* (always) generate regular .depend output *)
   (fun ma_file -> 
     try
      let deps = Hashtbl.find_all include_deps ma_file in
      let deps = List.fast_sort Pervasives.compare deps in
      let deps = HExtlib.list_uniq deps in
      let deps = ma_file :: deps in
      let baseuri = Hashtbl.find baseuri_of ma_file in
      let moo = obj_file_of_baseuri true baseuri in
      Printf.printf "%s: %s\n%s: %s\n%s: %s\n" 
        moo (String.concat " " deps)
        (Filename.basename(Pcre.replace ~pat:"ma$" ~templ:"mo" ma_file)) moo
        (Pcre.replace ~pat:"ma$" ~templ:"mo" ma_file) moo
     with Not_found -> 
       prerr_endline ("File "^ma_file^" has no baseuri. Use set baseuri");
       exit 1)
    ma_files

