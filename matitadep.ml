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

module GA = GrafiteAst 
module U = UriManager
                
let main () =
  (* all are maps from "file" to "something" *)
  let include_deps = Hashtbl.create 13 in
  let baseuri_of = Hashtbl.create 13 in
  let baseuri_of_inv = Hashtbl.create 13 in
  let dot_file = ref "" in
  (* helpers *)
  let include_paths = ref [] in
  let baseuri_of_script s = 
     try Hashtbl.find baseuri_of s 
     with Not_found -> 
       let _,b,_,_ = 
         Librarian.baseuri_of_script ~include_paths:!include_paths s 
       in
       Hashtbl.add baseuri_of s b; 
       Hashtbl.add baseuri_of_inv b s; 
       b
  in
  let script_of_baseuri ma b =
    try Some (Hashtbl.find baseuri_of_inv b)
    with Not_found -> 
      HLog.error ("Skipping dependency of '"^ma^"' over '"^b^"'");
      HLog.error ("Plase include the file defining such baseuri, or fix");
      HLog.error ("possibly incorrect verbatim URIs in the .ma file.");
      None
  in
  let buri alias = U.buri_of_uri (U.uri_of_string alias) in
  let resolve alias current_buri =
    let buri = buri alias in
    if buri <> current_buri then Some buri else None 
  in
  (* initialization *)
  MatitaInit.add_cmdline_spec 
    ["-dot", Arg.Set_string dot_file,
    "<file> Save dependency graph in dot format to the given file";];
  MatitaInit.parse_cmdline_and_configuration_file ();
  MatitaInit.initialize_environment ();
  let args = 
      let roots = Librarian.find_roots_in_dir (Sys.getcwd ()) in
      match roots with
      | [] -> 
         prerr_endline ("No roots found in " ^ Sys.getcwd ());
         exit 1
      | [x] -> 
         Sys.chdir (Filename.dirname x);
         let opts = Librarian.load_root_file "root" in
         include_paths := 
           (try Str.split (Str.regexp " ") (List.assoc "include_paths" opts)
           with Not_found -> []) @ 
           (Helm_registry.get_list Helm_registry.string "matita.includes");
         HExtlib.find ~test:(fun x -> Filename.check_suffix x ".ma") "."
      | _ ->
         let roots = List.map (HExtlib.chop_prefix (Sys.getcwd()^"/")) roots in
         prerr_endline ("Too many roots found:\n\t" ^ String.concat "\n\t" roots);
         prerr_endline ("\nEnter one of these directories and retry");
         exit 1
  in
  let ma_files = args in
  (* here we go *)
  (* fills:
              Hashtbl.add include_deps     ma_file ma_file
              Hashtbl.add include_deps_dot ma_file baseuri
  *)
  List.iter (fun ma_file -> ignore (baseuri_of_script ma_file)) ma_files;
  List.iter
   (fun ma_file -> 
      let ma_baseuri = baseuri_of_script ma_file in
      let dependencies = DependenciesParser.deps_of_file ma_file in
      List.iter 
       (function
         | DependenciesParser.UriDep uri -> 
            let uri = UriManager.string_of_uri uri in
            if not (Http_getter_storage.is_legacy uri) then
              let dep = resolve uri ma_baseuri in
              (match dep with 
              | None -> ()
              | Some u -> 
                  match script_of_baseuri ma_file u with
                  | Some d -> Hashtbl.add include_deps ma_file d
                  | None -> ())                
         | DependenciesParser.IncludeDep path -> 
                ignore (baseuri_of_script path);
                Hashtbl.add include_deps ma_file path)
       dependencies)
   ma_files;
  (* dot generation *)
  if !dot_file <> "" then 
    begin
      let oc = open_out !dot_file in
      let fmt = Format.formatter_of_out_channel oc in 
      GraphvizPp.Dot.header fmt;
      List.iter
       (fun ma_file -> 
        let deps = Hashtbl.find_all include_deps ma_file in
        let deps = 
          HExtlib.filter_map 
            (fun u -> 
              try Some (Hashtbl.find baseuri_of_inv u) 
              with Not_found -> None) 
            deps 
        in
        let deps = List.fast_sort Pervasives.compare deps in
        let deps = HExtlib.list_uniq deps in
        GraphvizPp.Dot.node ma_file fmt;
        List.iter (fun dep -> GraphvizPp.Dot.edge ma_file dep fmt) deps)
       ma_files;
      GraphvizPp.Dot.trailer fmt;
      close_out oc
    end;
  (* generate regular depend output *)
  let fix_name f =
    let f = 
      if Pcre.pmatch ~pat:"^\\./" f then
        String.sub f 2 (String.length f - 2)
      else 
        f
    in 
      HExtlib.normalize_path f
  in
  let deps =
    List.fold_left
     (fun acc ma_file -> 
      let deps = Hashtbl.find_all include_deps ma_file in
      let deps = List.fast_sort Pervasives.compare deps in
      let deps = HExtlib.list_uniq deps in
      let deps = List.map fix_name deps in
      (fix_name ma_file, deps) :: acc)
     [] ma_files
  in
  let extern = 
    List.fold_left
      (fun acc (_,d) -> 
        List.fold_left 
          (fun a x -> 
             if List.exists (fun (t,_) -> x=t) deps then a 
             else x::a) 
          acc d)
      [] deps
  in
  Librarian.write_deps_file (Sys.getcwd()) 
   (deps@HExtlib.list_uniq (List.sort Pervasives.compare (List.map (fun x ->
           x,[]) extern)))
;;

