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

module MK = MatitamakeLib ;;

let main () =
  MatitaInit.fill_registry ();
  MatitaInit.parse_cmdline ();
  MatitaInit.load_configuration_file ();
  MK.initialize ();
  let usage = ref (fun () -> ()) in
  let dev_of_name name = 
    match MK.development_for_name name with
    | None -> 
        prerr_endline ("Unable to find a development called " ^ name);
        exit 1
    | Some d -> d
  in
  let dev_for_dir dir =
    match MK.development_for_dir dir with
    | None -> 
        prerr_endline ("Unable to find a development holding directory: "^ dir);
        exit 1
    | Some d -> d
  in
  let init_dev args =
    let name, path =
      match args with
      | [ name; path ] when path.[0] = '/' -> name, path
      | [ name; path ] -> name, Unix.getcwd () ^ "/" ^ path
      | [ name ] -> name, Unix.getcwd ()
      | _ -> !usage (); (* should not be reached *) assert false
    in
    match MK.initialize_development name path with
    | None -> exit 2
    | Some _ -> exit 0
  in
  let list_dev args =
    if List.length args <> 0 then !usage ();
    match MK.list_known_developments () with
    | [] -> print_string "No developments found.\n"; exit 0
    | l ->
        List.iter 
          (fun (name, root) -> 
            print_string (Printf.sprintf "%-10s\trooted in %s\n" name root)) 
          l;
        exit 0
  in
  let destroy_dev args = 
    if List.length args <> 1 then !usage ();
    let name = (List.hd args) in
    let dev = dev_of_name name in
    MK.destroy_development dev; 
    exit 0
  in
  let clean_dev args = 
    let dev = 
      match args with
      | [] -> dev_for_dir (Unix.getcwd ())
      | [name] -> dev_of_name name
      | _ -> !usage (); exit 1
    in
    match MK.clean_development dev with
    | true -> exit 0
    | false -> exit 1
  in
  let build_dev args = 
    if List.length args <> 1 then !usage ();
    let name = (List.hd args) in
    let dev = dev_of_name name in
    match MK.build_development dev with
    | true -> exit 0
    | false -> exit 1
  in
  let publish_dev args = 
    if List.length args <> 1 then !usage ();
    let name = (List.hd args) in
    let dev = dev_of_name name in
    match MK.publish_development dev with
    | true -> exit 0
    | false -> exit 1
  in
  let target args = 
    if List.length args < 1 then !usage ();
    let dev = dev_for_dir (Unix.getcwd ()) in
    List.iter 
      (fun t -> 
        ignore(MK.build_development ~target:t dev)) 
      args
  in
  let params = [
    "init", init_dev;
    "clean", clean_dev;
    "list", list_dev;
    "destroy", destroy_dev;
    "build", build_dev;
    "publish", publish_dev;
  ]
  in
  usage := MatitaInit.die_usage;
  let parse args = 
    match args with
    | [] -> target [ "all" ]
    | s :: tl ->
        let f, args = 
          try 
            (List.assoc s params), tl
          with Not_found -> 
            if s.[0] = '-' then (!usage ();assert false) else target, args
        in
        f args
  in
  parse (Helm_registry.get_list Helm_registry.string "matita.args")
