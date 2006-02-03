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
  let init_dev_doc = "
\tParameters: name (the name of the development, required)
\tDescription: tells matitamake that a new development radicated 
\t\tin the current working directory should be handled."
  in
  let init_dev args =
    if List.length args <> 1 then !usage ();
    match MK.initialize_development (List.hd args) (Unix.getcwd ()) with
    | None -> exit 2
    | Some _ -> exit 0
  in
  let list_dev_doc = "
\tParameters: 
\tDescription: lists the known developments and their roots."
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
  let destroy_dev_doc = "
\tParameters: name (the name of the development to destroy, required)
\tDescription: deletes a development (only from matitamake metadat, no
\t\t.ma files will be deleted)."
  in
  let destroy_dev args = 
    if List.length args <> 1 then !usage ();
    let name = (List.hd args) in
    let dev = dev_of_name name in
    MK.destroy_development dev; 
    exit 0
  in
  let clean_dev_doc = "
\tParameters: name (the name of the development to destroy, optional)
\t\tIf omitted the development that holds the current working 
\t\tdirectory is used (if any).
\tDescription: clean the develpoment."
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
  let build_dev_doc = "
\tParameters: name (the name of the development to build, required)
\tDescription: completely builds the develpoment."
  in
  let build_dev args = 
    if List.length args <> 1 then !usage ();
    let name = (List.hd args) in
    let dev = dev_of_name name in
    match MK.build_development dev with
    | true -> exit 0
    | false -> exit 1
  in
  let nodb_doc = "
\tParameters:
\tDescription: avoid using external database connection."
  in
  let nodb _ = Helm_registry.set_bool "db.nodb" true in
  let target args = 
    if List.length args < 1 then !usage ();
    let dev = dev_for_dir (Unix.getcwd ()) in
    List.iter 
      (fun t -> 
        ignore(MK.build_development ~target:t dev)) 
      args
  in
  let params = [
    "-init", init_dev, init_dev_doc;
    "-clean", clean_dev, clean_dev_doc;
    "-list", list_dev, list_dev_doc;
    "-destroy", destroy_dev, destroy_dev_doc;
    "-build", build_dev, build_dev_doc;
    "-nodb", nodb, nodb_doc;
    "-h", (fun _ -> !usage()), "print this help screen";
    "-help", (fun _ -> !usage()), "print this help screen";
  ]
  in
  usage := (fun () -> 
    let p = prerr_endline in 
    p "\nusage:";
    p "\tmatitamake(.opt) [command [options]]\n";
    p "\tmatitamake(.opt) [target]\n";
    p "commands:";
    List.iter (fun (n,_,d) -> p (Printf.sprintf "    %-10s%s" n d)) params;
    p "\nIf target is omitted a 'all' will be used as the default.";
    p "With -build you can build a development wherever it is.";
    p "If you specify a target it implicitly refers to the development that";
    p "holds the current working directory (if any).\n"; 
    exit 1);
  let rec parse args = 
    match args with
    | [] -> target ["all"]
    | s::tl ->
        try
          let _,f,_ = List.find (fun (n,_,_) -> n = s) params in
          f tl;
          parse tl
        with Not_found -> if s.[0] = '-' then !usage () else target args
  in
  parse (List.tl (Array.to_list Sys.argv))

