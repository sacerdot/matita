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

module UM = UriManager
module TA = GrafiteAst

let clean_suffixes = [ ".moo"; ".lexicon"; ".metadata"; ".xml.gz" ]

let ask_confirmation _ =
  print_string "
  You are trying to delete the whole standard library.
  Since this may be a dangerous operation, you are asked to type
    
    yes, I'm sure
    
  verbatim and press enter.\n\n> ";
  flush stdout;
  let str = input_line stdin in
  if str = "yes, I'm sure" then 
    begin
      print_string "deletion in progess...\n";
      flush stdout
    end
  else 
    begin
      print_string "deletion cancelled.\n";
      flush stdout;
      exit 1
    end
;;

let clean_all () =
  if Helm_registry.get_bool "matita.system" then
    ask_confirmation ();
  let prefixes = 
    HExtlib.filter_map 
      (fun s -> 
        if String.sub s 0 5 = "file:" then 
          Some (Str.replace_first (Str.regexp "^file://") "" s)
        else
          None)
      (Http_getter_storage.list_writable_prefixes ())
  in
  List.iter 
    (fun xmldir ->
      let clean_pat =
        String.concat " -o "
          (List.map (fun suf -> "-name \\*" ^ suf) clean_suffixes) in
      let clean_cmd =
        sprintf "find %s \\( %s \\) -exec rm \\{\\} \\; 2> /dev/null"
          xmldir clean_pat in
      ignore (Sys.command clean_cmd);
      ignore 
       (Sys.command ("find " ^ xmldir ^ 
        " -type d -exec rmdir -p {} \\; 2> /dev/null"))) 
    prefixes;
  ignore (Sys.command ("rm -rf " ^ Helm_registry.get "matita.basedir"))
;;

let main () =
  let _ = MatitaInit.initialize_all () in
  if not (Helm_registry.get_bool "matita.verbose") then MatitaMisc.shutup ();
  let files =
    match Helm_registry.get_list Helm_registry.string "matita.args" with
    | [ "all" ] -> clean_all (); exit 0
    | [] -> 
        (match Librarian.find_roots_in_dir (Sys.getcwd ()) with
        | [x] -> 
           Sys.chdir (Filename.dirname x); 
           HExtlib.find ~test:(fun x -> Filename.check_suffix x ".ma") "."
        | [] -> 
           prerr_endline "No targets and no root found"; exit 1
        | roots -> 
           let roots = List.map (HExtlib.chop_prefix (Sys.getcwd()^"/")) roots in
           prerr_endline ("Too many roots found:\n\t" ^ String.concat "\n\t" roots);
           prerr_endline ("\nEnter one of these directories and retry");
           exit 1);
    | files -> files
  in
  let uris_to_remove =
   List.fold_left
     (fun uris_to_remove suri ->
       let uri = 
         try
           UM.buri_of_uri (UM.uri_of_string suri)
         with UM.IllFormedUri _ ->
           let _,u,_,_ = Librarian.baseuri_of_script ~include_paths:[] suri in
           if Librarian.is_uri u then u else begin
             HLog.error (sprintf "File %s defines a bad baseuri: %s" suri u);
             exit 1
           end 
       in
        uri::uris_to_remove) [] files
  in
   LibraryClean.clean_baseuris uris_to_remove
