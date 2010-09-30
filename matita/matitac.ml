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

(* compiler ala pascal/java using make *)
let main_compiler () =
  MatitaInit.initialize_all ();
  (* targets and deps *)
  let targets = Helm_registry.get_list Helm_registry.string "matita.args" in
  let target, root = 
    match targets with
    | [] ->
      (match Librarian.find_roots_in_dir (Sys.getcwd ()) with
      | [x] -> [], Filename.dirname x
      | [] -> 
         prerr_endline "No targets and no root found"; exit 1
      | roots -> 
         let roots = List.map (HExtlib.chop_prefix (Sys.getcwd()^"/")) roots in
         prerr_endline ("Too many roots found:\n\t" ^ String.concat "\n\t" roots);
         prerr_endline ("\nEnter one of these directories and retry");
         exit 1);
    | hds -> 
      let roots_and_targets = 
       List.map (fun (root, buri, file, target) -> root,target)
        (List.map (Librarian.baseuri_of_script ~include_paths:[]) hds) in
      let roots,targets = List.split roots_and_targets in
      let root = List.hd roots in
      if (List.exists (fun root' -> root' <> root) roots) then
       (prerr_endline "Only targets in the same root can be specified.";exit 1);
      targets, root
  in
  (* must be called after init since args are set by cmdline parsing *)
  let system_mode =  Helm_registry.get_bool "matita.system" in
  if system_mode then HLog.message "Compiling in system space";
  (* here we go *)
  if not (Helm_registry.get_bool "matita.verbose") then MatitaMisc.shutup ();
  if MatitacLib.Make.make root target then 
    (HLog.message "Compilation successful"; 0)
  else
    (HLog.message "Compilation failed"; 1)
;;

let main () =
  Sys.catch_break true;
  let bin = Filename.basename Sys.argv.(0) in
  if      Pcre.pmatch ~pat:"^matitadep"    bin then Matitadep.main ()
  else if Pcre.pmatch ~pat:"^matitaclean"  bin then Matitaclean.main ()
  else if Pcre.pmatch ~pat:"^matitawiki"   bin then MatitaWiki.main ()
  else exit (main_compiler ())
;;

let _ = main ()

