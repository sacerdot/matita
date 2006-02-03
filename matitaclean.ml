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

let main () =
  let _ = MatitaInit.initialize_all () in
  let basedir = Helm_registry.get "matita.basedir" in
  match Helm_registry.get_list Helm_registry.string "matita.args" with
  | [ "all" ] ->
      LibraryDb.clean_owner_environment ();
      let xmldir = basedir ^ "/xml" in
      let clean_pat =
        String.concat " -o "
          (List.map (fun suf -> "-name \\*" ^ suf) clean_suffixes) in
      let clean_cmd =
        sprintf "find %s \\( %s \\) -exec rm \\{\\} \\; 2> /dev/null"
          xmldir clean_pat in
      ignore (Sys.command clean_cmd);
      ignore 
       (Sys.command ("find " ^ xmldir ^ 
        " -type d -exec rmdir -p {} \\; 2> /dev/null"));
      exit 0
  | [] -> MatitaInit.die_usage ()
  | files ->
     let uris_to_remove =
      List.fold_left
        (fun uris_to_remove suri ->
          let uri = 
            try
              UM.buri_of_uri (UM.uri_of_string suri)
            with UM.IllFormedUri _ ->
              let u =
               DependenciesParser.baseuri_of_script ~include_paths:[] suri in
              if String.length u < 5 || String.sub u 0 5 <> "cic:/" then begin
                HLog.error (sprintf "File %s defines a bad baseuri: %s"
                  suri u);
                exit 1
              end else
                u
          in
           uri::uris_to_remove) [] files
     in
      LibraryClean.clean_baseuris ~basedir uris_to_remove
