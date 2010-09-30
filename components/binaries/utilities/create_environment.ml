(* Copyright (C) 2004-2005, HELM Team.
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

let trust = true

let outfname =
  match Sys.argv.(1) with
    | "-help" | "--help" | "-h" | "--h" ->
          print_endline
            ("Usage: create_environment <dumpfile> <uri_index>\n" ^
             "  <dumpfile>   is the file where environment will be dumped\n" ^
             "  <uri_index>  is the file containing the URIs, one per line,\n" ^
             "               that will be typechecked. Could be \"-\" for\n" ^
             "               standard input");
          flush stdout;
          exit 0
    | f -> f
let _ =
  CicEnvironment.set_trust (fun _ -> trust);
  Helm_registry.set "getter.mode" "remote";
  Helm_registry.set "getter.url" "http://mowgli.cs.unibo.it:58081/";
  Sys.catch_break true;
  if Sys.file_exists outfname then begin
    let ic = open_in outfname in
    CicEnvironment.restore_from_channel ic;
    close_in ic
  end
let urifname =
  try
    Sys.argv.(2)
  with Invalid_argument _ -> "-"
let ic =
  match urifname with
    | "-" -> stdin
    | fname -> open_in fname
let _ =
  try
    while true do
(*       try *)
        let uri = input_line ic in
        print_endline uri;
        flush stdout;
        let uri = UriManager.uri_of_string uri in
        ignore (CicTypeChecker.typecheck uri)
(*       with Sys.Break -> () *)
    done
  with End_of_file | Sys.Break ->
    let oc = open_out outfname in
    CicEnvironment.dump_to_channel oc;
    close_out oc

