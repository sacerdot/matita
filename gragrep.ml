(* Copyright (C) 2006, HELM Team.
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

open Printf

let is_notation = function GrafiteParser.LNone _ -> true | _ -> false

let grep () =
  let recursive = ref false in
  let spec = [
    "-r", Arg.Set recursive, "enable directory recursion";
  ] in
  MatitaInit.add_cmdline_spec spec;
  MatitaInit.initialize_all ();
  let include_paths =
    Helm_registry.get_list Helm_registry.string "matita.includes" in
  let status =
    CicNotation2.load_notation ~include_paths
      BuildTimeConf.core_notation_script in
  let path =
    match Helm_registry.get_list Helm_registry.string "matita.args" with
    | [ path ] -> path
    | _ -> MatitaInit.die_usage () in
  let grep_fun =
    if !recursive then
      (fun dirname ->
        ignore (GrafiteWalker.rgrep_statement ~status
          ~callback:(fun (fname, s) -> printf "%s: %s\n%!" fname s)
          ~dirname is_notation))
    else
      (fun fname ->
        ignore (GrafiteWalker.grep_statement ~status
          ~callback:(fun s -> printf "%s\n%!" s)
          ~fname is_notation)) in
  grep_fun path

let handle_localized_exns f arg =
  try
    f arg
  with HExtlib.Localized (loc, exn) ->
    let loc_begin, loc_end = HExtlib.loc_of_floc loc in
    eprintf "Error at %d-%d: %s\n%!" loc_begin loc_end (Printexc.to_string exn)

let main () = handle_localized_exns grep ()

