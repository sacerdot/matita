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

let arg_spec =
  let std_arg_spec = [] in
  let debug_arg_spec = [] in
  std_arg_spec @ debug_arg_spec

let usage =
  sprintf "MatitaC v%s\nUsage: dump_moo [option ...] file.moo\nOptions:"
    BuildTimeConf.version

let _ =
  let moos = ref [] in
  let add_moo fname = moos := fname :: !moos in
  Arg.parse arg_spec add_moo usage;
  if !moos = [] then begin print_endline usage; exit 1 end;
  List.iter
    (fun fname ->
      if not (Sys.file_exists fname) then
        HLog.error (sprintf "Can't find moo '%s', skipping it." fname)
      else begin
        printf "%s:\n" fname; flush stdout;
        let commands = GrafiteMarshal.load_moo ~fname in
        List.iter
          (fun cmd ->
            printf "  %s\n%!"
              (GrafiteAstPp.pp_command ~obj_pp:(fun _ -> assert false) cmd))
          commands;
      end)
    (List.rev !moos)

