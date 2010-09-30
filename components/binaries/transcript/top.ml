(* Copyright (C) 2000, HELM Team.
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
 * http://cs.unibo.it/helm/.
 *)

let main =
   let help = "Usage: transcript [ -glmpx | -C <dir> ] [ <package> | <conf_file> ]*" in
   let help_C = " set working directory to <dir>" in
   let help_g = " check for non existing objects" in
   let help_l = " verbose lexing" in
   let help_m = " minimal output generation" in
   let help_p = " verbose parsing" in
   let help_x = " verbose character escaping" in
   let set_cwd dir = Options.cwd := dir; Engine.init () in
   let process_file file =
      if Sys.file_exists file || Sys.file_exists (file ^ Engine.suffix) then
         begin Engine.produce (Engine.make file); Options.sources := [] end
      else
         Options.sources := file :: !Options.sources
   in
   Arg.parse [
      ("-C", Arg.String set_cwd, help_C);
      ("-g", Arg.Set Options.getter, help_g);
      ("-l", Arg.Set Options.verbose_lexer, help_l);
      ("-m", Arg.Clear Options.comments, help_m);
      ("-p", Arg.Set Options.verbose_parser, help_p);
      ("-x", Arg.Set Options.verbose_escape, help_x);
   ] process_file help
