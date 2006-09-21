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

type development

(* initialize_development [name] [dir]
 * ask matitamake to recorder [dir] as the root for thedevelopment [name] *)
val initialize_development: string -> string -> development option
(* make target [default all] *)
val build_development: ?matita_flags:string -> ?target:string -> development -> bool
(* make target [default all], the refresh cb is called after every output *)
val build_development_in_bg: 
  ?matita_flags:string -> ?target:string -> (unit -> unit) -> development -> bool
(* make clean *)
val clean_development: ?matita_flags:string -> development -> bool
val clean_development_in_bg: ?matita_flags:string -> (unit -> unit) -> development -> bool

val publish_development_in_bg: (unit -> unit) -> development -> bool
val publish_development: development -> bool

(* return the development that handles dir *)
val development_for_dir: string -> development option
(* return the development *)
val development_for_name: string -> development option
(* return the known list of name, development_root *)
val list_known_developments: unit -> (string * string ) list
(* cleans the development, forgetting about it *)
val destroy_development: ?matita_flags:string -> development -> unit
val destroy_development_in_bg: ?matita_flags:string -> (unit -> unit) -> development -> unit
(* initiale internal data structures *)
val initialize : unit -> unit
(* gives back the root *)
val root_for_development : development -> string 
(* gives back the name *)
val name_for_development : development -> string 

(** @return dot file for a given development, if it exists *)
val dot_for_development : development -> string option

