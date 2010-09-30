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

type notation_id

val compare_notation_id : notation_id -> notation_id -> int

val process_notation: LexiconAst.command -> notation_id list

val remove_notation: notation_id -> unit

(** {2 Notation enabling/disabling}
 * Right now, only disabling of notation during pretty printing is supported.
 * If it is useful to disable it also for the input phase is still to be
 * understood ... *)

val get_all_notations: unit -> (notation_id * string) list  (* id, dsc *)
val get_active_notations: unit -> notation_id list
val set_active_notations: notation_id list -> unit

val push: unit -> unit
val pop: unit -> unit
