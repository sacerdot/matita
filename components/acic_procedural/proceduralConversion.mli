(* Copyright (C) 2003-2005, HELM Team.
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

val meta: Cic.id -> Cic.annterm

val hole: Cic.id -> Cic.annterm

val lift: int -> int -> Cic.annterm -> Cic.annterm

val fake_annotate: Cic.id -> Cic.context -> Cic.term -> Cic.annterm

val mk_pattern: int -> Cic.annterm -> Cic.annterm -> Cic.annterm

val beta: Cic.annterm -> Cic.annterm -> Cic.annterm

val get_clears: 
   Cic.context -> Cic.term -> (Cic.term * Cic.term) option -> 
   Cic.context * string list

val clear: Cic.context -> string -> Cic.context
(*
val elim_inferred_type:
   Cic.context -> Cic.term -> Cic.term -> Cic.term -> Cic.term -> Cic.term
*)
val does_not_occur: Cic.annterm -> bool
