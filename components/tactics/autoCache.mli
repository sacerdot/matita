(* Copyright (C) 2002, HELM Team.
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

type cache
type cache_key = Cic.term
type cache_elem = 
  | Failed_in of int
  | Succeded of Cic.term
  | UnderInspection
  | Notfound
val get_candidates: cache -> Cic.term -> Cic.term list
val cache_add_list: 
    cache -> Cic.context -> (Cic.term*Cic.term) list -> cache
val cache_examine: cache -> cache_key -> cache_elem
val cache_add_failure: cache -> cache_key -> int -> cache 
val cache_add_success: cache -> cache_key -> Cic.term -> cache
val cache_add_underinspection: cache -> cache_key -> int -> cache
val cache_remove_underinspection: cache -> cache_key -> cache
val cache_reset_underinspection: cache -> cache
val cache_empty: cache
val cache_print: Cic.context -> cache -> string
val cache_size: cache -> int
val cache_clean: cache -> cache

