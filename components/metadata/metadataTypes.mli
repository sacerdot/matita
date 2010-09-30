(* Copyright (C) 2004, HELM Team.
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

val position_prefix : string

val inconcl_pos : string 
val mainconcl_pos : string
val mainhyp_pos : string
val inhyp_pos : string
val inbody_pos : string

type relation = 
  | Eq of int
  | Le of int
  | Lt of int
  | Ge of int
  | Gt of int

type main_position =
  [ `MainConclusion of relation option (* Pi depth *)
  | `MainHypothesis of relation option (* Pi depth *)
  ]

type position =
  [ main_position
  | `InConclusion
  | `InHypothesis
  | `InBody
  ]

type pi_depth = int

type metadata =
  [ `Sort of Cic.sort * main_position
  | `Rel of main_position
  | `Obj of UriManager.uri * position
  ]

type constr =
  [ `Sort of Cic.sort * main_position list
  | `Rel of main_position list
  | `Obj of UriManager.uri * position list
  ]

val constr_of_metadata: metadata -> constr

  (** invoke this function to set the current owner. Afterwards the functions
  * below will return the name of the table of the set owner *)
val ownerize_tables : string -> unit
val are_tables_ownerized : unit -> bool

val sort_tbl: unit -> string  
val rel_tbl: unit -> string
val obj_tbl: unit -> string
val name_tbl: unit -> string
val count_tbl: unit -> string

val library_sort_tbl:  string  
val library_rel_tbl:  string
val library_obj_tbl:  string
val library_name_tbl:  string
val library_count_tbl: string
val library_hits_tbl: string

