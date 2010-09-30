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

(* $Id$ *)

let position_prefix = "http://www.cs.unibo.it/helm/schemas/schema-helm#"
(* let position_prefix = "" *)

let inconcl_pos = position_prefix ^ "InConclusion"
let mainconcl_pos = position_prefix ^ "MainConclusion"
let mainhyp_pos = position_prefix ^ "MainHypothesis"
let inhyp_pos = position_prefix ^ "InHypothesis"
let inbody_pos = position_prefix ^ "InBody"

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

let constr_of_metadata: metadata -> constr = function
  | `Sort (sort, pos) -> `Sort (sort, [pos])
  | `Rel pos -> `Rel [pos]
  | `Obj (uri, pos) -> `Obj (uri, [pos])

  (** the name of the tables in the DB *)
let sort_tbl_original = "refSort"
let rel_tbl_original = "refRel"
let obj_tbl_original = "refObj"
let name_tbl_original = "objectName"
let count_tbl_original = "count"
let hits_tbl_original = "hits"

  (** the names currently used *)
let sort_tbl_real = ref sort_tbl_original
let rel_tbl_real = ref rel_tbl_original
let obj_tbl_real = ref obj_tbl_original
let name_tbl_real = ref name_tbl_original 
let count_tbl_real = ref count_tbl_original

  (** the exported symbols *)
let sort_tbl () = ! sort_tbl_real ;; 
let rel_tbl () = ! rel_tbl_real ;; 
let obj_tbl () = ! obj_tbl_real ;; 
let name_tbl () = ! name_tbl_real ;; 
let count_tbl () = ! count_tbl_real ;; 

  (** to use the owned tables *)
let ownerize_tables owner =
  sort_tbl_real := ( sort_tbl_original ^ "_" ^ owner) ;
  rel_tbl_real := ( rel_tbl_original ^ "_" ^ owner) ;
  obj_tbl_real := ( obj_tbl_original ^ "_" ^ owner) ;
  name_tbl_real := ( name_tbl_original ^ "_" ^ owner);
  count_tbl_real := ( count_tbl_original ^ "_" ^ owner)
;;

let library_sort_tbl =   sort_tbl_original
let library_rel_tbl = rel_tbl_original
let library_obj_tbl = obj_tbl_original
let library_name_tbl = name_tbl_original
let library_count_tbl = count_tbl_original
let library_hits_tbl = hits_tbl_original

let are_tables_ownerized () =
  sort_tbl () <> library_sort_tbl

