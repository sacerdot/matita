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

val set_default : string -> UriManager.uri list -> unit

val reset_defaults : unit -> unit 
val push: unit -> unit
val pop: unit -> unit

val eq_URI : unit -> UriManager.uri option

val is_eq_URI : UriManager.uri -> bool
val is_eq_refl_URI : UriManager.uri -> bool
val is_eq_ind_URI : UriManager.uri -> bool
val is_eq_ind_r_URI : UriManager.uri -> bool
val is_eq_rec_URI : UriManager.uri -> bool
val is_eq_rec_r_URI : UriManager.uri -> bool
val is_eq_rect_URI : UriManager.uri -> bool
val is_eq_rect_r_URI : UriManager.uri -> bool
val is_trans_eq_URI : UriManager.uri -> bool
val is_sym_eq_URI : UriManager.uri -> bool
val is_eq_f_URI : UriManager.uri -> bool
val is_eq_f_sym_URI : UriManager.uri -> bool
val in_eq_URIs : UriManager.uri -> bool

val eq_URI_of_eq_f_URI : UriManager.uri -> UriManager.uri

exception NotRecognized of string;;

val eq_refl_URI : eq:UriManager.uri -> UriManager.uri
val eq_ind_URI : eq:UriManager.uri -> UriManager.uri
val eq_ind_r_URI : eq:UriManager.uri -> UriManager.uri
val eq_rec_URI : eq:UriManager.uri -> UriManager.uri
val eq_rec_r_URI : eq:UriManager.uri -> UriManager.uri
val eq_rect_URI : eq:UriManager.uri -> UriManager.uri
val eq_rect_r_URI : eq:UriManager.uri -> UriManager.uri
val trans_eq_URI : eq:UriManager.uri -> UriManager.uri
val sym_eq_URI : eq:UriManager.uri -> UriManager.uri
val eq_f_URI : eq:UriManager.uri -> UriManager.uri
val eq_f_sym_URI : eq:UriManager.uri -> UriManager.uri


val false_URI : unit -> UriManager.uri option
val true_URI : unit -> UriManager.uri option
val absurd_URI : unit -> UriManager.uri option

val nat_URI : unit -> UriManager.uri option
val is_nat_URI : UriManager.uri -> bool
