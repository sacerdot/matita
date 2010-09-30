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
 * http://cs.unibo.it/helm/.
 *)

(* mk_fresh_name metasenv context name typ             *)
(* returns an identifier which is fresh in the context *)
(* and that resembles [name] as much as possible.      *)
(* [typ] will be the type of the variable              *)
val mk_fresh_name :
  subst:Cic.substitution ->
  Cic.metasenv -> Cic.context -> Cic.name -> typ:Cic.term -> Cic.name

(* mk_fresh_names metasenv context term                *)
(* returns a term t' convertible with term where all   *)
(* matita_dummies have been replaced by fresh names    *)

val mk_fresh_names :
  subst:Cic.substitution ->
  Cic.metasenv -> Cic.context -> Cic.term -> Cic.term 

(* clean_dummy_dependent_types term                               *)
(* returns a copy of [term] where every dummy dependent product *)
(* have been replaced with a non-dependent product and where    *)
(* dummy let-ins have been removed.                             *)
val clean_dummy_dependent_types : Cic.term -> Cic.term
