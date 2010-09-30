(* Copyright (C) 2006, HELM Team.
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

type substitution 

val empty_subst : substitution
val apply_subst : substitution -> Cic.term -> Cic.term
val apply_subst_lift : int -> substitution -> Cic.term -> Cic.term
val apply_subst_metasenv : substitution -> Cic.metasenv -> Cic.metasenv
val ppsubst : ?names:(Cic.name option list) -> substitution -> string
val buildsubst : 
  int -> Cic.context -> Cic.term -> Cic.term -> substitution -> 
    substitution
val flatten_subst : substitution -> substitution 
val lookup_subst : Cic.term -> substitution -> Cic.term
val filter : substitution -> Cic.metasenv -> Cic.metasenv
val is_in_subst : int -> substitution -> bool
val merge_subst_if_possible: 
  substitution -> substitution -> 
    substitution option
val concat: substitution -> substitution -> substitution
