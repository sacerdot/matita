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

exception CannotSubstInMeta;;
exception RelToHiddenHypothesis;;
exception ReferenceToVariable;;
exception ReferenceToConstant;;
exception ReferenceToInductiveDefinition;;

(* lift n t         *)
(* lifts [t] of [n] *)
(* NOTE: the opposite function (delift_rels) is defined in CicMetaSubst *)
(* since it needs to restrict the metavariables in case of failure      *)
val lift : int -> Cic.term -> Cic.term

(* lift from n t *)
(* as lift but lifts only indexes >= from *)
val lift_from: int -> int -> Cic.term -> Cic.term

(* lift map t *)
(* as lift_from but lifts indexes by applying a map to them
   the first argument of the map is the current depth *)
(* FG: this is used in CicDischarge to perform non-linear relocation *)
val lift_map: int -> (int -> int -> int) -> Cic.term -> Cic.term

(* subst t1 t2                                                         *)
(* substitutes [t1] for [Rel 1] in [t2]                                *)
(* if avoid_beta_redexes is true (default: false) no new beta redexes  *)
(* are generated. WARNING: the substitution can diverge when t2 is not *)
(* well typed and avoid_beta_redexes is true.                          *)
val subst : ?avoid_beta_redexes:bool -> Cic.term -> Cic.term -> Cic.term

(* subst_vars exp_named_subst t2     *)
(* applies [exp_named_subst] to [t2] *)
val subst_vars :
 Cic.term Cic.explicit_named_substitution -> Cic.term -> Cic.term

(* subst_meta [t_1 ; ... ; t_n] t                                *)
(* returns the term [t] where [Rel i] is substituted with [t_i] *)
(* [t_i] is lifted as usual when it crosses an abstraction      *)
val subst_meta : (Cic.term option) list -> Cic.term -> Cic.term

