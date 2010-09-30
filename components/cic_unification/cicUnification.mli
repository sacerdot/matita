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

exception UnificationFailure of string Lazy.t;;
exception Uncertain of string Lazy.t;;
exception AssertFailure of string Lazy.t;;

(* fo_unif metasenv context t1 t2                *)
(* unifies [t1] and [t2] in a context [context]. *)
(* Only the metavariables declared in [metasenv] *)
(* can be used in [t1] and [t2].                 *)
(* The returned substitution can be directly     *)
(* withouth first unwinding it.                  *)
val fo_unif :
  Cic.metasenv -> Cic.context -> 
    Cic.term -> Cic.term -> CicUniv.universe_graph -> 
      Cic.substitution * Cic.metasenv * CicUniv.universe_graph

(* fo_unif_subst metasenv subst context t1 t2    *)
(* unifies [t1] and [t2] in a context [context]  *)
(* and with [subst] as the current substitution  *)
(* (i.e. unifies ([subst] [t1]) and              *)
(* ([subst] [t2]) in a context                   *)
(* ([subst] [context]) using the metasenv        *)
(* ([subst] [metasenv])                          *)
(* Only the metavariables declared in [metasenv] *)
(* can be used in [t1] and [t2].                 *)
(* [subst] and the substitution returned are not *)
(* unwinded.                                     *)
(*CSC: fare un tipo unione Unwinded o ToUnwind e fare gestire la
 cosa all'apply_subst!!!*)
val fo_unif_subst :
  Cic.substitution -> Cic.context -> Cic.metasenv -> 
    Cic.term -> Cic.term -> CicUniv.universe_graph ->
      Cic.substitution * Cic.metasenv * CicUniv.universe_graph

