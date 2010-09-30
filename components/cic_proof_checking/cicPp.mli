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

(*****************************************************************************)
(*                                                                           *)
(*                               PROJECT HELM                                *)
(*                                                                           *)
(*                Claudio Sacerdoti Coen <sacerdot@cs.unibo.it>              *)
(*                                 24/01/2000                                *)
(*                                                                           *)
(* This module implements a very simple Coq-like pretty printer that, given  *)
(* an object of cic (internal representation) returns a string describing the*)
(* object in a syntax similar to that of coq                                 *)
(*                                                                           *)
(*****************************************************************************)

(* ppobj obj  returns a string with describing the cic object obj in a syntax*)
(* similar to the one used by Coq                                            *)
val ppobj : Cic.obj -> string

val ppterm : ?metasenv:Cic.metasenv -> Cic.term -> string

val ppcontext : ?metasenv:Cic.metasenv -> ?sep:string -> Cic.context -> string 

(* Required only by the topLevel. It is the generalization of ppterm to *)
(* work with environments.                                              *)
val pp : ?metasenv:Cic.metasenv -> Cic.term -> (Cic.name option) list -> string

val ppname : Cic.name -> string

val ppsort: Cic.sort -> string

val check: string -> Cic.term -> bool
