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

exception WrongUriToInductiveDefinition
exception ReferenceToConstant
exception ReferenceToVariable
exception ReferenceToCurrentProof
exception ReferenceToInductiveDefinition
val ndebug : bool ref
val fdebug : int ref
val whd : 
  ?delta:bool -> ?subst:Cic.substitution -> Cic.context -> Cic.term -> Cic.term
val are_convertible : 
  ?subst:Cic.substitution -> ?metasenv:Cic.metasenv -> 
  Cic.context -> Cic.term -> Cic.term -> CicUniv.universe_graph -> 
  bool * CicUniv.universe_graph
val normalize:
  ?delta:bool -> ?subst:Cic.substitution -> Cic.context -> Cic.term -> Cic.term
 
(* performs head beta/(delta)/cast reduction; the default is to not perform
   delta reduction; if provided, ~upto is the maximum number of beta redexes
   reduced *)
val head_beta_reduce: ?delta:bool -> ?upto:int -> Cic.term -> Cic.term
