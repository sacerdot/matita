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

exception Impossible of int
exception ReferenceToConstant
exception ReferenceToVariable
exception ReferenceToCurrentProof
exception ReferenceToInductiveDefinition
exception WrongUriToInductiveDefinition
exception RelToHiddenHypothesis
exception WrongShape
exception AlreadySimplified
exception WhatAndWithWhatDoNotHaveTheSameLength;;

(* Replaces "textually" in "where" every term in "what" with the corresponding
   term in "with_what". The terms in "what" ARE NOT lifted when binders are
   crossed. The terms in "with_what" ARE NOT lifted when binders are crossed.
   Every free variable in "where" IS NOT lifted by nnn. *)
val replace :
  equality:('a -> Cic.term -> bool) ->
  what:'a list -> with_what:Cic.term list -> where:Cic.term -> Cic.term

(* Replaces in "where" every term in "what" with the corresponding
   term in "with_what". The terms in "what" ARE lifted when binders are
   crossed. The terms in "with_what" ARE lifted when binders are crossed.
   Every free variable in "where" IS NOT lifted by nnn.
   Thus "replace_lifting_csc 1 ~with_what:[Rel 1; ... ; Rel 1]" is the
   inverse of subst up to the fact that free variables in "where" are NOT
   lifted. *)
val replace_lifting :
  equality:(Cic.context -> Cic.term -> Cic.term -> bool) ->
  context:Cic.context ->
  what:Cic.term list -> with_what:Cic.term list -> where:Cic.term -> Cic.term

(* Replaces in "where" every term in "what" with the corresponding
   term in "with_what". The terms in "what" ARE NOT lifted when binders are
   crossed. The terms in "with_what" ARE lifted when binders are crossed.
   Every free variable in "where" IS lifted by nnn.
   Thus "replace_lifting_csc 1 ~with_what:[Rel 1; ... ; Rel 1]" is the
   inverse of subst up to the fact that "what" terms are NOT lifted. *)
val replace_lifting_csc :
  int -> equality:(Cic.term -> Cic.term -> bool) ->
  what:Cic.term list -> with_what:Cic.term list -> where:Cic.term -> Cic.term

(* This is like "replace_lifting_csc 1 ~with_what:[Rel 1; ... ; Rel 1]"
   up to the fact that the index to start from can be specified *)
val replace_with_rel_1_from :
  equality:(Cic.term -> Cic.term -> bool) ->
  what:Cic.term list -> int -> Cic.term -> Cic.term
val simpl : Cic.context -> Cic.term -> Cic.term
val unfold : ?what:Cic.term -> Cic.context -> Cic.term -> Cic.term
