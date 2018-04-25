(**************************************************************************)
(*       ___                                                              *)
(*      ||M||                                                             *)
(*      ||A||       A project by Andrea Asperti                           *)
(*      ||T||                                                             *)
(*      ||I||       Developers:                                           *)
(*      ||T||         The HELM team.                                      *)
(*      ||A||         http://helm.cs.unibo.it                             *)
(*      \   /                                                             *)
(*       \ /        This file is distributed under the terms of the       *)
(*        v         GNU General Public License Version 2                  *)
(*                                                                        *)
(**************************************************************************)

include "ground_2/lib/relations.ma".

(* FUNCTIONS ****************************************************************)

definition left_identity (A:Type[0]) (f): predicate A ≝ λi. ∀a:A. a = f i a.

definition right_identity (A:Type[0]) (f): predicate A ≝ λi. ∀a:A. a = f a i.
