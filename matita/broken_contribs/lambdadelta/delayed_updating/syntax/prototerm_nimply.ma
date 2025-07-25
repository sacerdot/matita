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

include "ground/subsets/subset_nimply.ma".
include "delayed_updating/syntax/prototerm_eq.ma".

(* PROTOTERM ****************************************************************)

(* Constructions with subset_nimply *****************************************)

lemma term_grafted_nimp (t1) (t2) (p):
      (⋔[p]t1)⧵(⋔[p]t2) ⇔ ⋔[p](t1⧵t2).
#t1 #t2 #p @conj #q //
qed.
