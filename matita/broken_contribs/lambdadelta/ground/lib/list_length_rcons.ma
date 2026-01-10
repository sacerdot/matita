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

include "ground/lib/list_rcons.ma".
include "ground/lib/list_length_append.ma".

(* LENGTH FOR LISTS *********************************************************)

(* Constructions with list_rcons ********************************************)

lemma list_length_rcons (A) (l) (a):
      (⁤↑❘l❘) = ❘l⨭❪A❫a❘.
// qed.
