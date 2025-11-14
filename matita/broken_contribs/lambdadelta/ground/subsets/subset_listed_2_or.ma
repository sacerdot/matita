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

include "ground/subsets/subset_eq.ma".
include "ground/subsets/subset_or.ma".
include "ground/subsets/subset_listed_1.ma".
include "ground/subsets/subset_listed_2.ma".

(* SUBSET WITH LISTED ELEMENTS **********************************************)

(* Constructions with subset_or and subset_eq *******************************)

lemma subset_pair_or (A) (a1) (a2):
      ❴a1❵ ∪ ❴a2❵ ⇔{A} ❴a1,a2❵.
#A #a1 #a2 @conj #x
[ * #Hx >(subset_in_inv_single ??? Hx) -x //
| #Hx elim (subset_in_inv_pair ???? Hx) -Hx #H0 destruct
  /2 width=1 by subset_or_in_dx, subset_or_in_sx/
]
qed.
