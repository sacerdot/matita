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
include "ground/subsets/subset_ext.ma".
include "ground/subsets/subset_and.ma".

(* INTERSECTION FOR SUBSETS *************************************************)

(* Constructions with extensions for subsets ********************************)

lemma subset_and_ext_f1 (A1) (A0) (f) (u1) (u2):
      (∀p1,p2. p1 ϵ u1 → p2 ϵ u2 → f p1 = f p2 → p1 = p2) →
      (subset_ext_f1 A1 A0 f u1) ∩ (subset_ext_f1 A1 A0 f u2) ⇔
      subset_ext_f1 A1 A0 f (u1 ∩ u2).
#A1 #A0 #f #u1 #u2 #Hf
@conj #r
[ * * #s1 #Hs1 #H1 * #s2 #Hs2 #H2 destruct
  lapply (Hf … (sym_eq … H2)) -Hf -H2 // #H0 destruct
  /3 width=1 by subset_and_in, subset_in_ext_f1_dx/
| * #s * #H1s #H2s #H0 destruct
  /3 width=1 by subset_and_in, subset_in_ext_f1_dx/
]
qed.
