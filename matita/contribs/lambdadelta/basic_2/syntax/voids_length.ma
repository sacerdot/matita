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

include "basic_2/syntax/lenv_length.ma".
include "basic_2/syntax/voids.ma".

(* EQUIVALENCE FOR LOCAL ENVIRONMENTS UP TO EXCLUSION BINDERS ***************)

(* Forward lemmas with length for local environments ************************)

lemma voids_fwd_length: ∀L1,L2,n1,n2. ⓧ*[n1]L1 ≋ ⓧ*[n2]L2 →
                        |L1| + n2 = |L2| + n1.
#L1 #L2 #n1 #n2 #H elim H -L1 -L2 -n1 -n2 normalize //
#I1 #I2 #K1 #K2 #V #n #_ #IH 

(* Main forward properties with length for local environments ***************)

theorem voids_inj_length: ∀n1,n2,L1,L2. ⓧ*[n1]L1 = ⓧ*[n2]L2 →
                          |L1| = |L2| → n1 = n2 ∧ L1 = L2.
#n1 elim n1 -n1
[ * /2 width=1 by conj/ #n2 #L1 #L2 | #n1 #IH * [ | #n2 ] #L1 #L2 ]
[ <voids_zero #H destruct
  <length_void <commutative_plus #H
  elim (plus_xSy_x_false … H)
| <voids_zero #H destruct
  <length_void <commutative_plus #H
  elim (plus_xSy_x_false … (sym_eq … H))
| <voids_succ <voids_succ #H #HL12
  elim (destruct_lbind_lbind_aux … H) -H (**) (* destruct lemma needed *)
  #H #_ elim (IH … H HL12) -IH -H -HL12 /2 width=1 by conj/
]
qed-.
