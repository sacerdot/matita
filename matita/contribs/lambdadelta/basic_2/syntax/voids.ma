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

include "basic_2/notation/relations/rvoidstar_4.ma".
include "basic_2/syntax/lenv.ma".

(* EQUIVALENCE FOR LOCAL ENVIRONMENTS UP TO EXCLUSION BINDERS ***************)

inductive voids: bi_relation nat lenv ≝
| voids_atom   : voids 0 (⋆) 0 (⋆)
| voids_pair_sn: ∀I1,I2,K1,K2,V1,n. voids n K1 n K2 →
                 voids 0 (K1.ⓑ{I1}V1) 0 (K2.ⓘ{I2})
| voids_pair_dx: ∀I1,I2,K1,K2,V2,n. voids n K1 n K2 →
                 voids 0 (K1.ⓘ{I1}) 0 (K2.ⓑ{I2}V2)
| voids_void_sn: ∀K1,K2,n1,n2. voids n1 K1 n2 K2 →
                 voids (⫯n1) (K1.ⓧ) n2 K2
| voids_void_dx: ∀K1,K2,n1,n2. voids n1 K1 n2 K2 →
                 voids n1 K1 (⫯n2) (K2.ⓧ)
.

interpretation "equivalence up to exclusion binders (local environment)"
   'RVoidStar n1 L1 n2 L2 = (voids n1 L1 n2 L2).

(* Basic properties *********************************************************)

lemma voids_refl: ∀L. ∃n. ⓧ*[n]L ≋ ⓧ*[n]L.
#L elim L -L /2 width=2 by ex_intro, voids_atom/
#L #I * #n #IH cases I -I /3 width=2 by ex_intro, voids_pair_dx/
* /4 width=2 by ex_intro, voids_void_sn, voids_void_dx/
qed-.

lemma voids_sym: bi_symmetric … voids.
#n1 #n2 #L1 #L2 #H elim H -L1 -L2 -n1 -n2
/2 width=2 by voids_atom, voids_pair_sn, voids_pair_dx, voids_void_sn, voids_void_dx/
qed-.

(* Advanced Inversion lemmas ************************************************)

fact voids_inv_void_dx_aux: ∀L1,L2,n1,n2. ⓧ*[n1]L1 ≋ ⓧ*[n2]L2 →
                            ∀K2,m2. n2 = ⫯m2 → L2 = K2.ⓧ → ⓧ*[n1]L1 ≋ ⓧ*[m2]K2.
#L1 #L2 #n1 #n2 #H elim H -L1 -L2 -n1 -n2
[ #K2 #m2 #H destruct
| #I1 #I2 #L1 #L2 #V #n #_ #_ #K2 #m2 #H destruct
| #I1 #I2 #L1 #L2 #V #n #_ #_ #K2 #m2 #H destruct
| #L1 #L2 #n1 #n2 #_ #IH #K2 #m2 #H1 #H2 destruct
  /3 width=1 by voids_void_sn/
| #L1 #L2 #n1 #n2 #HL12 #_ #K2 #m2 #H1 #H2 destruct //
]
qed-.

lemma voids_inv_void_dx: ∀L1,L2,n1,n2. ⓧ*[n1]L1 ≋ ⓧ*[⫯n2]L2.ⓧ → ⓧ*[n1]L1 ≋ ⓧ*[n2]L2.
/2 width=5 by voids_inv_void_dx_aux/ qed-.
