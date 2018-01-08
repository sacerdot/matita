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

include "basic_2/notation/relations/voidstareq_4.ma".
include "basic_2/syntax/lenv.ma".

(* EQUIVALENCE FOR LOCAL ENVIRONMENTS UP TO EXCLUSION BINDERS ***************)

inductive lveq: bi_relation nat lenv ≝
| lveq_atom   : lveq 0 (⋆) 0 (⋆)
| lveq_pair_sn: ∀I1,I2,K1,K2,V1,n. lveq n K1 n K2 →
                lveq 0 (K1.ⓑ{I1}V1) 0 (K2.ⓘ{I2})
| lveq_pair_dx: ∀I1,I2,K1,K2,V2,n. lveq n K1 n K2 →
                lveq 0 (K1.ⓘ{I1}) 0 (K2.ⓑ{I2}V2)
| lveq_void_sn: ∀K1,K2,n1,n2. lveq n1 K1 n2 K2 →
                lveq (⫯n1) (K1.ⓧ) n2 K2
| lveq_void_dx: ∀K1,K2,n1,n2. lveq n1 K1 n2 K2 →
                lveq n1 K1 (⫯n2) (K2.ⓧ)
.

interpretation "equivalence up to exclusion binders (local environment)"
   'VoidStarEq L1 n1 n2 L2 = (lveq n1 L1 n2 L2).

(* Basic properties *********************************************************)

lemma lveq_refl: ∀L. ∃n. L ≋ⓧ*[n, n] L.
#L elim L -L /2 width=2 by ex_intro, lveq_atom/
#L #I * #n #IH cases I -I /3 width=2 by ex_intro, lveq_pair_dx/
* /4 width=2 by ex_intro, lveq_void_sn, lveq_void_dx/
qed-.

lemma lveq_sym: bi_symmetric … lveq.
#n1 #n2 #L1 #L2 #H elim H -L1 -L2 -n1 -n2
/2 width=2 by lveq_atom, lveq_pair_sn, lveq_pair_dx, lveq_void_sn, lveq_void_dx/
qed-.

(* Basic inversion lemmas ***************************************************)

fact lveq_inv_atom_aux: ∀L1,L2,n1,n2. L1 ≋ⓧ*[n1, n2] L2 →
                        ⋆ = L1 → ⋆ = L2 → ∧∧ 0 = n1 & 0 = n2.
#L1 #L2 #n1 #n2 * -L1 -L2 -n1 -n2
[ /2 width=1 by conj/
|2,3: #I1 #I2 #K1 #K2 #V #n #_ #H1 #H2 destruct
|4,5: #K1 #K2 #n1 #n2 #_ #H1 #H2 destruct
]
qed-.

(* Advanced inversion lemmas ************************************************)

lemma lveq_inv_atom: ∀n1,n2. ⋆ ≋ⓧ*[n1, n2] ⋆ → 0 = n1 ∧ 0 = n2.
/2 width=5 by lveq_inv_atom_aux/ qed-.

fact lveq_inv_void_succ_sn_aux: ∀L1,L2,n1,n2. L1 ≋ⓧ*[n1, n2] L2 →
                                ∀K1,m1. L1 = K1.ⓧ → n1 = ⫯m1 → K1 ≋ ⓧ*[m1, n2] L2.
#L1 #L2 #n1 #n2 #H elim H -L1 -L2 -n1 -n2
[ #K2 #m2 #H destruct
| #I1 #I2 #L1 #L2 #V #n #_ #_ #K1 #m1 #H1 #H2 destruct
| #I1 #I2 #L1 #L2 #V #n #_ #_ #K1 #m1 #H1 #H2 destruct
| #L1 #L2 #n1 #n2 #HL12 #_ #K1 #m1 #H1 #H2 destruct //
| #L1 #L2 #n1 #n2 #_ #IH #K1 #m1 #H1 #H2 destruct
  /3 width=1 by lveq_void_dx/
]
qed-.

lemma lveq_inv_void_succ_sn: ∀L1,L2,n1,n2. L1.ⓧ ≋ⓧ*[⫯n1, n2] L2 → L1 ≋ ⓧ*[n1, n2] L2.
/2 width=5 by lveq_inv_void_succ_sn_aux/ qed-.

lemma lveq_inv_void_succ_dx: ∀L1,L2,n1,n2. L1 ≋ⓧ*[n1, ⫯n2] L2.ⓧ → L1 ≋ ⓧ*[n1, n2] L2.
/4 width=5 by lveq_inv_void_succ_sn_aux, lveq_sym/ qed-.

(* Advanced forward lemmas **************************************************)

fact lveq_fwd_pair_sn_aux: ∀L1,L2,n1,n2. L1 ≋ⓧ*[n1, n2] L2 →
                           ∀I,K1,V. K1.ⓑ{I}V = L1 → 0 = n1.
#L1 #L2 #n1 #n2 #H elim H -L1 -L2 -n1 -n2 //
#K1 #K2 #n1 #n2 #_ #IH #J #L1 #V #H destruct /2 width=4 by/
qed-.

lemma lveq_fwd_pair_sn: ∀I,K1,L2,V,n1,n2. K1.ⓑ{I}V ≋ⓧ*[n1, n2] L2 → 0 = n1.
/2 width=8 by lveq_fwd_pair_sn_aux/ qed-.

lemma lveq_fwd_pair_dx: ∀I,L1,K2,V,n1,n2. L1 ≋ⓧ*[n1, n2] K2.ⓑ{I}V → 0 = n2.
/3 width=6 by lveq_fwd_pair_sn, lveq_sym/ qed-.
