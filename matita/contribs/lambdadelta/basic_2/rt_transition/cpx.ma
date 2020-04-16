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

include "ground/xoa/ex_3_4.ma".
include "ground/xoa/ex_4_1.ma".
include "ground/xoa/ex_5_6.ma".
include "ground/xoa/ex_6_6.ma".
include "ground/xoa/ex_6_7.ma".
include "ground/xoa/ex_7_7.ma".
include "ground/xoa/or_4.ma".
include "basic_2/notation/relations/predty_4.ma".
include "basic_2/rt_transition/cpg.ma".

(* EXTENDED CONTEXT-SENSITIVE PARALLEL RT-TRANSITION FOR TERMS **************)

definition sort_eq_f: relation nat ≝ λs1,s2. ⊤.

definition cpx (G) (L): relation2 term term ≝
           λT1,T2. ∃c. ❪G,L❫ ⊢ T1 ⬈[sort_eq_f,rtc_eq_f,c] T2.

interpretation
  "extended context-sensitive parallel rt-transition (term)"
  'PRedTy G L T1 T2 = (cpx G L T1 T2).

(* Basic properties *********************************************************)

(* Basic_2A1: uses: cpx_st *)
lemma cpx_qu (G) (L): ∀s1,s2. ❪G,L❫ ⊢ ⋆s1 ⬈ ⋆s2.
/3 width=2 by cpg_ess, ex_intro/ qed.

lemma cpx_delta (G) (K):
      ∀I,V1,V2,W2. ❪G,K❫ ⊢ V1 ⬈ V2 →
      ⇧[1] V2 ≘ W2 → ❪G,K.ⓑ[I]V1❫ ⊢ #0 ⬈ W2.
#G #K * #V1 #V2 #W2 *
/3 width=4 by cpg_delta, cpg_ell, ex_intro/
qed.

lemma cpx_lref (G) (K):
      ∀I,T,U,i. ❪G,K❫ ⊢ #i ⬈ T →
      ⇧[1] T ≘ U → ❪G,K.ⓘ[I]❫ ⊢ #↑i ⬈ U.
#G #K #I #T #U #i *
/3 width=4 by cpg_lref, ex_intro/
qed.

lemma cpx_bind (G) (L):
      ∀p,I,V1,V2,T1,T2.
      ❪G,L❫ ⊢ V1 ⬈ V2 → ❪G,L.ⓑ[I]V1❫ ⊢ T1 ⬈ T2 →
      ❪G,L❫ ⊢ ⓑ[p,I]V1.T1 ⬈ ⓑ[p,I]V2.T2.
#G #L #p #I #V1 #V2 #T1 #T2 * #cV #HV12 *
/3 width=2 by cpg_bind, ex_intro/
qed.

lemma cpx_flat (G) (L):
      ∀I,V1,V2,T1,T2.
      ❪G,L❫ ⊢ V1 ⬈ V2 → ❪G,L❫ ⊢ T1 ⬈ T2 →
      ❪G,L❫ ⊢ ⓕ[I]V1.T1 ⬈ ⓕ[I]V2.T2.
#G #L * #V1 #V2 #T1 #T2 * #cV #HV12 *
/3 width=5 by cpg_appl, cpg_cast, ex_intro/
qed.

lemma cpx_zeta (G) (L):
      ∀T1,T. ⇧[1] T ≘ T1 → ∀T2. ❪G,L❫ ⊢ T ⬈ T2 →
      ∀V. ❪G,L❫ ⊢ +ⓓV.T1 ⬈ T2.
#G #L #T1 #T #HT1 #T2 *
/3 width=4 by cpg_zeta, ex_intro/
qed.

lemma cpx_eps (G) (L):
      ∀V,T1,T2. ❪G,L❫ ⊢ T1 ⬈ T2 → ❪G,L❫ ⊢ ⓝV.T1 ⬈ T2.
#G #L #V #T1 #T2 *
/3 width=2 by cpg_eps, ex_intro/
qed.

(* Basic_2A1: was: cpx_ct *)
lemma cpx_ee (G) (L):
      ∀V1,V2,T. ❪G,L❫ ⊢ V1 ⬈ V2 → ❪G,L❫ ⊢ ⓝV1.T ⬈ V2.
#G #L #V1 #V2 #T *
/3 width=2 by cpg_ee, ex_intro/
qed.

lemma cpx_beta (G) (L):
      ∀p,V1,V2,W1,W2,T1,T2.
      ❪G,L❫ ⊢ V1 ⬈ V2 → ❪G,L❫ ⊢ W1 ⬈ W2 → ❪G,L.ⓛW1❫ ⊢ T1 ⬈ T2 →
      ❪G,L❫ ⊢ ⓐV1.ⓛ[p]W1.T1 ⬈ ⓓ[p]ⓝW2.V2.T2.
#G #L #p #V1 #V2 #W1 #W2 #T1 #T2 * #cV #HV12 * #cW #HW12 *
/3 width=2 by cpg_beta, ex_intro/
qed.

lemma cpx_theta (G) (L):
      ∀p,V1,V,V2,W1,W2,T1,T2.
      ❪G,L❫ ⊢ V1 ⬈ V → ⇧[1] V ≘ V2 → ❪G,L❫ ⊢ W1 ⬈ W2 → ❪G,L.ⓓW1❫ ⊢ T1 ⬈ T2 →
      ❪G,L❫ ⊢ ⓐV1.ⓓ[p]W1.T1 ⬈ ⓓ[p]W2.ⓐV2.T2.
#G #L #p #V1 #V #V2 #W1 #W2 #T1 #T2 * #cV #HV1 #HV2 * #cW #HW12 *
/3 width=4 by cpg_theta, ex_intro/
qed.

(* Basic_2A1: includes: cpx_atom *)
lemma cpx_refl (G) (L): reflexive … (cpx G L).
/3 width=2 by cpg_refl, ex_intro/ qed.

(* Advanced properties ******************************************************)

lemma cpx_pair_sn (G) (L):
      ∀I,V1,V2. ❪G,L❫ ⊢ V1 ⬈ V2 →
      ∀T. ❪G,L❫ ⊢ ②[I]V1.T ⬈ ②[I]V2.T.
#G #L * /2 width=2 by cpx_flat, cpx_bind/
qed.

lemma cpg_cpx (Rs) (Rk) (c) (G) (L):
      ∀T1,T2. ❪G,L❫ ⊢ T1 ⬈[Rs,Rk,c] T2 → ❪G,L❫ ⊢ T1 ⬈ T2.
#Rs #Rk #c #G #L #T1 #T2 #H elim H -c -G -L -T1 -T2
/2 width=3 by cpx_theta, cpx_beta, cpx_ee, cpx_eps, cpx_zeta, cpx_flat, cpx_bind, cpx_lref, cpx_delta/
qed.

(* Basic inversion lemmas ***************************************************)

lemma cpx_inv_atom1 (G) (L):
      ∀J,T2. ❪G,L❫ ⊢ ⓪[J] ⬈ T2 →
      ∨∨ T2 = ⓪[J]
       | ∃∃s1,s2. T2 = ⋆s2 & J = Sort s1
       | ∃∃I,K,V1,V2. ❪G,K❫ ⊢ V1 ⬈ V2 & ⇧[1] V2 ≘ T2 & L = K.ⓑ[I]V1 & J = LRef 0
       | ∃∃I,K,T,i. ❪G,K❫ ⊢ #i ⬈ T & ⇧[1] T ≘ T2 & L = K.ⓘ[I] & J = LRef (↑i).
#G #L #J #T2 * #c #H elim (cpg_inv_atom1 … H) -H *
/4 width=8 by or4_intro0, or4_intro1, or4_intro2, or4_intro3, ex4_4_intro, ex2_2_intro, ex_intro/
qed-.

lemma cpx_inv_sort1 (G) (L):
      ∀T2,s1. ❪G,L❫ ⊢ ⋆s1 ⬈ T2 →
      ∃s2. T2 = ⋆s2.
#G #L #T2 #s1 * #c #H elim (cpg_inv_sort1 … H) -H *
/2 width=2 by ex_intro/
qed-.

lemma cpx_inv_zero1 (G) (L):
      ∀T2. ❪G,L❫ ⊢ #0 ⬈ T2 →
      ∨∨ T2 = #0
       | ∃∃I,K,V1,V2. ❪G,K❫ ⊢ V1 ⬈ V2 & ⇧[1] V2 ≘ T2 & L = K.ⓑ[I]V1.
#G #L #T2 * #c #H elim (cpg_inv_zero1 … H) -H *
/4 width=7 by ex3_4_intro, ex_intro, or_introl, or_intror/
qed-.

lemma cpx_inv_lref1 (G) (L):
      ∀T2,i. ❪G,L❫ ⊢ #↑i ⬈ T2 →
      ∨∨ T2 = #(↑i)
       | ∃∃I,K,T. ❪G,K❫ ⊢ #i ⬈ T & ⇧[1] T ≘ T2 & L = K.ⓘ[I].
#G #L #T2 #i * #c #H elim (cpg_inv_lref1 … H) -H *
/4 width=6 by ex3_3_intro, ex_intro, or_introl, or_intror/
qed-.

lemma cpx_inv_gref1 (G) (L):
      ∀T2,l. ❪G,L❫ ⊢ §l ⬈ T2 → T2 = §l.
#G #L #T2 #l * #c #H elim (cpg_inv_gref1 … H) -H //
qed-.

lemma cpx_inv_bind1 (G) (L):
      ∀p,I,V1,T1,U2. ❪G,L❫ ⊢ ⓑ[p,I]V1.T1 ⬈ U2 →
      ∨∨ ∃∃V2,T2. ❪G,L❫ ⊢ V1 ⬈ V2 & ❪G,L.ⓑ[I]V1❫ ⊢ T1 ⬈ T2 & U2 = ⓑ[p,I]V2.T2
       | ∃∃T. ⇧[1] T ≘ T1 & ❪G,L❫ ⊢ T ⬈ U2 & p = true & I = Abbr.
#G #L #p #I #V1 #T1 #U2 * #c #H elim (cpg_inv_bind1 … H) -H *
/4 width=5 by ex4_intro, ex3_2_intro, ex_intro, or_introl, or_intror/
qed-.

lemma cpx_inv_abbr1 (G) (L):
      ∀p,V1,T1,U2. ❪G,L❫ ⊢ ⓓ[p]V1.T1 ⬈ U2 →
      ∨∨ ∃∃V2,T2. ❪G,L❫ ⊢ V1 ⬈ V2 & ❪G,L.ⓓV1❫ ⊢ T1 ⬈ T2 & U2 = ⓓ[p]V2.T2
       | ∃∃T. ⇧[1] T ≘ T1 & ❪G,L❫ ⊢ T ⬈ U2 & p = true.
#G #L #p #V1 #T1 #U2 * #c #H elim (cpg_inv_abbr1 … H) -H *
/4 width=5 by ex3_2_intro, ex3_intro, ex_intro, or_introl, or_intror/
qed-.

lemma cpx_inv_abst1 (G) (L):
      ∀p,V1,T1,U2. ❪G,L❫ ⊢ ⓛ[p]V1.T1 ⬈ U2 →
      ∃∃V2,T2. ❪G,L❫ ⊢ V1 ⬈ V2 & ❪G,L.ⓛV1❫ ⊢ T1 ⬈ T2 & U2 = ⓛ[p]V2.T2.
#G #L #p #V1 #T1 #U2 * #c #H elim (cpg_inv_abst1 … H) -H
/3 width=5 by ex3_2_intro, ex_intro/
qed-.

lemma cpx_inv_appl1 (G) (L):
      ∀V1,U1,U2. ❪G,L❫ ⊢ ⓐ V1.U1 ⬈ U2 →
      ∨∨ ∃∃V2,T2. ❪G,L❫ ⊢ V1 ⬈ V2 & ❪G,L❫ ⊢ U1 ⬈ T2 & U2 = ⓐV2.T2
       | ∃∃p,V2,W1,W2,T1,T2. ❪G,L❫ ⊢ V1 ⬈ V2 & ❪G,L❫ ⊢ W1 ⬈ W2 & ❪G,L.ⓛW1❫ ⊢ T1 ⬈ T2 & U1 = ⓛ[p]W1.T1 & U2 = ⓓ[p]ⓝW2.V2.T2
       | ∃∃p,V,V2,W1,W2,T1,T2. ❪G,L❫ ⊢ V1 ⬈ V & ⇧[1] V ≘ V2 & ❪G,L❫ ⊢ W1 ⬈ W2 & ❪G,L.ⓓW1❫ ⊢ T1 ⬈ T2 & U1 = ⓓ[p]W1.T1 & U2 = ⓓ[p]W2.ⓐV2.T2.
#G #L #V1 #U1 #U2 * #c #H elim (cpg_inv_appl1 … H) -H *
/4 width=13 by or3_intro0, or3_intro1, or3_intro2, ex6_7_intro, ex5_6_intro, ex3_2_intro, ex_intro/
qed-.

lemma cpx_inv_cast1 (G) (L):
      ∀V1,U1,U2. ❪G,L❫ ⊢ ⓝV1.U1 ⬈ U2 →
      ∨∨ ∃∃V2,T2. ❪G,L❫ ⊢ V1 ⬈ V2 & ❪G,L❫ ⊢ U1 ⬈ T2 & U2 = ⓝV2.T2
       | ❪G,L❫ ⊢ U1 ⬈ U2
       | ❪G,L❫ ⊢ V1 ⬈ U2.
#G #L #V1 #U1 #U2 * #c #H elim (cpg_inv_cast1 … H) -H *
/4 width=5 by or3_intro0, or3_intro1, or3_intro2, ex3_2_intro, ex_intro/
qed-.

(* Advanced inversion lemmas ************************************************)

lemma cpx_inv_zero1_pair (G) (K):
      ∀I,V1,T2. ❪G,K.ⓑ[I]V1❫ ⊢ #0 ⬈ T2 →
      ∨∨ T2 = #0
       | ∃∃V2. ❪G,K❫ ⊢ V1 ⬈ V2 & ⇧[1] V2 ≘ T2.
#G #K #I #V1 #T2 * #c #H elim (cpg_inv_zero1_pair … H) -H *
/4 width=3 by ex2_intro, ex_intro, or_intror, or_introl/
qed-.

lemma cpx_inv_lref1_bind (G) (K):
      ∀I,T2,i. ❪G,K.ⓘ[I]❫ ⊢ #↑i ⬈ T2 →
      ∨∨ T2 = #(↑i)
       | ∃∃T. ❪G,K❫ ⊢ #i ⬈ T & ⇧[1] T ≘ T2.
#G #K #I #T2 #i * #c #H elim (cpg_inv_lref1_bind … H) -H *
/4 width=3 by ex2_intro, ex_intro, or_introl, or_intror/
qed-.

lemma cpx_inv_flat1 (G) (L):
      ∀I,V1,U1,U2. ❪G,L❫ ⊢ ⓕ[I]V1.U1 ⬈ U2 →
      ∨∨ ∃∃V2,T2. ❪G,L❫ ⊢ V1 ⬈ V2 & ❪G,L❫ ⊢ U1 ⬈ T2 & U2 = ⓕ[I]V2.T2
       | (❪G,L❫ ⊢ U1 ⬈ U2 ∧ I = Cast)
       | (❪G,L❫ ⊢ V1 ⬈ U2 ∧ I = Cast)
       | ∃∃p,V2,W1,W2,T1,T2. ❪G,L❫ ⊢ V1 ⬈ V2 & ❪G,L❫ ⊢ W1 ⬈ W2 & ❪G,L.ⓛW1❫ ⊢ T1 ⬈ T2 & U1 = ⓛ[p]W1.T1 & U2 = ⓓ[p]ⓝW2.V2.T2 & I = Appl
       | ∃∃p,V,V2,W1,W2,T1,T2. ❪G,L❫ ⊢ V1 ⬈ V & ⇧[1] V ≘ V2 & ❪G,L❫ ⊢ W1 ⬈ W2 & ❪G,L.ⓓW1❫ ⊢ T1 ⬈ T2 & U1 = ⓓ[p]W1.T1 & U2 = ⓓ[p]W2.ⓐV2.T2 & I = Appl.
#G #L * #V1 #U1 #U2 #H
[ elim (cpx_inv_appl1 … H) -H *
  /3 width=14 by or5_intro0, or5_intro3, or5_intro4, ex7_7_intro, ex6_6_intro, ex3_2_intro/
| elim (cpx_inv_cast1 … H) -H [ * ]
  /3 width=14 by or5_intro0, or5_intro1, or5_intro2, ex3_2_intro, conj/
]
qed-.

(* Basic forward lemmas *****************************************************)

lemma cpx_fwd_bind1_minus (G) (L):
      ∀I,V1,T1,T. ❪G,L❫ ⊢ -ⓑ[I]V1.T1 ⬈ T → ∀p.
      ∃∃V2,T2. ❪G,L❫ ⊢ ⓑ[p,I]V1.T1 ⬈ ⓑ[p,I]V2.T2 & T = -ⓑ[I]V2.T2.
#G #L #I #V1 #T1 #T * #c #H #p elim (cpg_fwd_bind1_minus … H p) -H
/3 width=4 by ex2_2_intro, ex_intro/
qed-.

(* Basic eliminators ********************************************************)

lemma cpx_ind (Q:relation4 …):
      (∀I,G,L. Q G L (⓪[I]) (⓪[I])) →
      (∀G,L,s1,s2. Q G L (⋆s1) (⋆s2)) →
      (∀I,G,K,V1,V2,W2. ❪G,K❫ ⊢ V1 ⬈ V2 → Q G K V1 V2 →
        ⇧[1] V2 ≘ W2 → Q G (K.ⓑ[I]V1) (#0) W2
      ) → (∀I,G,K,T,U,i. ❪G,K❫ ⊢ #i ⬈ T → Q G K (#i) T →
        ⇧[1] T ≘ U → Q G (K.ⓘ[I]) (#↑i) (U)
      ) → (∀p,I,G,L,V1,V2,T1,T2. ❪G,L❫ ⊢ V1 ⬈ V2 → ❪G,L.ⓑ[I]V1❫ ⊢ T1 ⬈ T2 →
        Q G L V1 V2 → Q G (L.ⓑ[I]V1) T1 T2 → Q G L (ⓑ[p,I]V1.T1) (ⓑ[p,I]V2.T2)
      ) → (∀I,G,L,V1,V2,T1,T2. ❪G,L❫ ⊢ V1 ⬈ V2 → ❪G,L❫ ⊢ T1 ⬈ T2 →
        Q G L V1 V2 → Q G L T1 T2 → Q G L (ⓕ[I]V1.T1) (ⓕ[I]V2.T2)
      ) → (∀G,L,V,T1,T,T2. ⇧[1] T ≘ T1 → ❪G,L❫ ⊢ T ⬈ T2 → Q G L T T2 →
        Q G L (+ⓓV.T1) T2
      ) → (∀G,L,V,T1,T2. ❪G,L❫ ⊢ T1 ⬈ T2 → Q G L T1 T2 →
        Q G L (ⓝV.T1) T2
      ) → (∀G,L,V1,V2,T. ❪G,L❫ ⊢ V1 ⬈ V2 → Q G L V1 V2 →
        Q G L (ⓝV1.T) V2
      ) → (∀p,G,L,V1,V2,W1,W2,T1,T2. ❪G,L❫ ⊢ V1 ⬈ V2 → ❪G,L❫ ⊢ W1 ⬈ W2 → ❪G,L.ⓛW1❫ ⊢ T1 ⬈ T2 →
        Q G L V1 V2 → Q G L W1 W2 → Q G (L.ⓛW1) T1 T2 →
        Q G L (ⓐV1.ⓛ[p]W1.T1) (ⓓ[p]ⓝW2.V2.T2)
      ) → (∀p,G,L,V1,V,V2,W1,W2,T1,T2. ❪G,L❫ ⊢ V1 ⬈ V → ❪G,L❫ ⊢ W1 ⬈ W2 → ❪G,L.ⓓW1❫ ⊢ T1 ⬈ T2 →
        Q G L V1 V → Q G L W1 W2 → Q G (L.ⓓW1) T1 T2 →
        ⇧[1] V ≘ V2 → Q G L (ⓐV1.ⓓ[p]W1.T1) (ⓓ[p]W2.ⓐV2.T2)
      ) →
      ∀G,L,T1,T2. ❪G,L❫ ⊢ T1 ⬈ T2 → Q G L T1 T2.
#Q #IH1 #IH2 #IH3 #IH4 #IH5 #IH6 #IH7 #IH8 #IH9 #IH10 #IH11 #G #L #T1 #T2
* #c #H elim H -c -G -L -T1 -T2 /3 width=4 by ex_intro/
qed-.
