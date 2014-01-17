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

include "basic_2/notation/relations/rdropstar_3.ma".
include "basic_2/notation/relations/rdropstar_4.ma".
include "basic_2/relocation/ldrop.ma".
include "basic_2/substitution/gr2_minus.ma".
include "basic_2/substitution/lifts.ma".

(* ITERATED LOCAL ENVIRONMENT SLICING ***************************************)

inductive ldrops (s:bool): list2 nat nat → relation lenv ≝
| ldrops_nil : ∀L. ldrops s (⟠) L L
| ldrops_cons: ∀L1,L,L2,des,d,e.
               ldrops s des L1 L → ⇩[s, d, e] L ≡ L2 → ldrops s ({d, e} @ des) L1 L2
.

interpretation "iterated slicing (local environment) abstract"
   'RDropStar s des T1 T2 = (ldrops s des T1 T2).
(*
interpretation "iterated slicing (local environment) general"
   'RDropStar des T1 T2 = (ldrops true des T1 T2).
*)

(* Basic inversion lemmas ***************************************************)

fact ldrops_inv_nil_aux: ∀L1,L2,s,des. ⇩*[s, des] L1 ≡ L2 → des = ⟠ → L1 = L2.
#L1 #L2 #s #des * -L1 -L2 -des //
#L1 #L #L2 #d #e #des #_ #_ #H destruct
qed-.

(* Basic_1: was: drop1_gen_pnil *)
lemma ldrops_inv_nil: ∀L1,L2,s. ⇩*[s, ⟠] L1 ≡ L2 → L1 = L2.
/2 width=4 by ldrops_inv_nil_aux/ qed-.

fact ldrops_inv_cons_aux: ∀L1,L2,s,des. ⇩*[s, des] L1 ≡ L2 →
                          ∀d,e,tl. des = {d, e} @ tl →
                          ∃∃L. ⇩*[s, tl] L1 ≡ L & ⇩[s, d, e] L ≡ L2.
#L1 #L2 #s #des * -L1 -L2 -des
[ #L #d #e #tl #H destruct
| #L1 #L #L2 #des #d #e #HT1 #HT2 #hd #he #tl #H destruct
  /2 width=3 by ex2_intro/
]
qed-.

(* Basic_1: was: drop1_gen_pcons *)
lemma ldrops_inv_cons: ∀L1,L2,s,d,e,des. ⇩*[s, {d, e} @ des] L1 ≡ L2 →
                       ∃∃L. ⇩*[s, des] L1 ≡ L & ⇩[s, d, e] L ≡ L2.
/2 width=3 by ldrops_inv_cons_aux/ qed-.

lemma ldrops_inv_skip2: ∀I,s,des,des2,i. des ▭ i ≡ des2 →
                        ∀L1,K2,V2. ⇩*[s, des2] L1 ≡ K2. ⓑ{I} V2 →
                        ∃∃K1,V1,des1. des + 1 ▭ i + 1 ≡ des1 + 1 &
                                      ⇩*[s, des1] K1 ≡ K2 &
                                      ⇧*[des1] V2 ≡ V1 &
                                      L1 = K1. ⓑ{I} V1.
#I #s #des #des2 #i #H elim H -des -des2 -i
[ #i #L1 #K2 #V2 #H
  >(ldrops_inv_nil … H) -L1 /2 width=7 by lifts_nil, minuss_nil, ex4_3_intro, ldrops_nil/
| #des #des2 #d #e #i #Hid #_ #IHdes2 #L1 #K2 #V2 #H
  elim (ldrops_inv_cons … H) -H #L #HL1 #H
  elim (ldrop_inv_skip2 … H) -H /2 width=1 by lt_plus_to_minus_r/ #K #V >minus_plus #HK2 #HV2 #H destruct
  elim (IHdes2 … HL1) -IHdes2 -HL1 #K1 #V1 #des1 #Hdes1 #HK1 #HV1 #X destruct
  @(ex4_3_intro … K1 V1 … ) // [3,4: /2 width=7 by lifts_cons, ldrops_cons/ | skip ]
  normalize >plus_minus /3 width=1 by minuss_lt, lt_minus_to_plus/ (**) (* explicit constructors *)
| #des #des2 #d #e #i #Hid #_ #IHdes2 #L1 #K2 #V2 #H
  elim (IHdes2 … H) -IHdes2 -H #K1 #V1 #des1 #Hdes1 #HK1 #HV1 #X destruct
  /4 width=7 by minuss_ge, ex4_3_intro, le_S_S/
]
qed-.

(* Basic properties *********************************************************)

(* Basic_1: was: drop1_skip_bind *)
lemma ldrops_skip: ∀L1,L2,s,des. ⇩*[s, des] L1 ≡ L2 → ∀V1,V2. ⇧*[des] V2 ≡ V1 →
                   ∀I. ⇩*[s, des + 1] L1.ⓑ{I}V1 ≡ L2.ⓑ{I}V2.
#L1 #L2 #s #des #H elim H -L1 -L2 -des
[ #L #V1 #V2 #HV12 #I
  >(lifts_inv_nil … HV12) -HV12 //
| #L1 #L #L2 #des #d #e #_ #HL2 #IHL #V1 #V2 #H #I
  elim (lifts_inv_cons … H) -H /3 width=5 by ldrop_skip, ldrops_cons/
].
qed.

(* Basic_1: removed theorems 1: drop1_getl_trans *)
