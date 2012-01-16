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

include "Basic_2/substitution/ldrop.ma".
include "Basic_2/unfold/lifts.ma".

(* GENERIC LOCAL ENVIRONMENT SLICING ****************************************)

inductive ldrops: list2 nat nat → relation lenv ≝
| ldrops_nil : ∀L. ldrops ⟠ L L
| ldrops_cons: ∀L1,L,L2,des,d,e.
               ldrops des L1 L → ⇩[d,e] L ≡ L2 → ldrops ({d, e} :: des) L1 L2
.

interpretation "generic local environment slicing"
   'RDropStar des T1 T2 = (ldrops des T1 T2).

(* Basic properties *********************************************************)

lemma ldrops_skip: ∀L1,L2,des. ⇩*[des] L1 ≡ L2 → ∀V1,V2. ⇧*[des] V2 ≡ V1 →
                   ∀I. ⇩*[des + 1] L1. 𝕓{I} V1 ≡ L2. 𝕓{I} V2.
#L1 #L2 #des #H elim H -L1 -L2 -des
[ #L #V1 #V2 #HV12 #I
  >(lifts_inv_nil … HV12) -HV12 //
| #L1 #L #L2 #des #d #e #_ #HL2 #IHL #V1 #V2 #H #I
  elim (lifts_inv_cons … H) -H /3 width=5/
].
qed.

(* Basic_1: removed theorems 1: drop1_getl_trans
*)
(*
lemma ldrops_inv_skip2: ∀des2,L1,I,K2,V2. ⇩*[des2] L1 ≡ K2. 𝕓{I} V2 →
                        ∀des,i. des ▭ i ≡ des2 →
                        ∃∃K1,V1,des1. des ▭ (i + 1) ≡ des1 &
                                      ⇩*[des1] K1 ≡ K2 &
                                      ⇧*[des1] V2 ≡ V1 &
                                      L1 = K1. 𝕓{I} V1.
*)