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

include "labelled_hap_computation.ma".

(* KASHIMA'S "ST" COMPUTATION ***********************************************)

(* Note: this is the "standard" computation of:
         R. Kashima: "A proof of the Standization Theorem in λ-Calculus". Typescript note, (2000).
*)
inductive st: relation term ≝
| st_vref: ∀s,M,i. M ⓗ⇀*[s] #i → st M (#i)
| st_abst: ∀s,M,A1,A2. M ⓗ⇀*[s] 𝛌.A1 → st A1 A2 → st M (𝛌.A2)
| st_appl: ∀s,M,B1,B2,A1,A2. M ⓗ⇀*[s] @B1.A1 → st B1 B2 → st A1 A2 → st M (@B2.A2)
.

interpretation "'st' computation"
    'Std M N = (st M N).

notation "hvbox( M ⓢ⥤* break term 46 N )"
   non associative with precedence 45
   for @{ 'Std $M $N }.

axiom st_refl: reflexive … st.

axiom st_step_sn: ∀N1,N2. N1 ⓢ⥤* N2 → ∀s,M. M ⓗ⇀*[s] N1 → M ⓢ⥤* N2.

axiom st_lift: liftable st.

axiom st_inv_lift: deliftable_sn st.

axiom st_dsubst: dsubstable st.

lemma st_inv_lsreds_is_le: ∀M,N. M ⓢ⥤* N →
                           ∃∃r. M ⇀*[r] N & is_le r.
#M #N #H elim H -M -N
[ #s #M #i #H
  lapply (lhap_inv_lsreds … H)
  lapply (lhap_inv_head … H) -H #H
  lapply (is_head_is_le … H) -H /2 width=3/
| #s #M #A1 #A2 #H #_ * #r #HA12 #Hr
  lapply (lhap_inv_lsreds … H) #HM
  lapply (lhap_inv_head … H) -H #Hs
  lapply (lsreds_trans … HM (rc:::r) (𝛌.A2) ?) /2 width=1/ -A1 #HM
  @(ex2_intro … HM) -M -A2 /3 width=1/
| #s #M #B1 #B2 #A1 #A2 #H #_ #_ * #rb #HB12 #Hrb * #ra #HA12 #Hra
  lapply (lhap_inv_lsreds … H) #HM
  lapply (lhap_inv_head … H) -H #Hs
  lapply (lsreds_trans … HM (dx:::ra) (@B1.A2) ?) /2 width=1/ -A1 #HM
  lapply (lsreds_trans … HM (sn:::rb) (@B2.A2) ?) /2 width=1/ -B1 #HM
  @(ex2_intro … HM) -M -B2 -A2 >associative_append /3 width=1/
]
qed-.
