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
