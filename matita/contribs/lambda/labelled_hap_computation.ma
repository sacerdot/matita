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

include "labelled_sequential_computation.ma".
include "labelled_hap_reduction.ma".

(* KASHIMA'S "HAP" COMPUTATION (LABELLED MULTISTEP) *************************)

(* Note: this is the "head in application" computation of:
         R. Kashima: "A proof of the Standization Theorem in λ-Calculus". Typescript note, (2000).
*)
definition lhap: pseq → relation term ≝ lstar … lhap1.

interpretation "labelled 'hap' computation"
   'HApStar M p N = (lhap p M N).

notation "hvbox( M break ⓗ⇀* [ term 46 p ] break term 46 N )"
   non associative with precedence 45
   for @{ 'HApStar $M $p $N }.

lemma lhap_step_rc: ∀p,M1,M2. M1 ⓗ⇀[p] M2 → M1 ⓗ⇀*[p::◊] M2.
/2 width=1/
qed.

lemma lhap_inv_nil: ∀s,M1,M2. M1 ⓗ⇀*[s] M2 → ◊ = s → M1 = M2.
/2 width=5 by lstar_inv_nil/
qed-.

lemma lhap_inv_cons: ∀s,M1,M2. M1 ⓗ⇀*[s] M2 → ∀q,r. q::r = s →
                     ∃∃M. M1 ⓗ⇀[q] M & M ⓗ⇀*[r] M2.
/2 width=3 by lstar_inv_cons/
qed-.

lemma lhap_inv_step_rc: ∀p,M1,M2. M1 ⓗ⇀*[p::◊] M2 → M1 ⓗ⇀[p] M2.
/2 width=1 by lstar_inv_step/
qed-.

lemma lhap_compatible_dx: ho_compatible_dx lhap.
/3 width=1/
qed.

lemma lhap_lift: ∀s. liftable (lhap s).
/2 width=1/
qed.

lemma lhap_inv_lift: ∀s. deliftable_sn (lhap s).
/3 width=3 by lstar_deliftable_sn, lhap1_inv_lift/
qed-.

lemma lhap_dsubst: ∀s. dsubstable_dx (lhap s).
/2 width=1/
qed.

theorem lhap_mono: ∀s. singlevalued … (lhap s).
/3 width=7 by lstar_singlevalued, lhap1_mono/
qed-.

theorem lhap_trans: ltransitive … lhap.
/2 width=3 by lstar_ltransitive/
qed-.

lemma head_lsreds_lhap: ∀s,M1,M2. M1 ⇀*[s] M2 → is_head s → M1 ⓗ⇀*[s] M2.
#s #M1 #M2 #H @(lstar_ind_l ????????? H) -s -M1 //
#a #s #M1 #M #HM1 #_ #IHM2 * /3 width=3/
qed.

lemma lhap_inv_head: ∀s,M1,M2. M1 ⓗ⇀*[s] M2 → is_head s.
#s #M1 #M2 #H @(lstar_ind_l ????????? H) -s -M1 //
#p #s #M1 #M #HM1 #_ #IHM2
lapply (lhap1_inv_head … HM1) -HM1 /2 width=1/
qed-.

lemma lhap_inv_lsreds: ∀s,M1,M2. M1 ⓗ⇀*[s] M2 → M1 ⇀*[s] M2.
#s #M1 #M2 #H @(lstar_ind_l ????????? H) -s -M1 //
#p #s #M1 #M #HM1 #_ #IHM2
lapply (lhap1_inv_lsred … HM1) -HM1 /2 width=3/
qed-.
