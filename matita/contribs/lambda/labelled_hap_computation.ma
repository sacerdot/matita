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

lemma lhap1_lhap: ∀p,M1,M2. M1 ⓗ⇀[p] M2 → M1 ⓗ⇀*[p::◊] M2.
/2 width=1/
qed.

lemma lhap_inv_nil: ∀s,M1,M2. M1 ⓗ⇀*[s] M2 → ◊ = s → M1 = M2.
/2 width=5 by lstar_inv_nil/
qed-.

lemma lhap_inv_cons: ∀s,M1,M2. M1 ⓗ⇀*[s] M2 → ∀q,r. q::r = s →
                     ∃∃M. M1 ⓗ⇀[q] M & M ⓗ⇀*[r] M2.
/2 width=3 by lstar_inv_cons/
qed-.

lemma lhap_inv_lhap1: ∀p,M1,M2. M1 ⓗ⇀*[p::◊] M2 → M1 ⓗ⇀[p] M2.
/2 width=1 by lstar_inv_step/
qed-.

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

theorem lhap_trans: ∀s1,M1,M. M1 ⓗ⇀*[s1] M →
                    ∀s2,M2. M ⓗ⇀*[s2] M2 → M1 ⓗ⇀*[s1@s2] M2.
/2 width=3 by lstar_trans/
qed-.

lemma lhap_appl: ∀s,B,A1,A2. A1 ⓗ⇀*[s] A2 → @B.A1 ⓗ⇀*[dx:::s] @B.A2.
#s #B #A1 #A2 #H @(lstar_ind_l ????????? H) -s -A1 // /3 width=3/
qed.

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

lemma lhap_fwd_le: ∀s,M1,M2. M1 ⓗ⇀*[s] M2 → is_le s.
#s #M1 #M2 #H @(lstar_ind_l ????????? H) -s -M1 /3 width=3/
#a1 #s #M1 #M #HM1 #IHM1
generalize in match HM1; -HM1
cases IHM1 -s -M -M2 //
#a #M0 #M #HM0 #s #M2 #_ #HM10 #H -M2
lapply (lhap1_fwd_le … HM10 … HM0) -M -M0 -M1 /2 width=1/
qed-.
