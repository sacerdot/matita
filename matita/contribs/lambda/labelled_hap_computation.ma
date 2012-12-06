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
definition lhap: rpseq → relation term ≝ lstar … lhap1.

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
(*
theorem lhap_mono: ∀s. singlevalued … (lhap s).
/3 width=7 by lstar_singlevalued, lhap1_mono/
qed-.
*)
theorem lhap_trans: ∀s1,M1,M. M1 ⓗ⇀*[s1] M →
                    ∀s2,M2. M ⓗ⇀*[s2] M2 → M1 ⓗ⇀*[s1@s2] M2.
/2 width=3 by lstar_trans/
qed-.
(*
lemma hap_appl: appl_compatible_dx hap.
/3 width=1/
qed.
*)
lemma lhap_spine_fwd: ∀s,M1,M2. M1 ⓗ⇀*[s] M2 → is_spine s.
#s #M1 #M2 #H elim H -s -M1 -M2 //
#p #M1 #M #HM1 #s #M2 #_ #IHM2
lapply (lhap1_spine_fwd … HM1) -HM1 /2 width=1/ 
qed-.

lemma lhap_lsreds_fwd: ∀s,M1,M2. M1 ⓗ⇀*[s] M2 → M1 ⇀*[s] M2.
#s #M1 #M2 #H elim H -s -M1 -M2 //
#p #M1 #M #HM1 #s #M2 #_ #IHM2
lapply (lhap1_lsred_fwd … HM1) -HM1 /2 width=3/ 
qed-.

lemma lhap_le_fwd: ∀s,M1,M2. M1 ⓗ⇀*[s] M2 → is_le s.
(*
#M1 #M2 #H @(star_ind_l ??????? H) -M1 /3 width=3/
#M1 #M #HM1 #H * #s * #H1s #H2s
generalize in match HM1; -HM1 generalize in match M1; -M1
@(star_ind_l ??????? H) -M
[ #M1 #HM12 elim (hap1_lsred … HM12) -HM12 /4 width=3/
| #M0 #M1 #HM01 #HM12 #_ #M #HM0 #HM02
*)
