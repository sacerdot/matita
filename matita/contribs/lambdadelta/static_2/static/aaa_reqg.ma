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

include "static_2/static/reqg_fqup.ma".
include "static_2/static/aaa.ma".

(* ATONIC ARITY ASSIGNMENT ON TERMS *****************************************)

(* Properties with generic equivalence on referred entries ******************)

lemma aaa_teqg_conf_reqg (S) (G):
      reflexive … S →
      ∀L1,T1,A. ❨G,L1❩ ⊢ T1 ⁝ A → ∀T2. T1 ≛[S] T2 →
      ∀L2. L1 ≛[S,T1] L2 → ❨G,L2❩ ⊢ T2 ⁝ A.
#S #G #HS #L1 #T1 #A #H elim H -G -L1 -T1 -A
[ #G #L1 #s1 #X #H1 elim (teqg_inv_sort1 … H1) -H1 //
| #I #G #L1 #V1 #B #_ #IH #X #H1 >(teqg_inv_lref1 … H1) -H1
  #Y #H2 elim (reqg_inv_zero_pair_sn … H2) -H2
  #L2 #V2 #HL12 #HV12 #H destruct /3 width=1 by aaa_zero/
| #I #G #L1 #A #i #_ #IH #X #H1 >(teqg_inv_lref1 … H1) -H1
  #Y #H2 elim (reqg_inv_lref_bind_sn … H2) -H2
  #J #L2 #HL12 #H destruct /3 width=1 by aaa_lref/
| #p #G #L1 #V1 #T1 #B #A #_ #_ #IHV #IHT #X #H1 elim (teqg_inv_pair1 … H1) -H1
  #V2 #T2 #HV12 #HT12 #H #L2 #H2 elim (reqg_inv_bind_refl … H2) -H2 destruct
  /5 width=2 by aaa_abbr, reqg_bind_repl_dx, ext2_pair/
| #p #G #L1 #V1 #T1 #B #A #_ #_ #IHV #IHT #X #H1 elim (teqg_inv_pair1 … H1) -H1
  #V2 #T2 #HV12 #HT12 #H #L2 #H2 elim (reqg_inv_bind_refl … H2) -H2 destruct
  /5 width=2 by aaa_abst, reqg_bind_repl_dx, ext2_pair/
| #G #L1 #V1 #T1 #B #A #_ #_ #IHV #IHT #X #H1 elim (teqg_inv_pair1 … H1) -H1
  #V2 #T2 #HV12 #HT12 #H #L2 #H2 elim (reqg_inv_flat … H2) -H2 destruct
  /3 width=3 by aaa_appl/
| #G #L1 #V1 #T1 #A #_ #_ #IHV #IHT #X #H1 elim (teqg_inv_pair1 … H1) -H1
  #V2 #T2 #HV12 #HT12 #H #L2 #H2 elim (reqg_inv_flat … H2) -H2 destruct
  /3 width=1 by aaa_cast/
]
qed-.

lemma aaa_teqg_conf (S) (G) (L) (A):
      reflexive … S →
      ∀T1. ❨G,L❩ ⊢ T1 ⁝ A → ∀T2. T1 ≛[S] T2 → ❨G,L❩ ⊢ T2 ⁝ A.
/3 width=7 by aaa_teqg_conf_reqg, reqg_refl/ qed-.

lemma aaa_reqg_conf (S) (G) (T) (A):
      reflexive … S →
      ∀L1. ❨G,L1❩ ⊢ T ⁝ A → ∀L2. L1 ≛[S,T] L2 → ❨G,L2❩ ⊢ T ⁝ A.
/3 width=7 by aaa_teqg_conf_reqg, teqg_refl/ qed-.
