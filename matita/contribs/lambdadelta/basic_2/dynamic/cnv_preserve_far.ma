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

include "basic_2/notation/relations/predstar_7.ma".
include "basic_2/rt_computation/fpbg.ma".
include "basic_2/rt_computation/cpms_fpbs.ma".
include "basic_2/dynamic/cnv.ma".

(* CONTEXT-SENSITIVE NATIVE VALIDITY FOR TERMS ******************************)

(* Inductive premises for the preservation results **************************)

definition cpsms (n) (h) (o): relation4 genv lenv term term ≝ λG,L,T1,T2.
                 ∃∃n1,n2,T. T1 ≛[h,o] T → ⊥ & ⦃G, L⦄ ⊢ T1 ➡[n1,h] T & ⦃G, L⦄ ⊢ T ➡*[n2,h] T2 & n1+n2 = n.

interpretation
   "context-sensitive parallel stratified t-bound  rt-computarion (term)"
   'PRedStar n h o G L T1 T2 = (cpsms n h o G L T1 T2).

definition IH_cnv_cpm_trans_lpr (a) (h): relation3 genv lenv term ≝
                                λG,L1,T1. ⦃G, L1⦄ ⊢ T1 ![a,h] →
                                ∀n,T2. ⦃G, L1⦄ ⊢ T1 ➡[n,h] T2 →
                                ∀L2. ⦃G, L1⦄ ⊢ ➡[h] L2 → ⦃G, L2⦄ ⊢ T2 ![a,h].

definition IH_cnv_cpms_trans_lpr (a) (h): relation3 genv lenv term ≝
                                 λG,L1,T1. ⦃G, L1⦄ ⊢ T1 ![a,h] →
                                 ∀n,T2. ⦃G, L1⦄ ⊢ T1 ➡*[n,h] T2 →
                                 ∀L2. ⦃G, L1⦄ ⊢ ➡[h] L2 → ⦃G, L2⦄ ⊢ T2 ![a,h].

definition IH_cnv_cpm_conf_lpr (a) (h): relation3 genv lenv term ≝
                               λG,L0,T0. ⦃G, L0⦄ ⊢ T0 ![a,h] →
                               ∀n1,T1. ⦃G, L0⦄ ⊢ T0 ➡[n1,h] T1 → ∀n2,T2. ⦃G, L0⦄ ⊢ T0 ➡[n2,h] T2 →
                               ∀L1. ⦃G, L0⦄ ⊢ ➡[h] L1 → ∀L2. ⦃G, L0⦄ ⊢ ➡[h] L2 →
                               ∃∃T. ⦃G, L1⦄ ⊢ T1 ➡*[n2-n1,h] T & ⦃G, L2⦄ ⊢ T2 ➡*[n1-n2,h] T.

definition IH_cnv_cpms_strip_lpr (a) (h): relation3 genv lenv term ≝
                                 λG,L0,T0. ⦃G, L0⦄ ⊢ T0 ![a,h] →
                                 ∀n1,T1. ⦃G, L0⦄ ⊢ T0 ➡*[n1,h] T1 → ∀n2,T2. ⦃G, L0⦄ ⊢ T0 ➡[n2,h] T2 →
                                 ∀L1. ⦃G, L0⦄ ⊢ ➡[h] L1 → ∀L2. ⦃G, L0⦄ ⊢ ➡[h] L2 →
                                 ∃∃T. ⦃G, L1⦄ ⊢ T1 ➡*[n2-n1,h] T & ⦃G, L2⦄ ⊢ T2 ➡*[n1-n2,h] T.

definition IH_cnv_cpms_conf_lpr (a) (h): relation3 genv lenv term ≝
                                λG,L0,T0. ⦃G, L0⦄ ⊢ T0 ![a,h] →
                                ∀n1,T1. ⦃G, L0⦄ ⊢ T0 ➡*[n1,h] T1 → ∀n2,T2. ⦃G, L0⦄ ⊢ T0 ➡*[n2,h] T2 →
                                ∀L1. ⦃G, L0⦄ ⊢ ➡[h] L1 → ∀L2. ⦃G, L0⦄ ⊢ ➡[h] L2 →
                                ∃∃T. ⦃G, L1⦄ ⊢ T1 ➡*[n2-n1,h] T & ⦃G, L2⦄ ⊢ T2 ➡*[n1-n2,h] T.

definition IH_cnv_cpsms_conf_lpr (a) (h) (o): relation3 genv lenv term ≝
                                 λG,L0,T0. ⦃G, L0⦄ ⊢ T0 ![a,h] →
                                 ∀n1,T1. ⦃G, L0⦄ ⊢ T0 ➡*[n1,h,o] T1 → ∀n2,T2. ⦃G, L0⦄ ⊢ T0 ➡*[n2,h,o] T2 →
                                 ∀L1. ⦃G, L0⦄ ⊢ ➡[h] L1 → ∀L2. ⦃G, L0⦄ ⊢ ➡[h] L2 →
                                 ∃∃T. ⦃G, L1⦄ ⊢ T1 ➡*[n2-n1,h] T & ⦃G, L2⦄ ⊢ T2 ➡*[n1-n2,h] T.

(* Properties for preservation **********************************************)

lemma cnv_cpms_trans_lpr_far (a) (h) (o):
                             ∀G0,L0,T0.
                             (∀G1,L1,T1. ⦃G0, L0, T0⦄ >[h, o] ⦃G1, L1, T1⦄ → IH_cnv_cpm_trans_lpr a h G1 L1 T1) →
                             ∀G1,L1,T1. ⦃G0, L0, T0⦄ >[h, o] ⦃G1, L1, T1⦄ → IH_cnv_cpms_trans_lpr a h G1 L1 T1.
#a #h #o #G0 #L0 #T0 #IH #G1 #L1 #T1 #H01 #HT1 #n #T2 #H
@(cpms_ind_dx … H) -n -T2
/4 width=7 by cpms_fwd_fpbs, fpbg_fpbs_trans/
qed-.

lemma cnv_cpm_conf_lpr_far (a) (h) (o):
                           ∀G0,L0,T0.
                           (∀G1,L1,T1. ⦃G0, L0, T0⦄ >[h, o] ⦃G1, L1, T1⦄ → IH_cnv_cpms_conf_lpr a h G1 L1 T1) →
                           ∀G1,L1,T1. ⦃G0, L0, T0⦄ >[h, o] ⦃G1, L1, T1⦄ → IH_cnv_cpm_conf_lpr a h G1 L1 T1.
/3 width=8 by cpm_cpms/ qed-.

lemma cnv_cpms_strip_lpr_far (a) (h) (o):
                             ∀G0,L0,T0.
                             (∀G1,L1,T1. ⦃G0, L0, T0⦄ >[h, o] ⦃G1, L1, T1⦄ → IH_cnv_cpms_conf_lpr a h G1 L1 T1) →
                             ∀G1,L1,T1. ⦃G0, L0, T0⦄ >[h, o] ⦃G1, L1, T1⦄ → IH_cnv_cpms_strip_lpr a h G1 L1 T1.
/3 width=8 by cpm_cpms/ qed-.
