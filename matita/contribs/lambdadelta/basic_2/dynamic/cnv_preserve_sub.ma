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

include "basic_2/rt_transition/lpr.ma".
include "basic_2/rt_computation/cpms_fpbg.ma".
include "basic_2/dynamic/cnv.ma".

(* CONTEXT-SENSITIVE NATIVE VALIDITY FOR TERMS ******************************)

(* Inductive premises for the preservation results **************************)

definition IH_cnv_cpm_trans_lpr (h) (a): relation3 genv lenv term ≝
           λG,L1,T1. ❪G,L1❫ ⊢ T1 ![h,a] →
           ∀n,T2. ❪G,L1❫ ⊢ T1 ➡[h,n] T2 →
           ∀L2. ❪G,L1❫ ⊢ ➡[h,0] L2 → ❪G,L2❫ ⊢ T2 ![h,a].

definition IH_cnv_cpms_trans_lpr (h) (a): relation3 genv lenv term ≝
           λG,L1,T1. ❪G,L1❫ ⊢ T1 ![h,a] →
           ∀n,T2. ❪G,L1❫ ⊢ T1 ➡*[h,n] T2 →
           ∀L2. ❪G,L1❫ ⊢ ➡[h,0] L2 → ❪G,L2❫ ⊢ T2 ![h,a].

definition IH_cnv_cpm_conf_lpr (h) (a): relation3 genv lenv term ≝
           λG,L0,T0. ❪G,L0❫ ⊢ T0 ![h,a] →
           ∀n1,T1. ❪G,L0❫ ⊢ T0 ➡[h,n1] T1 → ∀n2,T2. ❪G,L0❫ ⊢ T0 ➡[h,n2] T2 →
           ∀L1. ❪G,L0❫ ⊢ ➡[h,0] L1 → ∀L2. ❪G,L0❫ ⊢ ➡[h,0] L2 →
           ∃∃T. ❪G,L1❫ ⊢ T1 ➡*[h,n2-n1] T & ❪G,L2❫ ⊢ T2 ➡*[h,n1-n2] T.

definition IH_cnv_cpms_strip_lpr (h) (a): relation3 genv lenv term ≝
           λG,L0,T0. ❪G,L0❫ ⊢ T0 ![h,a] →
           ∀n1,T1. ❪G,L0❫ ⊢ T0 ➡*[h,n1] T1 → ∀n2,T2. ❪G,L0❫ ⊢ T0 ➡[h,n2] T2 →
           ∀L1. ❪G,L0❫ ⊢ ➡[h,0] L1 → ∀L2. ❪G,L0❫ ⊢ ➡[h,0] L2 →
           ∃∃T. ❪G,L1❫ ⊢ T1 ➡*[h,n2-n1] T & ❪G,L2❫ ⊢ T2 ➡*[h,n1-n2] T.

definition IH_cnv_cpms_conf_lpr (h) (a): relation3 genv lenv term ≝
           λG,L0,T0. ❪G,L0❫ ⊢ T0 ![h,a] →
           ∀n1,T1. ❪G,L0❫ ⊢ T0 ➡*[h,n1] T1 → ∀n2,T2. ❪G,L0❫ ⊢ T0 ➡*[h,n2] T2 →
           ∀L1. ❪G,L0❫ ⊢ ➡[h,0] L1 → ∀L2. ❪G,L0❫ ⊢ ➡[h,0] L2 →
           ∃∃T. ❪G,L1❫ ⊢ T1 ➡*[h,n2-n1] T & ❪G,L2❫ ⊢ T2 ➡*[h,n1-n2] T.

(* Auxiliary properties for preservation ************************************)

fact cnv_cpms_trans_lpr_sub (h) (a):
     ∀G0,L0,T0.
     (∀G1,L1,T1. ❪G0,L0,T0❫ > ❪G1,L1,T1❫ → IH_cnv_cpm_trans_lpr h a G1 L1 T1) →
     ∀G1,L1,T1. ❪G0,L0,T0❫ > ❪G1,L1,T1❫ → IH_cnv_cpms_trans_lpr h a G1 L1 T1.
#h #a #G0 #L0 #T0 #IH #G1 #L1 #T1 #H01 #HT1 #n #T2 #H
@(cpms_ind_dx … H) -n -T2
/3 width=7 by fpbg_cpms_trans/
qed-.

fact cnv_cpm_conf_lpr_sub (h) (a):
     ∀G0,L0,T0.
     (∀G1,L1,T1. ❪G0,L0,T0❫ > ❪G1,L1,T1❫ → IH_cnv_cpms_conf_lpr h a G1 L1 T1) →
     ∀G1,L1,T1. ❪G0,L0,T0❫ > ❪G1,L1,T1❫ → IH_cnv_cpm_conf_lpr h a G1 L1 T1.
/3 width=8 by cpm_cpms/ qed-.

fact cnv_cpms_strip_lpr_sub (h) (a):
     ∀G0,L0,T0.
     (∀G1,L1,T1. ❪G0,L0,T0❫ > ❪G1,L1,T1❫ → IH_cnv_cpms_conf_lpr h a G1 L1 T1) →
     ∀G1,L1,T1. ❪G0,L0,T0❫ > ❪G1,L1,T1❫ → IH_cnv_cpms_strip_lpr h a G1 L1 T1.
/3 width=8 by cpm_cpms/ qed-.
