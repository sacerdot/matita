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

include "basic_2/rt_computation/cpts_cpms.ma".
include "basic_2/rt_equivalence/cpcs_cpcs.ma".
include "basic_2/rt_equivalence/cpes.ma".
include "basic_2/dynamic/cnv_preserve_cpcs.ma".

(* CONTEXT-SENSITIVE NATIVE VALIDITY FOR TERMS ******************************)

(* Forward lemmas with t-bound t-computarion for terms **********************)

lemma cpts_cpms_conf_eq (h) (n) (a) (G) (L):
      ∀T0. ❨G,L❩ ⊢ T0 ![h,a] → ∀T1. ❨G,L❩ ⊢ T0 ⬆*[h,n] T1 →
      ∀T2. ❨G,L❩ ⊢ T0 ➡*[h,n] T2 → ❨G,L❩ ⊢ T1 ⬌*[h] T2.
#h #a #n #G #L #T0 #HT0 #T1 #HT01 #T2 #HT02
/3 width=6 by cpts_fwd_cpms, cnv_cpms_conf_eq/
qed-.

(* Inversion lemmas with t-bound t-computarion for terms ********************)

lemma cnv_inv_cast_cpts (h) (a) (nu) (nt) (G) (L):
      ∀U1. ❨G,L❩ ⊢ U1 ![h,a] → ∀U2. ❨G,L❩ ⊢ U1 ⬆*[h,nu] U2 →
      ∀T1. ❨G,L❩ ⊢ T1 ![h,a] → ∀T2. ❨G,L❩ ⊢ T1 ⬆*[h,nt] T2 →
      ❨G,L❩ ⊢ U1 ⬌*[h,nu,nt] T1 → ❨G,L❩ ⊢ U2 ⬌*[h] T2.
#h #a #nu #nt #G #L #U1 #HU1 #U2 #HU12 #T1 #HT1 #T2 #HT12 * #X1 #HUX1 #HTX1
/3 width=8 by cpts_cpms_conf_eq, cpcs_canc_dx/
qed-.

lemma cnv_inv_appl_cpts (h) (a) (nv) (nt) (p) (G) (L):
      ∀V1. ❨G,L❩ ⊢ V1 ![h,a] → ∀V2. ❨G,L❩ ⊢ V1 ⬆*[h,nv] V2 →
      ∀T1. ❨G,L❩ ⊢ T1 ![h,a] → ∀T2. ❨G,L❩ ⊢ T1 ⬆*[h,nt] T2 →
      ∀V0. ❨G,L❩ ⊢ V1 ➡*[h,nv] V0 → ∀T0. ❨G,L❩ ⊢ T1 ➡*[h,nt] ⓛ[p]V0.T0 →
      ∃∃W0,U0. ❨G,L❩ ⊢ V2 ➡*[h,0] W0 & ❨G,L❩ ⊢ T2 ➡*[h,0] ⓛ[p]W0.U0.
#h #a #nv #nt #p #G #L #V1 #HV1 #V2 #HV12 #T1 #HT1 #T2 #HT12 #V0 #HV20 #T0 #HT20
lapply (cpts_cpms_conf_eq … HV1 … HV12 … HV20) -nv -V1 #HV20
lapply (cpts_cpms_conf_eq … HT1 … HT12 … HT20) -nt -T1 #HT20
lapply (cpcs_bind_sn … Abst … T0 HV20 p) -HV20 #HV20
lapply (cpcs_canc_dx … HT20 … HV20) -V0 #HT20
elim (cpcs_inv_cprs … HT20) -HT20 #X #HT2X #HT0X
elim (cpms_inv_abst_sn … HT0X) -HT0X #V0 #X0 #HV20 #_ #H destruct
/2 width=4 by ex2_2_intro/
qed-.

(* Properties with t-bound t-computarion for terms **************************)

lemma cnv_cast_cpts (h) (a) (nu) (nt) (G) (L):
      ∀U1. ❨G,L❩ ⊢ U1 ![h,a] → ∀U2. ❨G,L❩ ⊢ U1 ⬆*[h,nu] U2 →
      ∀T1. ❨G,L❩ ⊢ T1 ![h,a] → ∀T2. ❨G,L❩ ⊢ T1 ⬆*[h,nt] T2 →
      ❨G,L❩ ⊢ U2 ⬌*[h] T2 → ❨G,L❩ ⊢ U1 ⬌*[h,nu,nt] T1.
#h #a #nu #nt #G #L #U1 #HU1 #U2 #HU12 #T1 #HT1 #T2 #HT12 #HUT2
elim (cpcs_inv_cprs … HUT2) -HUT2 #X2 #HUX2 #HTX2
/3 width=5 by cpts_cprs_trans, cpms_div/
qed-.

lemma cnv_appl_cpts (h) (a) (nv) (nt) (p) (G) (L):
      ∀V1. ❨G,L❩ ⊢ V1 ![h,a] → ∀V2. ❨G,L❩ ⊢ V1 ⬆*[h,nv] V2 →
      ∀T1. ❨G,L❩ ⊢ T1 ![h,a] → ∀T2. ❨G,L❩ ⊢ T1 ⬆*[h,nt] T2 →
      ∀V0. ❨G,L❩ ⊢ V2 ➡*[h,0] V0 → ∀T0. ❨G,L❩ ⊢ T2 ➡*[h,0] ⓛ[p]V0.T0 →
      ∃∃W0,U0. ❨G,L❩ ⊢ V1 ➡*[h,nv] W0 & ❨G,L❩ ⊢ T1 ➡*[h,nt] ⓛ[p]W0.U0.
#h #a #nv #nt #p #G #L #V1 #HV1 #V2 #HV12 #T1 #HT1 #T2 #HT12 #V0 #HV20 #T0 #HT20
/3 width=6 by cpts_cprs_trans, ex2_2_intro/
qed-.
