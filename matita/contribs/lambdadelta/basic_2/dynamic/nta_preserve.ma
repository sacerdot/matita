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

include "basic_2/rt_equivalence/cpcs_cprs.ma".
include "basic_2/dynamic/cnv_preserve.ma".
include "basic_2/dynamic/nta.ma".

(* NATIVE TYPE ASSIGNMENT FOR TERMS *****************************************)

(* Properties based on preservation *****************************************)

lemma cnv_cpms_nta (a) (h) (G) (L):
      ∀T. ⦃G,L⦄ ⊢ T ![a,h] → ∀U.⦃G,L⦄ ⊢ T ➡*[1,h] U → ⦃G,L⦄ ⊢ T :[a,h] U.
/3 width=4 by cnv_cast, cnv_cpms_trans/ qed.

lemma cnv_nta_sn (a) (h) (G) (L):
      ∀T. ⦃G,L⦄ ⊢ T ![a,h] → ∃U. ⦃G,L⦄ ⊢ T :[a,h] U.
#a #h #G #L #T #HT
elim (cnv_fwd_cpm_SO … HT) #U #HTU
/4 width=2 by cnv_cpms_nta, cpm_cpms, ex_intro/
qed-.

(* Basic_1: was: ty3_typecheck *)
lemma nta_typecheck (a) (h) (G) (L):
      ∀T,U. ⦃G,L⦄ ⊢ T :[a,h] U → ∃T0. ⦃G,L⦄ ⊢ ⓝU.T :[a,h] T0.
/3 width=1 by cnv_cast, cnv_nta_sn/ qed-.

(* Basic_1: was: ty3_correct *)
(* Basic_2A1: was: ntaa_fwd_correct *)
lemma nta_fwd_correct (a) (h) (G) (L):
      ∀T,U. ⦃G,L⦄ ⊢ T :[a,h] U → ∃T0. ⦃G,L⦄ ⊢ U :[a,h] T0.
/3 width=2 by nta_fwd_cnv_dx, cnv_nta_sn/ qed-.

lemma nta_pure_cnv (h) (G) (L):
      ∀T,U. ⦃G,L⦄ ⊢ T :*[h] U →
      ∀V. ⦃G,L⦄ ⊢ ⓐV.U !*[h] → ⦃G,L⦄ ⊢ ⓐV.T :*[h] ⓐV.U.
#h #G #L #T #U #H1 #V #H2
elim (cnv_inv_cast … H1) -H1 #X0 #HU #HT #HUX0 #HTX0
elim (cnv_inv_appl … H2) #n #p #X1 #X2 #_ #HV #_ #HVX1 #HUX2
elim (cnv_cpms_conf … HU … HUX0 … HUX2) -HU -HUX2
<minus_O_n <minus_n_O #X #HX0 #H
elim (cpms_inv_abst_sn … H) -H #X3 #X4 #HX13 #HX24 #H destruct
@(cnv_cast … (ⓐV.X0)) [2:|*: /2 width=1 by cpms_appl_dx/ ]
@(cnv_appl … X3) [4: |*: /2 width=7 by cpms_trans, cpms_cprs_trans/ ]
#H destruct
qed.

(* Inversion lemmas based on preservation ***********************************)

lemma nta_inv_bind_sn_cnv (a) (h) (p) (I) (G) (K) (X2):
      ∀V,T. ⦃G,K⦄ ⊢ ⓑ{p,I}V.T :[a,h] X2 →
      ∃∃U. ⦃G,K⦄ ⊢ V ![a,h] & ⦃G,K.ⓑ{I}V⦄ ⊢ T :[a,h] U & ⦃G,K⦄ ⊢ ⓑ{p,I}V.U ⬌*[h] X2 & ⦃G,K⦄ ⊢ X2 ![a,h].
#a #h #p * #G #K #X2 #V #T #H
elim (cnv_inv_cast … H) -H #X1 #HX2 #H1 #HX21 #H2
elim (cnv_inv_bind … H1) -H1 #HV #HT
[ elim (cpms_inv_abbr_sn_dx … H2) -H2 *
  [ #V0 #U #HV0 #HTU #H destruct
    /4 width=5 by cnv_cpms_nta, cprs_div, cpms_bind, ex4_intro/
  | #U #HTU #HX1U #H destruct
    /4 width=5 by cnv_cpms_nta, cprs_div, cpms_zeta, ex4_intro/
  ]
| elim (cpms_inv_abst_sn … H2) -H2 #V0 #U #HV0 #HTU #H destruct
  /4 width=5 by cnv_cpms_nta, cprs_div, cpms_bind, ex4_intro/
]
qed-.

(* Basic_1: uses: ty3_gen_appl *)
lemma nta_inv_appl_sn (h) (G) (L) (X2):
      ∀V,T. ⦃G,L⦄ ⊢ ⓐV.T :[h] X2 →
      ∃∃p,W,U. ⦃G,L⦄ ⊢ V :[h] W & ⦃G,L⦄ ⊢ T :[h] ⓛ{p}W.U & ⦃G,L⦄ ⊢ ⓐV.ⓛ{p}W.U ⬌*[h] X2 & ⦃G,L⦄ ⊢ X2 ![h].
#h #G #L #X2 #V #T #H
elim (cnv_inv_cast … H) -H #X #HX2 #H1 #HX2 #H2
elim (cnv_inv_appl … H1) * [ | #n ] #p #W #U #Hn #HV #HT #HVW #HTU
[ lapply (cnv_cpms_trans … HT … HTU) #H
  elim (cnv_inv_bind … H) -H #_ #HU
  elim (cnv_fwd_cpm_SO … HU) #U0 #HU0 -HU
  lapply (cpms_step_dx … HTU 1 (ⓛ{p}W.U0) ?) -HTU [ /2 width=1 by cpm_bind/ ] #HTU
| lapply (le_n_O_to_eq n ?) [ /3 width=1 by le_S_S_to_le/ ] -Hn #H destruct
]
lapply (cpms_appl_dx … V V … HTU) [1,3: // ] #HVTU
elim (cnv_cpms_conf … H1 … H2 … HVTU) -H1 -H2 -HVTU <minus_n_n #X0 #HX0 #HUX0
@ex4_3_intro [6,13: |*: /2 width=5 by cnv_cpms_nta/ ]
/3 width=5 by cprs_div, cprs_trans/
qed-.

(* Basic_2A1: uses: nta_inv_cast1 *)
lemma nta_inv_cast_sn (a) (h) (G) (L) (X2):
      ∀U,T. ⦃G,L⦄ ⊢ ⓝU.T :[a,h] X2 →
      ∧∧ ⦃G,L⦄ ⊢ T :[a,h] U & ⦃G,L⦄ ⊢ U ⬌*[h] X2 & ⦃G,L⦄ ⊢ X2 ![a,h].
#a #h #G #L #X2 #U #T #H
elim (cnv_inv_cast … H) -H #X0 #HX2 #H1 #HX20 #H2
elim (cnv_inv_cast … H1) #X #HU #HT #HUX #HTX
elim (cpms_inv_cast1 … H2) -H2 [ * || * ]
[ #U0 #T0 #HU0 #HT0 #H destruct -HU -HU0
  elim (cnv_cpms_conf … HT … HTX … HT0) -HT -HTX -HT0
  <minus_n_n #T1 #HXT1 #HT01
  @and3_intro // @(cprs_div … T1) /3 width=4 by cprs_trans, cpms_eps/ (**) (* full auto too slow *)
| #HTX0 -HU
  elim (cnv_cpms_conf … HT … HTX … HTX0) -HT -HTX -HTX0
  <minus_n_n #T1 #HXT1 #HXT01
  @and3_intro // @(cprs_div … T1) /2 width=3 by cprs_trans/ (**) (* full auto too slow *)
| #m #HUX0 #H destruct -HT -HTX
  elim (cnv_cpms_conf … HU … HUX … HUX0) -HU -HUX0
  <minus_n_n #U1 #HXU1 #HXU01
  @and3_intro // @(cprs_div … U1) /2 width=3 by cprs_trans/ (**) (* full auto too slow *)
]
qed-.

(* Basic_1: uses: ty3_gen_cast *)
lemma nta_inv_cast_sn_old (a) (h) (G) (L) (X2):
      ∀T0,T1. ⦃G,L⦄ ⊢ ⓝT1.T0 :[a,h] X2 →
      ∃∃T2. ⦃G,L⦄ ⊢ T0 :[a,h] T1 & ⦃G,L⦄ ⊢ T1 :[a,h] T2 & ⦃G,L⦄ ⊢ ⓝT2.T1 ⬌*[h] X2 & ⦃G,L⦄ ⊢ X2 ![a,h].
#a #h #G #L #X2 #T0 #T1 #H
elim (cnv_inv_cast … H) -H #X0 #HX2 #H1 #HX20 #H2
elim (cnv_inv_cast … H1) #X #HT1 #HT0 #HT1X #HT0X
elim (cpms_inv_cast1 … H2) -H2 [ * || * ]
[ #U1 #U0 #HTU1 #HTU0 #H destruct
  elim (cnv_cpms_conf … HT0 … HT0X … HTU0) -HT0 -HT0X -HTU0
  <minus_n_n #X0 #HX0 #HUX0
  lapply (cprs_trans … HT1X … HX0) -X #HT1X0
  /5 width=7 by cnv_cpms_nta, cpcs_cprs_div, cprs_div, cpms_cast, ex4_intro/
| #HTX0
  elim (cnv_cpms_conf … HT0 … HT0X … HTX0) -HT0 -HT0X -HTX0
  <minus_n_n #X1 #HX1 #HX01
  elim (cnv_nta_sn … HT1) -HT1 #U1 #HTU1
  lapply (cprs_trans … HT1X … HX1) -X #HTX1
  lapply (cprs_trans … HX20 … HX01) -X0 #HX21
  /4 width=5 by cprs_div, cpms_eps, ex4_intro/
| #n #HT1X0 #H destruct -X -HT0
  elim (cnv_nta_sn … HT1) -HT1 #U1 #HTU1
  /4 width=5 by cprs_div, cpms_eps, ex4_intro/
]
qed-.

(* Forward lemmas based on preservation *************************************)

(* Basic_1: was: ty3_unique *)
theorem nta_mono (a) (h) (G) (L) (T):
        ∀U1. ⦃G,L⦄ ⊢ T :[a,h] U1 → ∀U2. ⦃G,L⦄ ⊢ T :[a,h] U2 → ⦃G,L⦄  ⊢ U1 ⬌*[h] U2.
#a #h #G #L #T #U1 #H1 #U2 #H2
elim (cnv_inv_cast … H1) -H1 #X1 #_ #_ #HUX1 #HTX1
elim (cnv_inv_cast … H2) -H2 #X2 #_ #HT #HUX2 #HTX2
elim (cnv_cpms_conf … HT … HTX1 … HTX2) -T <minus_n_n #X #HX1 #HX2
/3 width=5 by cprs_div, cprs_trans/
qed-.
