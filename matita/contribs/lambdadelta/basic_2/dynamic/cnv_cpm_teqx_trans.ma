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

include "basic_2/dynamic/cnv_cpm_trans.ma".
include "basic_2/dynamic/cnv_cpm_teqx.ma".

(* CONTEXT-SENSITIVE NATIVE VALIDITY FOR TERMS ******************************)

definition IH_cnv_cpm_teqx_cpm_trans (h) (a): relation3 genv lenv term ≝
           λG,L,T1. ❪G,L❫ ⊢ T1 ![h,a] →
           ∀n1,T. ❪G,L❫ ⊢ T1 ➡[h,n1] T → T1 ≛ T →
           ∀n2,T2. ❪G,L❫ ⊢ T ➡[h,n2] T2 →
           ∃∃T0. ❪G,L❫ ⊢ T1 ➡[h,n2] T0 & ❪G,L❫ ⊢ T0 ➡[h,n1] T2 & T0 ≛ T2.

(* Transitive properties restricted rt-transition for terms *****************)

fact cnv_cpm_teqx_cpm_trans_sub (h) (a) (G0) (L0) (T0):
     (∀G,L,T. ❪G0,L0,T0❫ > ❪G,L,T❫ → IH_cnv_cpm_trans_lpr h a G L T) →
     (∀G,L,T. ❪G0,L0,T0❫ ⬂+ ❪G,L,T❫ → IH_cnv_cpm_teqx_cpm_trans h a G L T) →
     ∀G,L,T1. G0 = G → L0 = L → T0 = T1 → IH_cnv_cpm_teqx_cpm_trans h a G L T1.
#h #a #G0 #L0 #T0 #IH2 #IH1 #G #L * [| * [| * ]]
[ #I #_ #_ #_ #_ #n1 #X1 #H1X #H2X #n2 #X2 #HX2 destruct -G0 -L0 -T0
  elim (cpm_teqx_inv_atom_sn … H1X H2X) -H1X -H2X *
  [ #H1 #H2 destruct /2 width=4 by ex3_intro/
  | #s #H1 #H2 #H3 destruct
    elim (cpm_inv_sort1 … HX2) -HX2 #H #Hn2 destruct >iter_n_Sm
    /3 width=4 by cpm_sort, teqx_sort, ex3_intro/
  ]
| #p #I #V1 #T1 #HG #HL #HT #H0 #n1 #X1 #H1X #H2X #n2 #X2 #HX2 destruct
  elim (cpm_teqx_inv_bind_sn … H0 … H1X H2X) -H0 -H1X -H2X #T #_ #H0T1 #H1T1 #H2T1 #H destruct
  elim (cpm_inv_bind1 … HX2) -HX2 *
  [ #V2 #T2 #HV12 #HT2 #H destruct
    elim (IH1 … H0T1 … H1T1 H2T1 … HT2) -T -IH1 [| // ] #T0 #HT10 #H1T02 #H2T02
    lapply (IH2 … H0T1 … HT10 (L.ⓑ[I]V1) ?) -IH2 -H0T1 [3:|*: /2 width=1 by fqup_fpbg/ ] #HT0
    lapply (cpm_teqx_free … HT0 … H1T02 H2T02 G (L.ⓑ[I]V2)) -H1T02 #H1T02
    /3 width=6 by cpm_bind, teqx_pair, ex3_intro/
  | #T2 #HT2 #HTX2 #H1 #H2 destruct -IH2
    elim (teqx_inv_lifts_dx … H2T1 … HT2) -H2T1 #XT #HXT1 #H2XT2
    lapply (cpm_inv_lifts_bi … H1T1 (Ⓣ) … HXT1 … HT2) -T [3:|*: /3 width=2 by drops_refl, drops_drop/ ] #H1XT2
    lapply (cnv_inv_lifts … H0T1 (Ⓣ) … HXT1) -H0T1 [3:|*: /3 width=2 by drops_refl, drops_drop/ ] #H0XT2
    elim (IH1 … H0XT2 … H1XT2 H2XT2 … HTX2) -T2 -IH1 -H0XT2 [| /2 width=1 by fqup_zeta/ ] #T2 #HXT2 #H1TX2 #H2XT2
    /3 width=4 by cpm_zeta, ex3_intro/
  ]
| #V1 #XT1 #HG #HL #HT #H0 #n1 #X1 #H1X #H2X #n2 #X2 #HX2 destruct
  elim (cpm_teqx_inv_appl_sn … H0 … H1X H2X) -H0 -H1X -H2X #m #q #W1 #U1 #XT #_ #_ #_ #_ #H0T1 #H1T1 #H2T1 #H destruct -m -q -W1 -U1
  elim (cpm_inv_appl1 … HX2) -HX2 *
  [ #V2 #T2 #HV12 #HT2 #H destruct -IH2
    elim (IH1 … H0T1 … H1T1 H2T1 … HT2) -XT -IH1 -H0T1 [| // ] #T0 #HT10 #H1T02 #H2T02
    /3 width=6 by cpm_appl, teqx_pair, ex3_intro/
  | #p #V2 #W1 #W2 #T #T2 #HV12 #HW12 #HT2 #H1 #H2 destruct
    elim (cpm_teqx_inv_bind_dx … H0T1 … H1T1 H2T1) -H0T1 -H1T1 -H2T1 #T1 #_ #H0T1 #H1T1 #H2T1 #H destruct
    elim (IH1 … H0T1 … H1T1 H2T1 … HT2) -T -IH1 [| // ] #T0 #HT10 #H1T02 #H2T02
    lapply (IH2 … H0T1 … HT10 (L.ⓛW1) ?) -IH2 -H0T1 [3:|*: /2 width=1 by fqup_fpbg/ ] #HT0
    lapply (cpm_teqx_free … HT0 … H1T02 H2T02 G (L.ⓓⓝW2.V2)) -H1T02 #H1T02
    /3 width=6 by cpm_beta, cpm_bind, teqx_pair, ex3_intro/
  | #p #V2 #V0 #W1 #W2 #T #T2 #HV12 #HV20 #HW12 #HT2 #H1 #H2 destruct
    elim (cpm_teqx_inv_bind_dx … H0T1 … H1T1 H2T1) -H0T1 -H1T1 -H2T1 #T1 #_ #H0T1 #H1T1 #H2T1 #H destruct
    elim (IH1 … H0T1 … H1T1 H2T1 … HT2) -T -IH1 [| // ] #T0 #HT10 #H1T02 #H2T02
    lapply (IH2 … H0T1 … HT10 (L.ⓓW1) ?) -IH2 -H0T1 [3:|*: /2 width=1 by fqup_fpbg/ ] #HT0
    lapply (cpm_teqx_free … HT0 … H1T02 H2T02 G (L.ⓓW2)) -H1T02
    /4 width=8 by cpm_theta, cpm_appl, cpm_bind, teqx_pair, ex3_intro/
  ]
| #U1 #T1 #HG #HL #HT #H0 #n1 #X1 #H1X #H2X #n2 #X2 #HX2 destruct -IH2
  elim (cpm_teqx_inv_cast_sn … H0 … H1X H2X) -H0 -H1X -H2X #U0 #U #T #_ #_ #H0U1 #H1U1 #H2U1 #H0T1 #H1T1 #H2T1 #H destruct -U0
  elim (cpm_inv_cast1 … HX2) -HX2 [ * || * ]
  [ #U2 #T2 #HU2 #HT2 #H destruct
    elim (IH1 … H0U1 … H1U1 H2U1 … HU2) -U -H0U1 [| // ] #U0 #HU10 #H1U02 #H2U02
    elim (IH1 … H0T1 … H1T1 H2T1 … HT2) -T -IH1 -H0T1 [| // ] #T0 #HT10 #H1T02 #H2T02
    /3 width=6 by cpm_cast, teqx_pair, ex3_intro/
  | #HTX2 -U -H0U1
    elim (IH1 … H0T1 … H1T1 H2T1 … HTX2) -T -IH1 -H0T1 [| // ] #T0 #HT10 #H1T02 #H2T02
    /3 width=4 by cpm_eps, ex3_intro/
  | #m2 #HUX2 #H destruct -T -H0T1
    elim (IH1 … H0U1 … H1U1 H2U1 … HUX2) -U -H0U1 [| // ] #U0 #HU10 #H1U02 #H2U02
    /3 width=4 by cpm_ee, ex3_intro/
  ]
]
qed-.

fact cnv_cpm_teqx_cpm_trans_aux (h) (a) (G0) (L0) (T0):
     (∀G,L,T. ❪G0,L0,T0❫ > ❪G,L,T❫ → IH_cnv_cpm_trans_lpr h a G L T) →
     IH_cnv_cpm_teqx_cpm_trans h a G0 L0 T0.
#h #a #G0 #L0 #T0
@(fqup_wf_ind (Ⓣ) … G0 L0 T0) -G0 -L0 -T0 #G0 #L0 #T0 #IH #IH0
/5 width=10 by cnv_cpm_teqx_cpm_trans_sub, fqup_fpbg_trans/
qed-.
