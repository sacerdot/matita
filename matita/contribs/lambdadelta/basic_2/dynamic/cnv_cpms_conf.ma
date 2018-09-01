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
include "basic_2/dynamic/cnv_cpm_trans.ma".
include "basic_2/dynamic/cnv_cpm_conf.ma".

(* CONTEXT-SENSITIVE NATIVE VALIDITY FOR TERMS ******************************)

definition cpsms (n) (h) (o): relation4 genv lenv term term ≝ λG,L,T1,T2.
                 ∃∃n1,n2,T. T1 ≛[h,o] T → ⊥ & ⦃G, L⦄ ⊢ T1 ➡[n1,h] T & ⦃G, L⦄ ⊢ T ➡*[n2,h] T2 & n1+n2 = n.

interpretation
   "context-sensitive parallel stratified t-bound  rt-computarion (term)"
   'PRedStar n h o G L T1 T2 = (cpsms n h o G L T1 T2).

definition IH_cnv_cpsms_conf_lpr (a) (h) (o): relation3 genv lenv term ≝
                                 λG,L0,T0. ⦃G, L0⦄ ⊢ T0 ![a,h] →
                                 ∀n1,T1. ⦃G, L0⦄ ⊢ T0 ➡*[n1,h,o] T1 → ∀n2,T2. ⦃G, L0⦄ ⊢ T0 ➡*[n2,h,o] T2 →
                                 ∀L1. ⦃G, L0⦄ ⊢ ➡[h] L1 → ∀L2. ⦃G, L0⦄ ⊢ ➡[h] L2 →
                                 ∃∃T. ⦃G, L1⦄ ⊢ T1 ➡*[n2-n1,h] T & ⦃G, L2⦄ ⊢ T2 ➡*[n1-n2,h] T.

(* Sub confluence propery with t-bound rt-computation for terms *************)

fact cnv_cpsms_conf_lpr_aux (a) (h) (o):
                            ∀G0,L0,T0.
                            (∀G1,L1,T1. ⦃G0, L0, T0⦄ >[h, o] ⦃G1, L1, T1⦄ → IH_cnv_cpm_trans_lpr a h G1 L1 T1) →
                            (∀G1,L1,T1. ⦃G0, L0, T0⦄ >[h, o] ⦃G1, L1, T1⦄ → IH_cnv_cpms_conf_lpr a h G1 L1 T1) →
                            ∀G1,L1,T1. G0 = G1 → L0 = L1 → T0 = T1 → IH_cnv_cpsms_conf_lpr a h o G1 L1 T1.
#a #h #o #G #L #T #IH2 #IH1 #G0 #L0 #T0 #HG #HL #HT #HT0
#n1 #T1 * #m11 #m12 #X1 #HnX01 #HX01 #HXT1 #H1
#n2 #T2 * #m21 #m22 #X2 #HnX02 #HX02 #HXT2 #H2
#L1 #HL01 #L2 #HL02 destruct
lapply (cnv_cpm_trans_lpr_aux … IH1 IH2 … HX01 … L0 ?) // #HX1
lapply (cnv_cpm_trans_lpr_aux … IH1 IH2 … HX02 … L0 ?) // #HX2
elim (cnv_cpm_conf_lpr_aux … IH2 IH1 … HX01 … HX02 … L0 … L0) // #Z0 #HXZ10 #HXZ20
cut (⦃G0,L0,T0⦄ >[h,o] ⦃G0,L0,X1⦄) [ /4 width=5 by cpms_fwd_fpbs, cpm_fpb, ex2_3_intro/ ] #H1fpbg (**) (* cut *)
lapply (fpbg_fpbs_trans ??? G0 ? L0 ? Z0 ? … H1fpbg) [ /2 width=2 by cpms_fwd_fpbs/ ] #H2fpbg
lapply (cnv_cpms_trans_lpr_sub … IH2 … HXZ10 … L0 ?) // #HZ0
elim (IH1 … HXT1 … HXZ10 … L1 … L0) [|*: /4 width=2 by fpb_fpbg, cpm_fpb/ ] -HXT1 -HXZ10 #Z1 #HTZ1 #HZ01
elim (IH1 … HXT2 … HXZ20 … L2 … L0) [|*: /4 width=2 by fpb_fpbg, cpm_fpb/ ] -HXT2 -HXZ20 #Z2 #HTZ2 #HZ02
elim (IH1 … HZ01 … HZ02  L1 … L2) // -L0 -T0 -X1 -X2 -Z0 #Z #HZ01 #HZ02
lapply (cpms_trans … HTZ1 … HZ01) -Z1 <arith_l4 #HT1Z
lapply (cpms_trans … HTZ2 … HZ02) -Z2 <arith_l4 #HT2Z
/2 width=3 by ex2_intro/
qed-.
