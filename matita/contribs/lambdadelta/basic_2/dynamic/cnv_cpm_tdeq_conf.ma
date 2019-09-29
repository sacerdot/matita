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

include "ground_2/xoa/ex_4_1_props.ma".
include "basic_2/dynamic/cnv_cpm_tdeq.ma".

(* CONTEXT-SENSITIVE NATIVE VALIDITY FOR TERMS ******************************)

definition IH_cnv_cpm_tdeq_conf_lpr (h) (a): relation3 genv lenv term ≝
           λG,L0,T0. ⦃G,L0⦄ ⊢ T0 ![h,a] →
           ∀n1,T1. ⦃G,L0⦄ ⊢ T0 ➡[n1,h] T1 → T0 ≛ T1 →
           ∀n2,T2. ⦃G,L0⦄ ⊢ T0 ➡[n2,h] T2 → T0 ≛ T2 →
           ∀L1. ⦃G,L0⦄ ⊢ ➡[h] L1 → ∀L2. ⦃G,L0⦄ ⊢ ➡[h] L2 →
           ∃∃T. ⦃G,L1⦄ ⊢ T1 ➡[n2-n1,h] T & T1 ≛ T & ⦃G,L2⦄ ⊢ T2 ➡[n1-n2,h] T & T2 ≛ T.

(* Diamond propery with restricted rt-transition for terms ******************)

fact cnv_cpm_tdeq_conf_lpr_atom_atom_aux (h) (G0) (L1) (L2) (I):
     ∃∃T. ⦃G0,L1⦄ ⊢ ⓪{I} ➡[h] T & ⓪{I} ≛ T & ⦃G0,L2⦄ ⊢ ⓪{I} ➡[h] T & ⓪{I} ≛ T.
#h #G0 #L1 #L2 #I
/2 width=5 by ex4_intro/
qed-.

fact cnv_cpm_tdeq_conf_lpr_atom_ess_aux (h) (G0) (L1) (L2) (s):
     ∃∃T. ⦃G0,L1⦄ ⊢ ⋆s ➡[1,h] T & ⋆s ≛ T & ⦃G0,L2⦄ ⊢ ⋆(⫯[h]s) ➡[h] T & ⋆(⫯[h]s) ≛ T.
#h #G0 #L1 #L2 #s
/3 width=5 by tdeq_sort, ex4_intro/
qed-.

fact cnv_cpm_tdeq_conf_lpr_bind_bind_aux (h) (a) (p) (I) (G0) (L0) (V0) (T0):
     (∀G,L,T. ⦃G0,L0,ⓑ{p,I}V0.T0⦄ ⬂+ ⦃G,L,T⦄ → IH_cnv_cpm_tdeq_conf_lpr h a G L T) →
     ⦃G0,L0⦄ ⊢ ⓑ{p,I}V0.T0 ![h,a] →
     ∀n1,T1. ⦃G0,L0.ⓑ{I}V0⦄ ⊢ T0 ➡[n1,h] T1 → T0 ≛ T1 →
     ∀n2,T2. ⦃G0,L0.ⓑ{I}V0⦄ ⊢ T0 ➡[n2,h] T2 → T0 ≛ T2 →
     ∀L1. ⦃G0,L0⦄ ⊢ ➡[h] L1 → ∀L2. ⦃G0,L0⦄ ⊢ ➡[h] L2 →
     ∃∃T. ⦃G0,L1⦄ ⊢ ⓑ{p,I}V0.T1 ➡[n2-n1,h] T & ⓑ{p,I}V0.T1 ≛ T & ⦃G0,L2⦄ ⊢ ⓑ{p,I}V0.T2 ➡[n1-n2,h] T & ⓑ{p,I}V0.T2 ≛ T.
#h #a #p #I #G0 #L0 #V0 #T0 #IH #H0
#n1 #T1 #H1T01 #H2T01 #n2 #T2 #H1T02 #H2T02
#L1 #HL01 #L2 #HL02
elim (cnv_inv_bind … H0) -H0 #_ #HT0
elim (IH … H1T01 H2T01 … H1T02 H2T02 (L1.ⓑ{I}V0) … (L2.ⓑ{I}V0)) [|*: /2 width=1 by lpr_bind_refl_dx/ ]
#T #H1T1 #H2T1 #H1T2 #H2T2 -L0 -T0
/3 width=7 by cpm_bind, tdeq_pair, ex4_intro/
qed-.

fact cnv_cpm_tdeq_conf_lpr_appl_appl_aux (h) (a) (G0) (L0) (V0) (T0):
     (∀G,L,T. ⦃G0,L0,ⓐV0.T0⦄ ⬂+ ⦃G,L,T⦄ → IH_cnv_cpm_tdeq_conf_lpr h a G L T) →
     ⦃G0,L0⦄ ⊢ ⓐV0.T0 ![h,a] →
     ∀n1,T1. ⦃G0,L0⦄ ⊢ T0 ➡[n1,h] T1 → T0 ≛ T1 →
     ∀n2,T2. ⦃G0,L0⦄ ⊢ T0 ➡[n2,h] T2 → T0 ≛ T2 →
     ∀L1. ⦃G0,L0⦄ ⊢ ➡[h] L1 → ∀L2. ⦃G0,L0⦄ ⊢ ➡[h] L2 →
     ∃∃T. ⦃G0,L1⦄ ⊢ ⓐV0.T1 ➡[n2-n1,h] T & ⓐV0.T1 ≛ T & ⦃G0,L2⦄ ⊢ ⓐV0.T2 ➡[n1-n2,h] T & ⓐV0.T2 ≛ T.
#h #a #G0 #L0 #V0 #T0 #IH #H0
#n1 #T1 #H1T01 #H2T01 #n2 #T2 #H1T02 #H2T02
#L1 #HL01 #L2 #HL02
elim (cnv_inv_appl … H0) -H0 #n0 #p0 #X01 #X02 #_ #_ #HT0 #_ #_ -n0 -p0 -X01 -X02
elim (IH … H1T01 H2T01 … H1T02 H2T02 … HL01 … HL02) [|*: /2 width=1 by fqup_fpbg/ ]
#T #H1T1 #H2T1 #H1T2 #H2T2 -L0 -T0
/3 width=7 by cpm_appl, tdeq_pair, ex4_intro/
qed-.

fact cnv_cpm_tdeq_conf_lpr_cast_cast_aux (h) (a) (G0) (L0) (V0) (T0):
     (∀G,L,T. ⦃G0,L0,ⓝV0.T0⦄ ⬂+ ⦃G,L,T⦄ → IH_cnv_cpm_tdeq_conf_lpr h a G L T) →
     ⦃G0,L0⦄ ⊢ ⓝV0.T0 ![h,a] →
     ∀n1,V1. ⦃G0,L0⦄ ⊢ V0 ➡[n1,h] V1 → V0 ≛ V1 →
     ∀n2,V2. ⦃G0,L0⦄ ⊢ V0 ➡[n2,h] V2 → V0 ≛ V2 →
     ∀T1. ⦃G0,L0⦄ ⊢ T0 ➡[n1,h] T1 → T0 ≛ T1 →
     ∀T2. ⦃G0,L0⦄ ⊢ T0 ➡[n2,h] T2 → T0 ≛ T2 →
     ∀L1. ⦃G0,L0⦄ ⊢ ➡[h] L1 → ∀L2. ⦃G0,L0⦄ ⊢ ➡[h] L2 →
     ∃∃T. ⦃G0,L1⦄ ⊢ ⓝV1.T1 ➡[n2-n1,h] T & ⓝV1.T1 ≛ T & ⦃G0,L2⦄ ⊢ ⓝV2.T2 ➡[n1-n2,h] T & ⓝV2.T2 ≛ T.
#h #a #G0 #L0 #V0 #T0 #IH #H0
#n1 #V1 #H1V01 #H2V01 #n2 #V2 #H1V02 #H2V02 #T1 #H1T01 #H2T01 #T2 #H1T02 #H2T02
#L1 #HL01 #L2 #HL02
elim (cnv_inv_cast … H0) -H0 #X0 #HV0 #HT0 #_ #_ -X0
elim (IH … H1V01 H2V01 … H1V02 H2V02 … HL01 … HL02) [|*: /2 width=1 by fqup_fpbg/ ]
elim (IH … H1T01 H2T01 … H1T02 H2T02 … HL01 … HL02) [|*: /2 width=1 by fqup_fpbg/ ]
#T #H1T1 #H2T1 #H1T2 #H2T2 #V #H1V1 #H2V1 #H1V2 #H2V2 -L0 -V0 -T0
/3 width=7 by cpm_cast, tdeq_pair, ex4_intro/
qed-.

fact cnv_cpm_tdeq_conf_lpr_aux (h) (a) (G0) (L0) (T0):
     (∀G,L,T. ⦃G0,L0,T0⦄ ⬂+ ⦃G,L,T⦄ → IH_cnv_cpm_tdeq_conf_lpr h a G L T) →
     ∀G,L,T. G0 = G → L0 = L → T0 = T → IH_cnv_cpm_tdeq_conf_lpr h a G L T.
#h #a #G0 #L0 #T0 #IH1 #G #L * [| * [| * ]]
[ #I #HG0 #HL0 #HT0 #HT #n1 #X1 #H1X1 #H2X1 #n2 #X2 #H1X2 #H2X2 #L1 #HL1 #L2 #HL2 destruct
  elim (cpm_tdeq_inv_atom_sn … H1X1 H2X1) -H1X1 -H2X1 *
  elim (cpm_tdeq_inv_atom_sn … H1X2 H2X2) -H1X2 -H2X2 *
  [ #H21 #H22 #H11 #H12 destruct -a -L
    <minus_O_n
    /2 width=1 by cnv_cpm_tdeq_conf_lpr_atom_atom_aux/
  | #s2 #H21 #H22 #H23 #H11 #H12 destruct -a -L
    <minus_O_n <minus_n_O
    /2 width=1 by cnv_cpm_tdeq_conf_lpr_atom_ess_aux/
  | #H21 #H22 #s1 #H11 #H12 #H13 destruct -a -L
    <minus_O_n <minus_n_O
    @ex4_commute /2 width=1 by cnv_cpm_tdeq_conf_lpr_atom_ess_aux/
  | #s2 #H21 #H22 #H23 #s1 #H11 #H12 #H13 destruct -a -L
    <minus_n_n
    /2 width=1 by cnv_cpm_tdeq_conf_lpr_atom_atom_aux/
  ]
| #p #I #V #T #HG0 #HL0 #HT0 #HT #n1 #X1 #H1X1 #H2X1 #n2 #X2 #H1X2 #H2X2 #L1 #HL1 #L2 #HL2 destruct
  elim (cpm_tdeq_inv_bind_sn … HT … H1X1 H2X1) -H1X1 -H2X1
  elim (cpm_tdeq_inv_bind_sn … HT … H1X2 H2X2) -H1X2 -H2X2
  #T2 #_ #_ #H1T2 #H2T2 #H21 #T1 #_ #_ #H1T1 #H2T1 #H11 destruct
  @(cnv_cpm_tdeq_conf_lpr_bind_bind_aux … IH1) -IH1 /1 width=1 by/
| #V #T #HG0 #HL0 #HT0 #HT #n1 #X1 #H1X1 #H2X1 #n2 #X2 #H1X2 #H2X2 #L1 #HL1 #L2 #HL2 destruct
  elim (cpm_tdeq_inv_appl_sn … HT … H1X1 H2X1) -H1X1 -H2X1
  elim (cpm_tdeq_inv_appl_sn … HT … H1X2 H2X2) -H1X2 -H2X2
  #m2 #q2 #W2 #U2 #T2 #_ #_ #_ #_ #_ #H1T2 #H2T2 #H21 #m1 #q1 #W1 #U1 #T1 #_ #_ #_ #_ #_ #H1T1 #H2T1 #H11 destruct -m1 -m2 -q1 -q2 -W1 -W2 -U1 -U2
  @(cnv_cpm_tdeq_conf_lpr_appl_appl_aux … IH1) -IH1 /1 width=1 by/
| #V #T #HG0 #HL0 #HT0 #HT #n1 #X1 #H1X1 #H2X1 #n2 #X2 #H1X2 #H2X2 #L1 #HL1 #L2 #HL2 destruct
  elim (cpm_tdeq_inv_cast_sn … HT … H1X1 H2X1) -H1X1 -H2X1
  elim (cpm_tdeq_inv_cast_sn … HT … H1X2 H2X2) -H1X2 -H2X2
  #U2 #V2 #T2 #_ #_ #_ #H1V2 #H2V2 #_ #H1T2 #H2T2 #H21 #U1 #V1 #T1 #_ #_ #_ #H1V1 #H2V1 #_ #H1T1 #H2T1 #H11 destruct -U1 -U2
  @(cnv_cpm_tdeq_conf_lpr_cast_cast_aux … IH1) -IH1 /1 width=1 by/
]
qed-.

lemma cnv_cpm_tdeq_conf_lpr (h) (a) (G0) (L0) (T0):
      IH_cnv_cpm_tdeq_conf_lpr h a G0 L0 T0.
#h #a #G0 #L0 #T0
@(fqup_wf_ind (Ⓣ) … G0 L0 T0) -G0 -L0 -T0 #G0 #L0 #T0 #IH
/3 width=17 by cnv_cpm_tdeq_conf_lpr_aux/
qed-.
