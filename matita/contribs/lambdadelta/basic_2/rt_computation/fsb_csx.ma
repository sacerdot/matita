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

include "basic_2/rt_transition/fpbc_fqup.ma".
include "basic_2/rt_transition/fpbc_lpx.ma".
include "basic_2/rt_computation/rsx_csx.ma".
include "basic_2/rt_computation/fpbs_cpx.ma".
include "basic_2/rt_computation/fpbs_csx.ma".
include "basic_2/rt_computation/fsb_fpbg.ma".

(* STRONGLY NORMALIZING CLOSURES FOR PARALLEL RST-TRANSITION ****************)

(* Inversion lemmas with context-sensitive stringly rt-normalizing terms ****)

lemma fsb_inv_csx:
      ∀G,L,T. ≥𝐒 ❪G,L,T❫ → ❪G,L❫ ⊢ ⬈*𝐒 T.
#G #L #T #H @(fsb_ind_alt … H) -G -L -T
/5 width=1 by csx_intro, cpx_fpbc/
qed-.

(* Propreties with context-sensitive stringly rt-normalizing terms **********)

lemma csx_fsb_fpbs:
      ∀G1,L1,T1. ❪G1,L1❫ ⊢ ⬈*𝐒 T1 →
      ∀G2,L2,T2. ❪G1,L1,T1❫ ≥ ❪G2,L2,T2❫ → ≥𝐒 ❪G2,L2,T2❫.
#G1 #L1 #T1 #H @(csx_ind … H) -T1
#T1 #HT1 #IHc #G2 #L2 #T2 @(fqup_wf_ind (Ⓣ) … G2 L2 T2) -G2 -L2 -T2
#G0 #L0 #T0 #IHu #H10
lapply (fpbs_csx_conf … H10) // -HT1 #HT0
generalize in match IHu; -IHu generalize in match H10; -H10
@(rsx_ind … (csx_rsx … HT0)) -L0 #L0 #_ #IHd #H10 #IHu
@fsb_intro #G2 #L2 #T2 #H
elim (fpbc_fwd_lpx … H) -H * [ -IHd -IHc | -IHu -IHd |]
[ /5 width=5 by fsb_fpb_trans, fpbs_fqup_trans, fqu_fqup/
| #T3 #HT03 #HnT03 #H32
  elim (fpbs_cpx_tneqg_trans … H10 … HT03 HnT03) -T0
  /4 width=5 by fsb_fpb_trans, sfull_dec/
| #L3 #HL03 #HnL03 #HL32
  @(fsb_fpb_trans … HL32) -L2
  @(IHd … HL03 HnL03) -IHd -HnL03 [ -IHu -IHc |]
  [ /3 width=3 by fpbs_lpxs_trans, lpx_lpxs/
  | #G4 #L4 #T4 #H04 #_
    elim (lpx_fqup_trans … H04 … HL03) -L3 #L3 #T3 #HT03 #H34 #HL34
    elim (teqx_dec T0 T3) [ -IHc -HT03 #HT03 | -IHu #HnT03 ]
    [ elim (teqg_fqup_trans … H34 … HT03) -T3 // #L2 #T3 #H03 #HT34 #HL23
      /4 width=10 by fsb_fpbs_trans, teqg_reqg_lpx_fpbs, fpbs_fqup_trans/
    | elim (cpxs_tneqg_fwd_step_sn … HT03 HnT03) -HT03 -HnT03 /2 width=1 by sfull_dec/ #T2 #HT02 #HnT02 #HT23
      elim (fpbs_cpx_tneqg_trans … H10 … HT02 HnT02) -T0 /2 width=1 by sfull_dec/ #T0 #HT10 #HnT10 #H02
      /3 width=17 by fpbs_cpxs_teqg_fqup_lpx_trans/
    ]
  ]
]
qed.

lemma csx_fsb (G) (L) (T):
      ❪G,L❫ ⊢ ⬈*𝐒 T → ≥𝐒 ❪G,L,T❫.
/2 width=5 by csx_fsb_fpbs/ qed.

(* Advanced eliminators *****************************************************)

lemma csx_ind_fpbc (Q:relation3 …):
      (∀G1,L1,T1.
        ❪G1,L1❫ ⊢ ⬈*𝐒 T1 →
        (∀G2,L2,T2. ❪G1,L1,T1❫ ≻ ❪G2,L2,T2❫ → Q G2 L2 T2) →
        Q G1 L1 T1
      ) →
      ∀G,L,T. ❪G,L❫ ⊢ ⬈*𝐒 T → Q G L T.
/4 width=4 by fsb_inv_csx, csx_fsb, fsb_ind_alt/ qed-.

lemma csx_ind_fpbg (Q:relation3 …):
      (∀G1,L1,T1.
        ❪G1,L1❫ ⊢ ⬈*𝐒 T1 →
        (∀G2,L2,T2. ❪G1,L1,T1❫ > ❪G2,L2,T2❫ → Q G2 L2 T2) →
        Q G1 L1 T1
      ) →
      ∀G,L,T. ❪G,L❫ ⊢ ⬈*𝐒 T → Q G L T.
/4 width=4 by fsb_inv_csx, csx_fsb, fsb_ind_fpbg/ qed-.
