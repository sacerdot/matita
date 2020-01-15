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

include "basic_2/rt_computation/rsx_csx.ma".
include "basic_2/rt_computation/fpbs_cpx.ma".
include "basic_2/rt_computation/fpbs_csx.ma".
include "basic_2/rt_computation/fsb_fpbg.ma".

(* STRONGLY NORMALIZING CLOSURES FOR PARALLEL RST-TRANSITION ****************)

(* Inversion lemmas with context-sensitive stringly rt-normalizing terms ****)

lemma fsb_inv_csx (h):
      ∀G,L,T. ≥𝐒[h] ❪G,L,T❫ → ❪G,L❫ ⊢ ⬈*𝐒[h] T.
#h #G #L #T #H @(fsb_ind_alt … H) -G -L -T /5 width=1 by csx_intro, fpb_cpx/
qed-.

(* Propreties with context-sensitive stringly rt-normalizing terms **********)

lemma csx_fsb_fpbs (h):
      ∀G1,L1,T1. ❪G1,L1❫ ⊢ ⬈*𝐒[h] T1 →
      ∀G2,L2,T2. ❪G1,L1,T1❫ ≥[h] ❪G2,L2,T2❫ → ≥𝐒[h] ❪G2,L2,T2❫.
#h #G1 #L1 #T1 #H @(csx_ind … H) -T1
#T1 #HT1 #IHc #G2 #L2 #T2 @(fqup_wf_ind (Ⓣ) … G2 L2 T2) -G2 -L2 -T2
#G0 #L0 #T0 #IHu #H10
lapply (fpbs_csx_conf … H10) // -HT1 #HT0
generalize in match IHu; -IHu generalize in match H10; -H10
@(rsx_ind … (csx_rsx … HT0)) -L0
#L0 #_ #IHd #H10 #IHu @fsb_intro
#G2 #L2 #T2 * -G2 -L2 -T2 [ -IHd -IHc | -IHu -IHd |  ]
[ /4 width=5 by fpbs_fqup_trans, fqu_fqup/
| #T2 #HT02 #HnT02
  elim (fpbs_cpx_tneqx_trans … H10 … HT02 HnT02) -T0
  /3 width=4 by/
| #L2 #HL02 #HnL02 @(IHd … HL02 HnL02) -IHd -HnL02 [ -IHu -IHc | ]
  [ /3 width=3 by fpbs_lpxs_trans, lpx_lpxs/
  | #G3 #L3 #T3 #H03 #_
    elim (lpx_fqup_trans … H03 … HL02) -L2 #L4 #T4 #HT04 #H43 #HL43
    elim (teqx_dec T0 T4) [ -IHc -HT04 #HT04 | -IHu #HnT04 ]
    [ elim (teqx_fqup_trans … H43 … HT04) -T4 #L2 #T4 #H04 #HT43 #HL24
      /4 width=7 by fsb_fpbs_trans, teqx_reqx_lpx_fpbs, fpbs_fqup_trans/
    | elim (cpxs_tneqx_fwd_step_sn … HT04 HnT04) -HT04 -HnT04 #T2 #T5 #HT02 #HnT02 #HT25 #HT54
      elim (fpbs_cpx_tneqx_trans … H10 … HT02 HnT02) -T0 #T0 #HT10 #HnT10 #H02
      /3 width=14 by fpbs_cpxs_teqx_fqup_lpx_trans/
    ]
  ]
]
qed.

lemma csx_fsb (h):
      ∀G,L,T. ❪G,L❫ ⊢ ⬈*𝐒[h] T → ≥𝐒[h] ❪G,L,T❫.
/2 width=5 by csx_fsb_fpbs/ qed.

(* Advanced eliminators *****************************************************)

lemma csx_ind_fpb (h) (Q:relation3 …):
      (∀G1,L1,T1.
        ❪G1,L1❫ ⊢ ⬈*𝐒[h] T1 →
        (∀G2,L2,T2. ❪G1,L1,T1❫ ≻[h] ❪G2,L2,T2❫ → Q G2 L2 T2) →
        Q G1 L1 T1
      ) →
      ∀G,L,T. ❪G,L❫ ⊢ ⬈*𝐒[h] T → Q G L T.
/4 width=4 by fsb_inv_csx, csx_fsb, fsb_ind_alt/ qed-.

lemma csx_ind_fpbg (h) (Q:relation3 …):
      (∀G1,L1,T1.
        ❪G1,L1❫ ⊢ ⬈*𝐒[h] T1 →
        (∀G2,L2,T2. ❪G1,L1,T1❫ >[h] ❪G2,L2,T2❫ → Q G2 L2 T2) →
        Q G1 L1 T1
      ) →
      ∀G,L,T. ❪G,L❫ ⊢ ⬈*𝐒[h] T → Q G L T.
/4 width=4 by fsb_inv_csx, csx_fsb, fsb_ind_fpbg/ qed-.
