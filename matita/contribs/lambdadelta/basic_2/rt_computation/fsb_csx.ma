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
      âG,L,T. â¥ğ â¨G,L,Tâ© â â¨G,Lâ© â¢ â¬*ğ T.
#G #L #T #H @(fsb_ind â¦ H) -G -L -T
/5 width=1 by csx_intro, cpx_fpbc/
qed-.

(* Propreties with context-sensitive stringly rt-normalizing terms **********)

lemma csx_fsb_fpbs:
      âG1,L1,T1. â¨G1,L1â© â¢ â¬*ğ T1 â
      âG2,L2,T2. â¨G1,L1,T1â© â¥ â¨G2,L2,T2â© â â¥ğ â¨G2,L2,T2â©.
#G1 #L1 #T1 #H @(csx_ind â¦ H) -T1
#T1 #HT1 #IHc #G2 #L2 #T2 @(fqup_wf_ind (â) â¦ G2 L2 T2) -G2 -L2 -T2
#G0 #L0 #T0 #IHu #H10
lapply (fpbs_csx_conf â¦ H10) // -HT1 #HT0
generalize in match IHu; -IHu generalize in match H10; -H10
@(rsx_ind â¦ (csx_rsx â¦ HT0)) -L0 #L0 #_ #IHd #H10 #IHu
@fsb_intro #G2 #L2 #T2 #H
elim (fpbc_fwd_lpx â¦ H) -H * [ -IHd -IHc | -IHu -IHd |]
[ /5 width=5 by fsb_fpb_trans, fpbs_fqup_trans, fqu_fqup/
| #T3 #HT03 #HnT03 #H32
  elim (fpbs_cpx_tneqg_trans â¦ H10 â¦ HT03 HnT03) -T0
  /4 width=5 by fsb_fpb_trans, sfull_dec/
| #L3 #HL03 #HnL03 #HL32
  @(fsb_fpb_trans â¦ HL32) -L2
  @(IHd â¦ HL03 HnL03) -IHd -HnL03 [ -IHu -IHc |]
  [ /3 width=3 by fpbs_lpxs_trans, lpx_lpxs/
  | #G4 #L4 #T4 #H04 #_
    elim (lpx_fqup_trans â¦ H04 â¦ HL03) -L3 #L3 #T3 #HT03 #H34 #HL34
    elim (teqx_dec T0 T3) [ -IHc -HT03 #HT03 | -IHu #HnT03 ]
    [ elim (teqg_fqup_trans â¦ H34 â¦ HT03) -T3 // #L2 #T3 #H03 #HT34 #HL23
      /4 width=10 by fsb_fpbs_trans, teqg_reqg_lpx_fpbs, fpbs_fqup_trans/
    | elim (cpxs_tneqg_fwd_step_sn â¦ HT03 HnT03) -HT03 -HnT03 /2 width=1 by sfull_dec/ #T2 #HT02 #HnT02 #HT23
      elim (fpbs_cpx_tneqg_trans â¦ H10 â¦ HT02 HnT02) -T0 /2 width=1 by sfull_dec/ #T0 #HT10 #HnT10 #H02
      /3 width=17 by fpbs_cpxs_teqg_fqup_lpx_trans/
    ]
  ]
]
qed.

lemma csx_fsb (G) (L) (T):
      â¨G,Lâ© â¢ â¬*ğ T â â¥ğ â¨G,L,Tâ©.
/2 width=5 by csx_fsb_fpbs/ qed.

(* Advanced eliminators *****************************************************)

lemma csx_ind_fpbc (Q:relation3 â¦):
      (âG1,L1,T1.
        â¨G1,L1â© â¢ â¬*ğ T1 â
        (âG2,L2,T2. â¨G1,L1,T1â© â» â¨G2,L2,T2â© â Q G2 L2 T2) â
        Q G1 L1 T1
      ) â
      âG,L,T. â¨G,Lâ© â¢ â¬*ğ T â Q G L T.
/4 width=4 by fsb_inv_csx, csx_fsb, fsb_ind/ qed-.

lemma csx_ind_fpbg (Q:relation3 â¦):
      (âG1,L1,T1.
        â¨G1,L1â© â¢ â¬*ğ T1 â
        (âG2,L2,T2. â¨G1,L1,T1â© > â¨G2,L2,T2â© â Q G2 L2 T2) â
        Q G1 L1 T1
      ) â
      âG,L,T. â¨G,Lâ© â¢ â¬*ğ T â Q G L T.
/4 width=4 by fsb_inv_csx, csx_fsb, fsb_ind_fpbg/ qed-.
