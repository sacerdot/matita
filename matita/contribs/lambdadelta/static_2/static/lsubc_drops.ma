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

include "static_2/static/aaa_drops.ma".
include "static_2/static/lsubc.ma".

(* LOCAL ENVIRONMENT REFINEMENT FOR GENERIC REDUCIBILITY ********************)

(* Properties with generic slicing ******************************************)

(* Note: the premise ðâ¨fâ© cannot be removed *)
(* Basic_1: includes: csubc_drop_conf_O *)
(* Basic_2A1: includes: lsubc_drop_O1_trans *)
lemma lsubc_drops_trans_isuni: âRP,G,L1,L2. G â¢ L1 â«[RP] L2 â
                               âb,f,K2. ðâ¨fâ© â â©*[b,f] L2 â K2 â
                               ââK1. â©*[b,f] L1 â K1 & G â¢ K1 â«[RP] K2.
#RP #G #L1 #L2 #H elim H -L1 -L2
[ /2 width=3 by ex2_intro/
| #I #L1 #L2 #HL12 #IH #b #f #K2 #Hf #H
  elim (drops_inv_bind1_isuni â¦ Hf H) -Hf -H *
  [ #Hf #H destruct -IH
    /3 width=3 by lsubc_bind, drops_refl, ex2_intro/
  | #g #Hg #HLK2 #H destruct -HL12
    elim (IH â¦ Hg HLK2) -L2 -Hg /3 width=3 by drops_drop, ex2_intro/
  ]
| #L1 #L2 #V #W #A #HV #H1W #H2W #HL12 #IH #b #f #K2 #Hf #H
  elim (drops_inv_bind1_isuni â¦ Hf H) -Hf -H *
  [ #Hf #H destruct -IH
    /3 width=8 by drops_refl, lsubc_beta, ex2_intro/
  | #g #Hg #HLK2 #H destruct -HL12
    elim (IH â¦ Hg HLK2) -L2 -Hg /3 width=3 by drops_drop, ex2_intro/
  ]
]
qed-.

(* Basic_1: was: csubc_drop1_conf_rev *)
(* Basic_1: includes: csubc_drop_conf_rev *)
(* Basic_2A1: includes: drop_lsubc_trans *)
lemma drops_lsubc_trans: âRR,RS,RP. gcp RR RS RP â
                         âb,f,G,L1,K1. â©*[b,f] L1 â K1 â âK2. G â¢ K1 â«[RP] K2 â
                         ââL2. G â¢ L1 â«[RP] L2 & â©*[b,f] L2 â K2.
#RR #RS #RP #HR #b #f #G #L1 #K1 #H elim H -f -L1 -K1
[ #f #Hf #Y #H lapply (lsubc_inv_atom1 â¦ H) -H
  #H destruct /4 width=3 by lsubc_atom, drops_atom, ex2_intro/
| #f #I #L1 #K1 #_ #IH #K2 #HK12 elim (IH â¦ HK12) -K1
  /3 width=5 by lsubc_bind, drops_drop, ex2_intro/
| #f #Z #I #L1 #K1 #HLK1 #HZ #IH #Y #H elim (lsubc_inv_bind1 â¦ H) -H *
  [ #K2 #HK12 #H destruct -HLK1
    elim (IH â¦ HK12) -K1 /3 width=5 by lsubc_bind, drops_skip, ex2_intro/
  | #K2 #V2 #W2 #A #HV2 #H1W2 #H2W2 #HK12 #H1 #H2 destruct
    elim (liftsb_inv_pair_sn â¦ HZ) -HZ #V1 #HV21 #H destruct
    elim (lifts_inv_flat1 â¦ HV21) -HV21 #W3 #V3 #HW23 #HV3 #H destruct
    elim (IH â¦ HK12) -IH -HK12 #K #HL1K #HK2
    lapply (acr_lifts â¦ HR â¦ HV2 â¦ HLK1 â¦ HV3) -HV2
    lapply (acr_lifts â¦ HR â¦ H1W2 â¦ HLK1 â¦ HW23) -H1W2
    /4 width=10 by lsubc_beta, aaa_lifts, drops_skip, ext2_pair, ex2_intro/
  ]
]
qed-.
