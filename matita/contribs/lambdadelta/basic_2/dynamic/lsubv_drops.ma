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

include "static_2/relocation/drops.ma".
include "basic_2/dynamic/lsubv.ma".

(* LOCAL ENVIRONMENT REFINEMENT FOR NATIVE VALIDITY *************************)

(* Properties with generic slicing for local environments *******************)

(* Note: the premise đâšfâ© cannot be removed *)
(* Basic_2A1: includes: lsubsv_drop_O1_conf *)
lemma lsubv_drops_conf_isuni (h) (a) (G):
      âL1,L2. G âą L1 â«![h,a] L2 â
      âb,f,K1. đâšfâ© â â©*[b,f] L1 â K1 â
      ââK2. G âą K1 â«![h,a] K2 & â©*[b,f] L2 â K2.
#h #a #G #L1 #L2 #H elim H -L1 -L2
[ /2 width=3 by ex2_intro/
| #I #L1 #L2 #HL12 #IH #b #f #K1 #Hf #H
  elim (drops_inv_bind1_isuni âŠ Hf H) -Hf -H *
  [ #Hf #H destruct -IH
    /3 width=3 by lsubv_bind, drops_refl, ex2_intro/
  | #g #Hg #HLK1 #H destruct -HL12
    elim (IH âŠ Hg HLK1) -L1 -Hg /3 width=3 by drops_drop, ex2_intro/
  ]
| #L1 #L2 #W #V #HVW #HL12 #IH #b #f #K1 #Hf #H
  elim (drops_inv_bind1_isuni âŠ Hf H) -Hf -H *
  [ #Hf #H destruct -IH
    /3 width=3 by drops_refl, lsubv_beta, ex2_intro/
  | #g #Hg #HLK1 #H destruct -HL12
    elim (IH âŠ Hg HLK1) -L1 -Hg /3 width=3 by drops_drop, ex2_intro/
  ]
]
qed-.

(* Note: the premise đâšfâ© cannot be removed *)
(* Basic_2A1: includes: lsubsv_drop_O1_trans *)
lemma lsubv_drops_trans_isuni (h) (a) (G):
      âL1,L2. G âą L1 â«![h,a] L2 â
      âb,f,K2. đâšfâ© â â©*[b,f] L2 â K2 â
      ââK1. G âą K1 â«![h,a] K2 & â©*[b,f] L1 â K1.
#h #a #G #L1 #L2 #H elim H -L1 -L2
[ /2 width=3 by ex2_intro/
| #I #L1 #L2 #HL12 #IH #b #f #K2 #Hf #H
  elim (drops_inv_bind1_isuni âŠ Hf H) -Hf -H *
  [ #Hf #H destruct -IH
    /3 width=3 by lsubv_bind, drops_refl, ex2_intro/
  | #g #Hg #HLK2 #H destruct -HL12
    elim (IH âŠ Hg HLK2) -L2 -Hg /3 width=3 by drops_drop, ex2_intro/
  ]
| #L1 #L2 #W #V #HWV #HL12 #IH #b #f #K2 #Hf #H
  elim (drops_inv_bind1_isuni âŠ Hf H) -Hf -H *
  [ #Hf #H destruct -IH
    /3 width=3 by drops_refl, lsubv_beta, ex2_intro/
  | #g #Hg #HLK2 #H destruct -HL12
    elim (IH âŠ Hg HLK2) -L2 -Hg /3 width=3 by drops_drop, ex2_intro/
  ]
]
qed-.
