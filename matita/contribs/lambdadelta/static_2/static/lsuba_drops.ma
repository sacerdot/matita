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
include "static_2/static/lsuba.ma".

(* RESTRICTED REFINEMENT FOR ATOMIC ARITY ASSIGNMENT ************************)

(* Properties with generic slicing for local environments *******************)

(* Note: the premise đâ¨fâŠ cannot be removed *)
(* Basic_2A1: includes: lsuba_drop_O1_conf *)
lemma lsuba_drops_conf_isuni: âG,L1,L2. G â˘ L1 âŤâ L2 â
                              âb,f,K1. đâ¨fâŠ â âŠ*[b,f] L1 â K1 â
                              ââK2. G â˘ K1 âŤâ K2 & âŠ*[b,f] L2 â K2.
#G #L1 #L2 #H elim H -L1 -L2
[ /2 width=3 by ex2_intro/
| #I #L1 #L2 #HL12 #IH #b #f #K1 #Hf #H
  elim (drops_inv_bind1_isuni âŚ Hf H) -Hf -H *
  [ #Hf #H destruct -IH
    /3 width=3 by lsuba_bind, drops_refl, ex2_intro/
  | #g #Hg #HLK1 #H destruct -HL12
    elim (IH âŚ Hg HLK1) -L1 -Hg /3 width=3 by drops_drop, ex2_intro/
  ]
| #L1 #L2 #W #V #A #HV #HW #HL12 #IH #b #f #K1 #Hf #H
  elim (drops_inv_bind1_isuni âŚ Hf H) -Hf -H *
  [ #Hf #H destruct -IH
    /3 width=3 by drops_refl, lsuba_beta, ex2_intro/
  | #g #Hg #HLK1 #H destruct -HL12
    elim (IH âŚ Hg HLK1) -L1 -Hg /3 width=3 by drops_drop, ex2_intro/
  ]
]
qed-.

(* Note: the premise đâ¨fâŠ cannot be removed *)
(* Basic_2A1: includes: lsuba_drop_O1_trans *)
lemma lsuba_drops_trans_isuni: âG,L1,L2. G â˘ L1 âŤâ L2 â
                               âb,f,K2. đâ¨fâŠ â âŠ*[b,f] L2 â K2 â
                               ââK1. G â˘ K1 âŤâ K2 & âŠ*[b,f] L1 â K1.
#G #L1 #L2 #H elim H -L1 -L2
[ /2 width=3 by ex2_intro/
| #I #L1 #L2 #HL12 #IH #b #f #K2 #Hf #H
  elim (drops_inv_bind1_isuni âŚ Hf H) -Hf -H *
  [ #Hf #H destruct -IH
    /3 width=3 by lsuba_bind, drops_refl, ex2_intro/
  | #g #Hg #HLK2 #H destruct -HL12
    elim (IH âŚ Hg HLK2) -L2 -Hg /3 width=3 by drops_drop, ex2_intro/
  ]
| #L1 #L2 #W #V #A #HV #HW #HL12 #IH #b #f #K2 #Hf #H
  elim (drops_inv_bind1_isuni âŚ Hf H) -Hf -H *
  [ #Hf #H destruct -IH
    /3 width=3 by drops_refl, lsuba_beta, ex2_intro/
  | #g #Hg #HLK2 #H destruct -HL12
    elim (IH âŚ Hg HLK2) -L2 -Hg /3 width=3 by drops_drop, ex2_intro/
  ]
]
qed-.
