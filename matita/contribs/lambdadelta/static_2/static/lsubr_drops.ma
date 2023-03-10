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
include "static_2/static/lsubr.ma".

(* RESTRICTED REFINEMENT FOR LOCAL ENVIRONMENTS *****************************)

(* Forward lemmas with generic slicing for local environments ***************)

(* Basic_2A1: includes: lsubr_fwd_drop2_pair *)
lemma lsubr_fwd_drops2_bind:
      âL1,L2. L1 âŤ L2 â
      âb,f,I,K2. đâ¨fâŠ â âŠ*[b,f] L2 â K2.â[I] â
      â¨â¨ ââK1. K1 âŤ K2 & âŠ*[b,f] L1 â K1.â[I]
       | ââK1,W,V. K1 âŤ K2 & âŠ*[b,f] L1 â K1.ââW.V & I = BPair Abst W
       | ââJ1,J2,K1,V. K1 âŤ K2 & âŠ*[b,f] L1 â K1.â[J1]V & I = BUnit J2.
#L1 #L2 #H elim H -L1 -L2
[ #b #f #I #K2 #_ #H
  elim (drops_inv_atom1 âŚ H) -H #H destruct
| #J #L1 #L2 | #L1 #L2 #V #W | #I1 #I2 #L1 #L2 #V1
]
#HL12 #IH #b #f #I #K2 #Hf #H
elim (drops_inv_bind1_isuni âŚ Hf H) -Hf -H *
[1,3,5: #Hf #H destruct -IH
  /4 width=6 by drops_refl, or3_intro0, or3_intro1, or3_intro2, ex3_4_intro, ex3_3_intro, ex2_intro/
|2,4,6: #g #Hg #HLK2 #H destruct -HL12
  elim (IH âŚ Hg HLK2) -IH -Hg -HLK2 *
  /4 width=6 by drops_drop, or3_intro0, or3_intro1, or3_intro2, ex3_4_intro, ex3_3_intro, ex2_intro/
]
qed-.

(* Basic_2A1: includes: lsubr_fwd_drop2_abbr *)
lemma lsubr_fwd_drops2_abbr:
      âL1,L2. L1 âŤ L2 â
      âb,f,K2,V. đâ¨fâŠ â âŠ*[b,f] L2 â K2.âV â
      ââK1. K1 âŤ K2 & âŠ*[b,f] L1 â K1.âV.
#L1 #L2 #HL12 #b #f #K2 #V #Hf #HLK2
elim (lsubr_fwd_drops2_bind âŚ HL12 âŚ Hf HLK2) -L2 -Hf // *
[ #K1 #W #V #_ #_ #H destruct
| #I1 #I2 #K1 #V #_ #_ #H destruct
]
qed-.
