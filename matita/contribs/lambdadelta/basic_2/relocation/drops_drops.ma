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

include "basic_2/relocation/lifts_lifts.ma".
include "basic_2/relocation/drops.ma".

(* GENERAL SLICING FOR LOCAL ENVIRONMENTS ***********************************)

(* Main properties **********************************************************)

(* Basic_2A1: includes: drop_conf_ge drop_conf_be drop_conf_le *)
theorem drops_conf: ∀L1,L,c1,f1. ⬇*[c1, f1] L1 ≡ L →
                    ∀L2,c2,f. ⬇*[c2, f] L1 ≡ L2 →
                    ∀f2. f1 ⊚ f2 ≡ f → ⬇*[c2, f2] L ≡ L2.
#L1 #L #c1 #f1 #H elim H -L1 -L -f1
[ #f1 #_ #L2 #c2 #f #HL2 #f2 #Hf12 elim (drops_inv_atom1 … HL2) -c1 -HL2
  #H #Hf destruct @drops_atom
  #H elim (after_inv_isid3 … Hf12) -Hf12 /2 width=1 by/
| #I #K1 #K #V1 #f1 #_ #IH #L2 #c2 #f #HL2 #f2 #Hf elim (after_inv_nxx … Hf) -Hf [2,3: // ]
  #g #Hg #H destruct /3 width=3 by drops_inv_drop1/
| #I #K1 #K #V1 #V #f1 #_ #HV1 #IH #L2 #c2 #f #HL2 #f2 #Hf elim (after_inv_pxx … Hf) -Hf [1,3: * |*:// ]
  #g2 #g #Hf #H1 #H2 destruct
  [ elim (drops_inv_skip1 … HL2) -HL2 /3 width=6 by drops_skip, lifts_div/
  | /4 width=3 by drops_inv_drop1, drops_drop/
  ]
]
qed-.

(* Basic_1: was: drop1_trans *)
(* Basic_2A1: includes: drop_trans_ge drop_trans_le drop_trans_ge_comm 
                        drops_drop_trans
*)
theorem drops_trans: ∀L1,L,c1,f1. ⬇*[c1, f1] L1 ≡ L →
                     ∀L2,c2,f2. ⬇*[c2, f2] L ≡ L2 →
                     ∀f. f1 ⊚ f2 ≡ f → ⬇*[c1∧c2, f] L1 ≡ L2.
#L1 #L #c1 #f1 #H elim H -L1 -L -f1
[ #f1 #Hf1 #L2 #c2 #f2 #HL2 #f #Hf elim (drops_inv_atom1 … HL2) -HL2
  #H #Hf2 destruct @drops_atom #H elim (andb_inv_true_dx … H) -H
  #H1 #H2 lapply (after_isid_inv_sn … Hf ?) -Hf
  /3 width=3 by isid_eq_repl_back/
| #I #K1 #K #V1 #f1 #_ #IH #L2 #c2 #f2 #HL2 #f #Hf elim (after_inv_nxx … Hf) -Hf
  /3 width=3 by drops_drop/
| #I #K1 #K #V1 #V #f1 #_ #HV1 #IH #L2 #c2 #f2 #HL2 #f #Hf elim (after_inv_pxx … Hf) -Hf [1,3: * |*: // ]
  #g2 #g #Hg #H1 #H2 destruct
  [ elim (drops_inv_skip1 … HL2) -HL2 /3 width=6 by drops_skip, lifts_trans/
  | /4 width=3 by drops_inv_drop1, drops_drop/
  ]
]
qed-.

(* Advanced properties ******************************************************)

(* Basic_2A1: includes: drop_mono *)
lemma drops_mono: ∀L,L1,c1,f. ⬇*[c1, f] L ≡ L1 →
                  ∀L2,c2. ⬇*[c2, f] L ≡ L2 → L1 = L2.
#L #L1 #c1 #f lapply (isid_after_dx 𝐈𝐝 … f)
/3 width=8 by drops_conf, drops_fwd_isid/
qed-.

(* Basic_2A1: includes: drop_conf_lt *)
lemma drops_conf_skip1: ∀L,L2,c2,f. ⬇*[c2, f] L ≡ L2 →
                        ∀I,K1,V1,c1,f1. ⬇*[c1, f1] L ≡ K1.ⓑ{I}V1 →
                        ∀f2. f1 ⊚ ↑f2 ≡ f →
                        ∃∃K2,V2. L2 = K2.ⓑ{I}V2 &
                                 ⬇*[c2, f2] K1 ≡ K2 & ⬆*[f2] V2 ≡ V1.
#L #L2 #c2 #f #H2 #I #K1 #V1 #c1 #f1 #H1 #f2 #Hf lapply (drops_conf … H1 … H2 … Hf) -L -Hf
#H elim (drops_inv_skip1 … H) -H /2 width=5 by ex3_2_intro/
qed-.

(* Basic_2A1: includes: drop_trans_lt *)
lemma drops_trans_skip2: ∀L1,L,c1,f1. ⬇*[c1, f1] L1 ≡ L →
                         ∀I,K2,V2,c2,f2. ⬇*[c2, f2] L ≡ K2.ⓑ{I}V2 →
                         ∀f. f1 ⊚ f2 ≡ ↑f →
                         ∃∃K1,V1. L1 = K1.ⓑ{I}V1 &
                                  ⬇*[c1∧c2, f] K1 ≡ K2 & ⬆*[f] V2 ≡ V1.
#L1 #L #c1 #f1 #H1 #I #K2 #V2 #c2 #f2 #H2 #f #Hf
lapply (drops_trans … H1 … H2 … Hf) -L -Hf
#H elim (drops_inv_skip2 … H) -H /2 width=5 by ex3_2_intro/
qed-.
