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
theorem drops_conf: ∀L1,L,s1,t1. ⬇*[s1, t1] L1 ≡ L →
                    ∀L2,s2,t. ⬇*[s2, t] L1 ≡ L2 →
                    ∀t2. t1 ⊚ t2 ≡ t → ⬇*[s2, t2] L ≡ L2.
#L1 #L #s1 #t1 #H elim H -L1 -L -t1
[ #t1 #_ #L2 #s2 #t #H #t2 #Ht12 elim (drops_inv_atom1 … H) -s1 -H
  #H #Ht destruct @drops_atom
  #H elim (after_inv_isid3 … Ht12) -Ht12 /2 width=1 by/
| #I #K1 #K #V1 #t1 #_ #IH #L2 #s2 #t #H12 #t2 #Ht elim (after_inv_false1 … Ht) -Ht
  #u #H #Hu destruct /3 width=3 by drops_inv_drop1/
| #I #K1 #K #V1 #V #t1 #_ #HV1 #IH #L2 #s2 #t #H #t2 #Ht elim (after_inv_true1 … Ht) -Ht
  #u2 #u * #H1 #H2 #Hu destruct
  [ elim (drops_inv_skip1 … H) -H /3 width=6 by drops_skip, lifts_div/
  | /4 width=3 by drops_inv_drop1, drops_drop/
  ]
]
qed-.

(* Basic_1: was: drop1_trans *)
(* Basic_2A1: includes: drop_trans_ge drop_trans_le drop_trans_ge_comm 
                        drops_drop_trans
*)
theorem drops_trans: ∀L1,L,s1,t1. ⬇*[s1, t1] L1 ≡ L →
                     ∀L2,s2,t2. ⬇*[s2, t2] L ≡ L2 →
                     ∀t. t1 ⊚ t2 ≡ t → ⬇*[s1∨s2, t] L1 ≡ L2.
#L1 #L #s1 #t1 #H elim H -L1 -L -t1
[ #t1 #Ht1 #L2 #s2 #t2 #H #t #Ht elim (drops_inv_atom1 … H) -H
  #H #Ht2 destruct @drops_atom #H elim (orb_false_r … H) -H
  #H1 #H2 >(after_isid_inv_sn … Ht) -Ht /2 width=1 by/
| #I #K1 #K #V1 #t1 #_ #IH #L #s2 #t2 #HKL #t #Ht elim (after_inv_false1 … Ht) -Ht
  /3 width=3 by drops_drop/
| #I #K1 #K #V1 #V #t1 #_ #HV1 #IH #L #s2 #t2 #H #t #Ht elim (after_inv_true1 … Ht) -Ht
  #u2 #u * #H1 #H2 #Hu destruct
  [ elim (drops_inv_skip1 … H) -H /3 width=6 by drops_skip, lifts_trans/
  | /4 width=3 by drops_inv_drop1, drops_drop/
  ]
]
qed-.

(* Advanced properties ******************************************************)

(* Basic_2A1: includes: drop_mono *)
lemma drops_mono: ∀L,L1,s1,t. ⬇*[s1, t] L ≡ L1 →
                  ∀L2,s2. ⬇*[s2, t] L ≡ L2 → L1 = L2.
#L #L1 #s1 #t elim (isid_after_dx t)
/3 width=8 by drops_conf, drops_fwd_isid/
qed-.

(* Basic_2A1: includes: drop_conf_lt *)
lemma drops_conf_skip1: ∀L,L2,s2,t. ⬇*[s2, t] L ≡ L2 →
                        ∀I,K1,V1,s1,t1. ⬇*[s1, t1] L ≡ K1.ⓑ{I}V1 →
                        ∀t2. t1 ⊚ Ⓣ@t2 ≡ t →
                        ∃∃K2,V2. L2 = K2.ⓑ{I}V2 &
                                 ⬇*[s2, t2] K1 ≡ K2 & ⬆*[t2] V2 ≡ V1.
#L #L2 #s2 #t #H2 #I #K1 #V1 #s1 #t1 #H1 #t2 #Ht lapply (drops_conf … H1 … H2 … Ht) -L -Ht
#H elim (drops_inv_skip1 … H) -H /2 width=5 by ex3_2_intro/
qed-.

(* Basic_2A1: includes: drop_trans_lt *)
lemma drops_trans_skip2: ∀L1,L,s1,t1. ⬇*[s1, t1] L1 ≡ L →
                         ∀I,K2,V2,s2,t2. ⬇*[s2, t2] L ≡ K2.ⓑ{I}V2 →
                         ∀t. t1 ⊚ t2 ≡ Ⓣ@t →
                         ∃∃K1,V1. L1 = K1.ⓑ{I}V1 &
                                  ⬇*[s1∨s2, t] K1 ≡ K2 & ⬆*[t] V2 ≡ V1.
#L1 #L #s1 #t1 #H1 #I #K2 #V2 #s2 #t2 #H2 #t #Ht
lapply (drops_trans … H1 … H2 … Ht) -L -Ht
#H elim (drops_inv_skip2 … H) -H /2 width=5 by ex3_2_intro/
qed-.
