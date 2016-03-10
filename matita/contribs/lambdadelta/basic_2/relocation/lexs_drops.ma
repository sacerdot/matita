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

include "basic_2/relocation/lexs.ma".
include "basic_2/relocation/drops.ma".

(* GENERAL ENTRYWISE EXTENSION OF A CONTEXT-SENSITIVE REALTION FOR TERMS ****)

(* Basic_2A1: includes: lpx_sn_deliftable_dropable *)
lemma lexs_deliftable_dropable: ∀RN,RP. d_deliftable2_sn RN → d_deliftable2_sn RP →
                                dropable_sn (lexs RN RP).
#RN #RP #HN #HP #L1 #K1 #c #f #H elim H -L1 -K1 -f
[ #f #Hf #X #f2 #H #f1 #Hf2 >(lexs_inv_atom1 … H) -X
  /4 width=3 by lexs_atom, drops_atom, ex2_intro/
| #I #L1 #K1 #V1 #f #_ #IH #X #f2 #H #f1 #Hf2 elim (after_inv_nxx … Hf2) -Hf2 [2,3: // ]
  #g2 #Hg2 #H2 destruct elim (lexs_inv_next1 … H) -H
  #L2 #V2 #HL12 #HV12 #H destruct elim (IH … HL12 … Hg2) -g2
  /3 width=3 by drops_drop, ex2_intro/
| #I #L1 #K1 #V1 #W1 #f #HLK #HWV #IH #X #f2 #H #f1 #Hf2 elim (after_inv_pxx … Hf2) -Hf2 [1,3:* |*: // ]
  #g1 #g2 #Hg2 #H1 #H2 destruct
  [ elim (lexs_inv_push1 … H) | elim (lexs_inv_next1 … H) ] -H
  #L2 #V2 #HL12 #HV12 #H destruct elim (IH … HL12 … Hg2) -g2
  [ elim (HP … HV12 … HLK … HWV) | elim (HN … HV12 … HLK … HWV) ] -V1
  /3 width=5 by lexs_next, lexs_push, drops_skip, ex2_intro/
]
qed-.
(*
lemma lpx_sn_liftable_dedropable: ∀R. (∀L. reflexive ? (R L)) →
                                  d_liftable2 R → dedropable_sn (lpx_sn R).
#R #H1R #H2R #L1 #K1 #s #l #m #H elim H -L1 -K1 -l -m
[ #l #m #Hm #X #H >(lpx_sn_inv_atom1 … H) -H
  /4 width=4 by drop_atom, lpx_sn_atom, ex3_intro/
| #I #K1 #V1 #X #H elim (lpx_sn_inv_pair1 … H) -H
  #K2 #V2 #HK12 #HV12 #H destruct
  lapply (lpx_sn_fwd_length … HK12)
  #H @(ex3_intro … (K2.ⓑ{I}V2)) (**) (* explicit constructor *)
  /3 width=1 by lpx_sn_pair, lreq_O2/
| #I #L1 #K1 #V1 #m #_ #IHLK1 #K2 #HK12 elim (IHLK1 … HK12) -K1
  /3 width=5 by drop_drop, lreq_pair, lpx_sn_pair, ex3_intro/
| #I #L1 #K1 #V1 #W1 #l #m #HLK1 #HWV1 #IHLK1 #X #H
  elim (lpx_sn_inv_pair1 … H) -H #K2 #W2 #HK12 #HW12 #H destruct
  elim (H2R … HW12 … HLK1 … HWV1) -W1
  elim (IHLK1 … HK12) -K1
  /3 width=6 by drop_skip, lreq_succ, lpx_sn_pair, ex3_intro/
]
qed-.
*)
include "ground_2/relocation/trace_isun.ma".

lemma lpx_sn_dropable: ∀R,L2,K2,c,t. ⬇*[c, t] L2 ≡ K2 → 𝐔⦃t⦄ →
                       ∀L1,u2. lpx_sn R u2 L1 L2 → ∀u1. t ⊚ u1 ≡ u2 →
                       ∃∃K1. ⬇*[c, t] L1 ≡ K1 & lpx_sn R u1 K1 K2.
#R #L2 #K2 #c #t #H elim H -L2 -K2 -t
[ #t #Ht #_ #X #u2 #H #u1 #Hu elim (lpx_sn_inv_atom2 … H) -H
  #H1 #H2 destruct elim (after_inv_empty3 … Hu) -Hu
  /4 width=3 by drops_atom, lpx_sn_atom, ex2_intro/
| #I #L2 #K2 #V2 #t #_ #IH #Ht #X #u2 #H #u1 #Hu elim (lpx_sn_inv_pair2 … H) -H
  #L1 #V1 #y2 #x #HL #HV #H1 #H2 destruct elim (after_inv_false1 … Hu) -Hu
  #u #H #Hu destruct elim (IH … HL … Hu) -L2 /3 width=3 by drops_drop, isun_inv_false, ex2_intro/
| #I #L2 #K2 #V2 #W2 #t #_ #HWV #IHLK #Ht #X #u2 #H #u1 #Hu elim (lpx_sn_inv_pair2 … H) -H
  #L1 #V1 #y2 #x #HL #HV #H1 #H2 destruct elim (after_inv_true1 … Hu) -Hu
  #y1 #y #x2 #H1 #H2 #Hu destruct lapply (isun_inv_true … Ht) -Ht
  #Ht elim (IHLK … HL … Hu) -L2 -Hu /2 width=1 by isun_id/
  #K1 #HLK1 #HK12 lapply (lifts_fwd_isid … HWV ?) // -HWV
  #H destruct lapply (drops_fwd_isid … HLK1 ?) //
  #H destruct
  @ex2_intro
  [ 
  | @(drops_skip … HLK1)
  | @(lpx_sn_pair … HK12 … HV) 
  

   lapply (drops_fwd_isid … HLK1 ?) // -HLK1
  2: 
  
  
  
  
   elim (HR … HV … HLK … HWV) -V1
  elim (IHLK … HL … Hu) -L1 /3 width=5 by drops_skip, lpx_sn_pair, ex2_intro/


]
qed-.
