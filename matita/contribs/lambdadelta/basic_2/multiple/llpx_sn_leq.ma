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

include "basic_2/substitution/drop_leq.ma".
include "basic_2/multiple/llpx_sn.ma".

(* LAZY SN POINTWISE EXTENSION OF A CONTEXT-SENSITIVE REALTION FOR TERMS ****)

(* Properties on equivalence for local environments *************************)

lemma leq_llpx_sn_trans: ∀R,L2,L,T,d. llpx_sn R d T L2 L →
                         ∀L1. L1 ⩬[d, ∞] L2 → llpx_sn R d T L1 L.
#R #L2 #L #T #d #H elim H -L2 -L -T -d
/4 width=5 by llpx_sn_flat, llpx_sn_gref, llpx_sn_skip, llpx_sn_sort, leq_fwd_length, trans_eq/  
[ #I #L2 #L #K2 #K #V2 #V #d #i #Hdi #HLK2 #HLK #HK2 #HV2 #_ #L1 #HL12
  elim (leq_drop_trans_be … HL12 … HLK2) -L2 // >yminus_Y_inj #K1 #HK12 #HLK1
  lapply (leq_inv_O_Y … HK12) -HK12 #H destruct /2 width=9 by llpx_sn_lref/
| /4 width=5 by llpx_sn_free, leq_fwd_length, le_repl_sn_trans_aux, trans_eq/
| /4 width=1 by llpx_sn_bind, leq_succ/
]
qed-.

lemma llpx_sn_leq_trans: ∀R,L,L1,T,d. llpx_sn R d T L L1 →
                         ∀L2. L1 ⩬[d, ∞] L2 → llpx_sn R d T L L2.
#R #L #L1 #T #d #H elim H -L -L1 -T -d
/4 width=5 by llpx_sn_flat, llpx_sn_gref, llpx_sn_skip, llpx_sn_sort, leq_fwd_length, trans_eq/  
[ #I #L #L1 #K #K1 #V #V1 #d #i #Hdi #HLK #HLK1 #HK1 #HV1 #_ #L2 #HL12
  elim (leq_drop_conf_be … HL12 … HLK1) -L1 // >yminus_Y_inj #K2 #HK12 #HLK2
  lapply (leq_inv_O_Y … HK12) -HK12 #H destruct /2 width=9 by llpx_sn_lref/
| /4 width=5 by llpx_sn_free, leq_fwd_length, le_repl_sn_conf_aux, trans_eq/
| /4 width=1 by llpx_sn_bind, leq_succ/
]
qed-.

lemma llpx_sn_leq_repl: ∀R,L1,L2,T,d. llpx_sn R d T L1 L2 → ∀K1. K1 ⩬[d, ∞] L1 → 
                        ∀K2. L2 ⩬[d, ∞] K2 → llpx_sn R d T K1 K2.
/3 width=4 by llpx_sn_leq_trans, leq_llpx_sn_trans/ qed-.

lemma llpx_sn_bind_repl_SO: ∀R,I1,I2,L1,L2,V1,V2,T. llpx_sn R 0 T (L1.ⓑ{I1}V1) (L2.ⓑ{I2}V2) →
                            ∀J1,J2,W1,W2. llpx_sn R 1 T (L1.ⓑ{J1}W1) (L2.ⓑ{J2}W2).
#R #I1 #I2 #L1 #L2 #V1 #V2 #T #HT #J1 #J2 #W1 #W2 lapply (llpx_sn_ge R … 1 … HT) -HT
/3 width=7 by llpx_sn_leq_repl, leq_succ/
qed-.
