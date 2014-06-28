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

include "basic_2/substitution/lpx_sn_drop.ma".
include "basic_2/multiple/llpx_sn.ma".

(* LAZY SN POINTWISE EXTENSION OF A CONTEXT-SENSITIVE REALTION FOR TERMS ****)

(* Properties on pointwise extensions ***************************************)

lemma lpx_sn_llpx_sn: ∀R. (∀L. reflexive … (R L)) →
                      ∀T,L1,L2,d. lpx_sn R L1 L2 → llpx_sn R d T L1 L2.
#R #HR #T #L1 @(f2_ind … rfw … L1 T) -L1 -T
#n #IH #L1 * *
[ -HR -IH /4 width=2 by lpx_sn_fwd_length, llpx_sn_sort/
| -HR #i elim (lt_or_ge i (|L1|))
  [2: -IH /4 width=4 by lpx_sn_fwd_length, llpx_sn_free, le_repl_sn_conf_aux/ ]
  #Hi #Hn #L2 #d elim (ylt_split i d) 
  [ -n /3 width=2 by llpx_sn_skip, lpx_sn_fwd_length/ ]
  #Hdi #HL12 elim (drop_O1_lt (Ⓕ) L1 i) //
  #I #K1 #V1 #HLK1 elim (lpx_sn_drop_conf … HL12 … HLK1) -HL12
  /4 width=9 by llpx_sn_lref, drop_fwd_rfw/
| -HR -IH /4 width=2 by lpx_sn_fwd_length, llpx_sn_gref/
| /4 width=1 by llpx_sn_bind, lpx_sn_pair/
| -HR /3 width=1 by llpx_sn_flat/
]
qed.
