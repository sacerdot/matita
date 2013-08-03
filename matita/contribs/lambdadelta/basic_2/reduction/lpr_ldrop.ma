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

include "basic_2/relocation/fsup.ma".
include "basic_2/relocation/ldrop_lpx_sn.ma".
include "basic_2/reduction/cpr_lift.ma".
include "basic_2/reduction/lpr.ma".

(* SN PARALLEL REDUCTION FOR LOCAL ENVIRONMENTS *****************************)

(* Properies on local environment slicing ***********************************)

(* Basic_1: includes: wcpr0_drop *)
lemma lpr_ldrop_conf: ∀G. dropable_sn (lpr G).
/3 width=5 by lpx_sn_deliftable_dropable, cpr_inv_lift1/ qed-.

(* Basic_1: includes: wcpr0_drop_back *)
lemma ldrop_lpr_trans: ∀G. dedropable_sn (lpr G).
/3 width=9 by lpx_sn_liftable_dedropable, cpr_lift/ qed-.

lemma lpr_ldrop_trans_O1: ∀G. dropable_dx (lpr G).
/2 width=3 by lpx_sn_dropable/ qed-.

(* Properties on context-sensitive parallel reduction for terms *************)

lemma fsup_cpr_trans: ∀G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊃ ⦃G2, L2, T2⦄ →
                      ∀U2. ⦃G2, L2⦄ ⊢ T2 ➡ U2 →
                      ∃∃L,U1. ⦃G1, L1⦄ ⊢ ➡ L & ⦃G1, L⦄ ⊢ T1 ➡ U1 & ⦃G1, L, U1⦄ ⊃ ⦃G2, L2, U2⦄.
#G1 #G2 #L1 #L2 #T1 #T2 #H elim H -G1 -G2 -L1 -L2 -T1 -T2 [1,2,3,4,5: /3 width=5/ ]
[ #G #L #K #U #T #d #e #HLK #HUT #He #U2 #HU2
  elim (lift_total U2 d e) #T2 #HUT2
  lapply (cpr_lift … HU2 … HLK … HUT … HUT2) -HU2 -HUT /3 width=9/
| #G1 #G2 #L1 #K1 #K2 #T1 #T2 #U1 #d #e #HLK1 #HTU1 #_ #IHT12 #U2 #HTU2
  elim (IHT12 … HTU2) -IHT12 -HTU2 #K #T #HK1 #HT1 #HT2
  elim (lift_total T d e) #U #HTU
  elim (ldrop_lpr_trans … HLK1 … HK1) -HLK1 -HK1 #L2 #HL12 #HL2K
  lapply (cpr_lift … HT1 … HL2K … HTU1 … HTU) -HT1 -HTU1 /3 width=11/
]
qed-.
