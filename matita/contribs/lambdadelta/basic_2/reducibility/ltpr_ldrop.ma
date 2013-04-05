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

include "basic_2/substitution/ldrop_lpx.ma".
include "basic_2/substitution/fsup.ma".
include "basic_2/reducibility/tpr_lift.ma".
include "basic_2/reducibility/ltpr.ma".

(* CONTEXT-FREE PARALLEL REDUCTION ON LOCAL ENVIRONMENTS ********************)

(* Properies on local environment slicing ***********************************)

(* Basic_1: was: wcpr0_drop *)
lemma ltpr_ldrop_conf: dropable_sn ltpr.
/3 width=3 by lpx_deliftable_dropable, tpr_inv_lift1/ qed.

(* Basic_1: was: wcpr0_drop_back *)
lemma ldrop_ltpr_trans: dedropable_sn ltpr.
/2 width=3/ qed.

lemma ltpr_ldrop_trans_O1: dropable_dx ltpr.
/2 width=3/ qed.

(* Properties on supclosure *************************************************)

lemma fsub_tpr_trans: ∀L1,L2,T1,T2. ⦃L1, T1⦄ ⊃ ⦃L2, T2⦄ → ∀U2. T2 ➡ U2 →
                      ∃∃L,U1. L1 ➡ L & T1 ➡ U1 & ⦃L, U1⦄ ⊃ ⦃L2, U2⦄.
#L1 #L2 #T1 #T2 #H elim H -L1 -L2 -T1 -T2 [1,2,3,4,5: /3 width=5/ ]
#L1 #K1 #K2 #T1 #T2 #U1 #d #e #HLK1 #HTU1 #_ #IHT12 #U2 #HTU2
elim (IHT12 … HTU2) -IHT12 -HTU2 #K #T #HK1 #HT1 #HK2
elim (lift_total T d e) #U #HTU
elim (ldrop_ltpr_trans … HLK1 … HK1) -HLK1 -HK1 #L #HL1 #HLK
lapply (tpr_lift … HT1 … HTU1 … HTU) -HT1 -HTU1 /3 width=11/
qed-.
