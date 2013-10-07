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

include "basic_2/relocation/ldrop_lpx_sn.ma".
include "basic_2/reduction/cpx_lift.ma".
include "basic_2/reduction/lpx.ma".

(* SN EXTENDED PARALLEL REDUCTION FOR LOCAL ENVIRONMENTS ********************)

(* Properies on local environment slicing ***********************************)

lemma lpx_ldrop_conf: ∀h,g,G. dropable_sn (lpx h g G).
/3 width=5 by lpx_sn_deliftable_dropable, cpx_inv_lift1/ qed-.

lemma ldrop_lpx_trans: ∀h,g,G. dedropable_sn (lpx h g G).
/3 width=9 by lpx_sn_liftable_dedropable, cpx_lift/ qed-.

lemma lpx_ldrop_trans_O1: ∀h,g,G. dropable_dx (lpx h g G).
/2 width=3 by lpx_sn_dropable/ qed-.

(* Properties on supclosure *************************************************)

lemma fsupq_lpx_trans: ∀h,g,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊃⸮ ⦃G2, L2, T2⦄ →
                       ∀K2. ⦃G2, L2⦄ ⊢ ➡[h, g] K2 →
		                   ∃∃K1,T. ⦃G1, L1⦄ ⊢ ➡[h, g] K1 & ⦃G1, L1⦄ ⊢ T1 ➡[h, g] T & ⦃G1, K1, T⦄ ⊃⸮ ⦃G2, K2, T2⦄.
#h #g #G1 #G2 #L1 #L2 #T1 #T2 #H elim H -G1 -G2 -L1 -L2 -T1 -T2
/3 width=5 by fsup_fsupq, fsupq_refl, lpx_pair, fsup_lref_O, fsup_pair_sn, fsup_flat_dx, ex3_2_intro/
[ #a #I #G2 #L2 #V2 #T2 #X #H elim (lpx_inv_pair1 … H) -H
  #K2 #W2 #HLK2 #HVW2 #H destruct
  /3 width=5 by fsup_fsupq, cpx_pair_sn, fsup_bind_dx, ex3_2_intro/
| #G1 #G2 #L1 #K1 #K2 #T1 #T2 #U1 #d #e #HLK1 #HTU1 #_ #IH12 #K0 #HK20
	elim (IH12 … HK20) -K2 #K2 #T #HK12
	elim (ldrop_lpx_trans … HLK1 … HK12) -HK12
	elim (lift_total T d e)
	/3 width=11 by cpx_lift, fsupq_ldrop, ex3_2_intro/
]
qed-.
