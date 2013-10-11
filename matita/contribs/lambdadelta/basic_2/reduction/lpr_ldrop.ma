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

include "basic_2/relocation/fsupq_alt.ma".
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
#G1 #G2 #L1 #L2 #T1 #T2 #H elim H -G1 -G2 -L1 -L2 -T1 -T2
/3 width=5 by fsup_lref_O, fsup_pair_sn, fsup_bind_dx, fsup_flat_dx, lpr_pair, cpr_pair_sn, cpr_atom, cpr_bind, cpr_flat, ex3_2_intro/
#G #L #K #U #T #e #HLK #HUT #U2 #HU2
elim (lift_total U2 0 (e+1)) #T2 #HUT2
lapply (cpr_lift … HU2 … HLK … HUT … HUT2) -HU2 -HUT /3 width=9 by fsup_drop, ex3_2_intro/
qed-.

lemma fsupq_cpr_trans: ∀G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊃⸮ ⦃G2, L2, T2⦄ →
                       ∀U2. ⦃G2, L2⦄ ⊢ T2 ➡ U2 →
                       ∃∃L,U1. ⦃G1, L1⦄ ⊢ ➡ L & ⦃G1, L⦄ ⊢ T1 ➡ U1 & ⦃G1, L, U1⦄ ⊃⸮ ⦃G2, L2, U2⦄.
#G1 #G2 #L1 #L2 #T1 #T2 #H #U2 #HTU2 elim (fsupq_inv_gen … H) -H
[ #HT12 elim (fsup_cpr_trans … HT12 … HTU2) /3 width=5 by fsup_fsupq, ex3_2_intro/
| * #H1 #H2 #H3 destruct /2 width=5 by ex3_2_intro/
]
qed-.
