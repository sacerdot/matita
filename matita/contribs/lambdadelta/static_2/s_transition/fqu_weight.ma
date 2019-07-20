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

include "static_2/syntax/cl_weight.ma".
include "static_2/relocation/lifts_weight.ma".
include "static_2/s_transition/fqu.ma".

(* SUPCLOSURE ***************************************************************)

(* Forward lemmas with weight for closures **********************************)

lemma fqu_fwd_fw: ∀b,G1,G2,L1,L2,T1,T2. ⦃G1,L1,T1⦄ ⬂[b] ⦃G2,L2,T2⦄ →
                  ♯{G2,L2,T2} < ♯{G1,L1,T1}.
#b #G1 #G2 #L1 #L2 #T1 #T2 #H elim H -G1 -G2 -L1 -L2 -T1 -T2 //
#I #I1 #I2 #G #L #HI12 normalize in ⊢ (?%%); -I1
<(lifts_fwd_tw … HI12) /3 width=1 by monotonic_lt_plus_r, monotonic_lt_plus_l/
qed-.

(* Advanced eliminators *****************************************************)

lemma fqu_wf_ind: ∀b. ∀Q:relation3 …. (
                     ∀G1,L1,T1. (∀G2,L2,T2. ⦃G1,L1,T1⦄ ⬂[b] ⦃G2,L2,T2⦄ → Q G2 L2 T2) →
		                 Q G1 L1 T1
		              ) → ∀G1,L1,T1. Q G1 L1 T1.
#b #Q #HQ @(f3_ind … fw) #x #IHx #G1 #L1 #T1 #H destruct /4 width=2 by fqu_fwd_fw/
qed-.
