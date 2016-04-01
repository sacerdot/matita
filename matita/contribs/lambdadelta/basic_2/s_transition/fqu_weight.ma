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

include "basic_2/grammar/cl_weight.ma".
include "basic_2/relocation/lifts_weight.ma".
include "basic_2/s_transition/fqu.ma".

(* SUPCLOSURE ***************************************************************)

(* Forward lemmas with weight for closures **********************************)

lemma fqu_fwd_fw: ∀G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊐ ⦃G2, L2, T2⦄ → ♯{G2, L2, T2} < ♯{G1, L1, T1}.
#G1 #G2 #L1 #L2 #T1 #T2 #H elim H -G1 -G2 -L1 -L2 -T1 -T2 //
#I #G #L #V #T #U #HTU normalize in ⊢ (?%%); -I
<(lifts_fwd_tw … HTU) -U /3 width=1 by monotonic_lt_plus_r, monotonic_lt_plus_l/
qed-.

(* Advanced eliminators *****************************************************)

lemma fqu_wf_ind: ∀R:relation3 …. (
                     ∀G1,L1,T1. (∀G2,L2,T2. ⦃G1, L1, T1⦄ ⊐ ⦃G2, L2, T2⦄ → R G2 L2 T2) →
		                 R G1 L1 T1
		              ) → ∀G1,L1,T1. R G1 L1 T1.
#R #HR @(f3_ind … fw) #x #IHx #G1 #L1 #T1 #H destruct /4 width=1 by fqu_fwd_fw/
qed-.
