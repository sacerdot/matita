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

include "basic_2/s_transition/fqu_weight.ma".
include "basic_2/s_computation/fqup.ma".

(* PLUS-ITERATED SUPCLOSURE *************************************************)

(* Forward lemmas with weight for closures **********************************)

lemma fqup_fwd_fw: ∀G1,G2,L1,L2,T1,T2.
                   ⦃G1, L1, T1⦄ ⊐+ ⦃G2, L2, T2⦄ → ♯{G2, L2, T2} < ♯{G1, L1, T1}.
#G1 #G2 #L1 #L2 #T1 #T2 #H @(fqup_ind … H) -G2 -L2 -T2
/3 width=3 by fqu_fwd_fw, transitive_lt/
qed-.

(* Advanced eliminators *****************************************************)

lemma fqup_wf_ind: ∀R:relation3 …. (
                      ∀G1,L1,T1. (∀G2,L2,T2. ⦃G1, L1, T1⦄ ⊐+ ⦃G2, L2, T2⦄ → R G2 L2 T2) →
                      R G1 L1 T1
                   ) → ∀G1,L1,T1. R G1 L1 T1.
#R #HR @(f3_ind … fw) #x #IHx #G1 #L1 #T1 #H destruct /4 width=1 by fqup_fwd_fw/
qed-.

lemma fqup_wf_ind_eq: ∀R:relation3 …. (
                         ∀G1,L1,T1. (∀G2,L2,T2. ⦃G1, L1, T1⦄ ⊐+ ⦃G2, L2, T2⦄ → R G2 L2 T2) →
                         ∀G2,L2,T2. G1 = G2 → L1 = L2 → T1 = T2 → R G2 L2 T2
                      ) → ∀G1,L1,T1. R G1 L1 T1.
#R #HR @(f3_ind … fw) #x #IHx #G1 #L1 #T1 #H destruct /4 width=7 by fqup_fwd_fw/
qed-.
