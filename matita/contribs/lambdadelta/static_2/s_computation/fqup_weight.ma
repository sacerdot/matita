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

include "static_2/s_transition/fqu_weight.ma".
include "static_2/s_computation/fqup.ma".

(* PLUS-ITERATED SUPCLOSURE *************************************************)

(* Forward lemmas with weight for closures **********************************)

lemma fqup_fwd_fw: ∀b,G1,G2,L1,L2,T1,T2. ⦃G1,L1,T1⦄ ⬂+[b] ⦃G2,L2,T2⦄ →
                   ♯{G2,L2,T2} < ♯{G1,L1,T1}.
#b #G1 #G2 #L1 #L2 #T1 #T2 #H @(fqup_ind … H) -G2 -L2 -T2
/3 width=3 by fqu_fwd_fw, transitive_lt/
qed-.

(* Advanced eliminators *****************************************************)

lemma fqup_wf_ind: ∀b. ∀Q:relation3 …. (
                      ∀G1,L1,T1. (∀G2,L2,T2. ⦃G1,L1,T1⦄ ⬂+[b] ⦃G2,L2,T2⦄ → Q G2 L2 T2) →
                      Q G1 L1 T1
                   ) → ∀G1,L1,T1. Q G1 L1 T1.
#b #Q #HQ @(f3_ind … fw) #x #IHx #G1 #L1 #T1 #H destruct
/4 width=2 by fqup_fwd_fw/
qed-.

lemma fqup_wf_ind_eq: ∀b. ∀Q:relation3 …. (
                         ∀G1,L1,T1. (∀G2,L2,T2. ⦃G1,L1,T1⦄ ⬂+[b] ⦃G2,L2,T2⦄ → Q G2 L2 T2) →
                         ∀G2,L2,T2. G1 = G2 → L1 = L2 → T1 = T2 → Q G2 L2 T2
                      ) → ∀G1,L1,T1. Q G1 L1 T1.
#b #Q #HQ @(f3_ind … fw) #x #IHx #G1 #L1 #T1 #H destruct
/4 width=7 by fqup_fwd_fw/
qed-.
