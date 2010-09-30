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



include "NPlus/fun.ma".

(* Monoidal properties ******************************************************)

theorem nplus_zero_1: ∀q. zero ⊕ q ≍ q.
 intros; elim q; clear q; autobatch.
qed.

theorem nplus_succ_1: ∀p,q,r. p ⊕ q ≍ r → succ p ⊕ q ≍ succ r.
 intros; elim H; clear H q r; autobatch.
qed.

theorem nplus_comm: ∀p, q, x. p ⊕ q ≍ x → ∀y. q ⊕ p ≍ y → x = y.
 intros 4; elim H; clear H q x;
 [ lapply linear nplus_inv_zero_1 to H1
 | lapply linear nplus_inv_succ_1 to H3. decompose
 ]; destruct; autobatch.
qed.

theorem nplus_comm_rew: ∀p,q,r. p ⊕ q ≍ r → q ⊕ p ≍ r.
 intros; elim H; clear H q r; autobatch.
qed.

theorem nplus_ass: ∀p1, p2, r1. p1 ⊕ p2 ≍ r1 → ∀p3, s1. r1 ⊕ p3 ≍ s1 →
                   ∀r3. p2 ⊕ p3 ≍ r3 → ∀s3. p1 ⊕ r3 ≍ s3 → s1 = s3.
 intros 4; elim H; clear H p2 r1;
 [ lapply linear nplus_inv_zero_1 to H2. destruct.
   lapply nplus_mono to H1, H3. destruct. autobatch
 | lapply linear nplus_inv_succ_1 to H3. decompose. destruct.
   lapply linear nplus_inv_succ_1 to H4. decompose. destruct.
   lapply linear nplus_inv_succ_2 to H5. decompose. destruct. autobatch
 ].
qed.
 
(* Corollaries of functional properties **************************************)

theorem nplus_inj_2: ∀p, q1, r. p ⊕ q1 ≍ r → ∀q2. p ⊕ q2 ≍ r → q1 = q2.
 intros. autobatch.
qed.

(* Corollaries of nonoidal properties ***************************************)

theorem nplus_comm_1: ∀p1, q, r1. p1 ⊕ q ≍ r1 → ∀p2, r2. p2 ⊕ q ≍ r2 →
                      ∀x. p2 ⊕ r1 ≍ x → ∀y. p1 ⊕ r2 ≍ y → x = y.
 intros 4; elim H; clear H q r1;
 [ lapply linear nplus_inv_zero_2 to H1
 | lapply linear nplus_inv_succ_2 to H3.
   lapply linear nplus_inv_succ_2 to H4. decompose. destruct.
   lapply linear nplus_inv_succ_2 to H5. decompose
 ]; destruct; autobatch.
qed.

theorem nplus_comm_1_rew: ∀p1,q,r1. p1 ⊕ q ≍ r1 → ∀p2,r2. p2 ⊕ q ≍ r2 →
                          ∀s. p1 ⊕ r2 ≍ s → p2 ⊕ r1 ≍ s.
 intros 4; elim H; clear H q r1;
 [ lapply linear nplus_inv_zero_2 to H1. destruct
 | lapply linear nplus_inv_succ_2 to H3. decompose. destruct.
   lapply linear nplus_inv_succ_2 to H4. decompose. destruct
 ]; autobatch.
qed.

(*                      
theorem nplus_shift_succ_sx: \forall p,q,r. 
                             (p \oplus (succ q) \asymp r) \to (succ p) \oplus q \asymp r.
 intros.
 lapply linear nplus_inv_succ_2 to H as H0.
 decompose. destruct. auto new timeout=100.
qed.

theorem nplus_shift_succ_dx: \forall p,q,r. 
                             ((succ p) \oplus q \asymp r) \to p \oplus (succ q) \asymp r.
 intros.
 lapply linear nplus_inv_succ_1 to H as H0.
 decompose. destruct. auto new timeout=100.
qed.

theorem nplus_trans_1: \forall p,q1,r1. (p \oplus q1 \asymp r1) \to 
                       \forall q2,r2. (r1 \oplus q2 \asymp r2) \to
                       \exists q. (q1 \oplus q2 \asymp q) \land p \oplus q \asymp r2.
 intros 2; elim q1; clear q1; intros;
 [ lapply linear nplus_inv_zero_2 to H as H0.
   destruct.
 | lapply linear nplus_inv_succ_2 to H1 as H0.
   decompose. destruct.
   lapply linear nplus_inv_succ_1 to H2 as H0.
   decompose. destruct.
   lapply linear H to H4, H3 as H0.
   decompose.
 ]; apply ex_intro; [| auto new timeout=100 || auto new timeout=100 ]. (**)
qed.

theorem nplus_trans_2: ∀p1,q,r1. p1 ⊕ q ≍ r1 → ∀p2,r2. p2 ⊕ r1 ≍ r2 →
                       ∃p. p1 ⊕ p2 ≍ p ∧ p ⊕ q ≍ r2.
 intros 2; elim q; clear q; intros;
 [ lapply linear nplus_inv_zero_2 to H as H0.
   destruct
 | lapply linear nplus_inv_succ_2 to H1 as H0.
   decompose. destruct.
   lapply linear nplus_inv_succ_2 to H2 as H0.
   decompose. destruct.
   lapply linear H to H4, H3 as H0.
   decompose.
 ]; autobatch. apply ex_intro; [| auto new timeout=100 || auto new timeout=100 ]. (**)
qed.
*)
