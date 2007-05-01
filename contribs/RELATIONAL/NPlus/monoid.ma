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

set "baseuri" "cic:/matita/RELATIONAL/NPlus/monoid".

include "NPlus/fun.ma".

(* Monoidal properties ******************************************************)

theorem nplus_zero_1: \forall q. zero + q == q.
 intros. elim q; clear q; auto.
qed.

theorem nplus_succ_1: \forall p,q,r. (p + q == r) \to 
                      (succ p) + q == (succ r).
 intros. elim H; clear H q r; auto.
qed.

theorem nplus_comm: \forall p, q, x. (p + q == x) \to
                    \forall y. (q + p == y) \to x = y.
 intros 4; elim H; clear H q x;
 [ lapply linear nplus_inv_zero_1 to H1
 | lapply linear nplus_inv_succ_1 to H3. decompose
 ]; subst; auto.
qed.

theorem nplus_comm_rew: \forall p,q,r. (p + q == r) \to q + p == r.
 intros. elim H; clear H q r; auto.
qed.

(* Corollaries of functional properties **************************************)

theorem nplus_inj_2: \forall p, q1, r. (p + q1 == r) \to
                     \forall q2. (p + q2 == r) \to q1 = q2.
 intros. auto.
qed.

(* Corollaries of nonoidal properties ***************************************)

theorem nplus_comm_1: \forall p1, q, r1. (p1 + q == r1) \to
                      \forall p2, r2. (p2 + q == r2) \to
                      \forall x. (p2 + r1 == x) \to 
                      \forall y. (p1 + r2 == y) \to
                      x = y.
 intros 4. elim H; clear H q r1;
 [ lapply linear nplus_inv_zero_2 to H1
 | lapply linear nplus_inv_succ_2 to H3.
   lapply linear nplus_inv_succ_2 to H4. decompose. subst.
   lapply linear nplus_inv_succ_2 to H5. decompose
 ]; subst; auto.
qed.

theorem nplus_comm_1_rew: \forall p1,q,r1. (p1 + q == r1) \to
                          \forall p2,r2. (p2 + q == r2) \to
                          \forall s. (p1 + r2 == s) \to (p2 + r1 == s).
 intros 4. elim H; clear H q r1;
 [ lapply linear nplus_inv_zero_2 to H1. subst
 | lapply linear nplus_inv_succ_2 to H3. decompose. subst.
   lapply linear nplus_inv_succ_2 to H4. decompose. subst
 ]; auto.
qed.

(*                      
theorem nplus_shift_succ_sx: \forall p,q,r. 
                             (p + (succ q) == r) \to (succ p) + q == r.
 intros.
 lapply linear nplus_inv_succ_2 to H as H0.
 decompose. subst. auto new timeout=100.
qed.

theorem nplus_shift_succ_dx: \forall p,q,r. 
                             ((succ p) + q == r) \to p + (succ q) == r.
 intros.
 lapply linear nplus_inv_succ_1 to H as H0.
 decompose. subst. auto new timeout=100.
qed.

theorem nplus_trans_1: \forall p,q1,r1. (p + q1 == r1) \to 
                       \forall q2,r2. (r1 + q2 == r2) \to
                       \exists q. (q1 + q2 == q) \land p + q == r2.
 intros 2; elim q1; clear q1; intros;
 [ lapply linear nplus_inv_zero_2 to H as H0.
   subst.
 | lapply linear nplus_inv_succ_2 to H1 as H0.
   decompose. subst.
   lapply linear nplus_inv_succ_1 to H2 as H0.
   decompose. subst.
   lapply linear H to H4, H3 as H0.
   decompose.
 ]; apply ex_intro; [| auto new timeout=100 || auto new timeout=100 ]. (**)
qed.

theorem nplus_trans_2: \forall p1,q,r1. (p1 + q == r1) \to 
                       \forall p2,r2. (p2 + r1 == r2) \to
                       \exists p. (p1 + p2 == p) \land p + q == r2.
 intros 2; elim q; clear q; intros;
 [ lapply linear nplus_inv_zero_2 to H as H0.
   subst
 | lapply linear nplus_inv_succ_2 to H1 as H0.
   decompose. subst.
   lapply linear nplus_inv_succ_2 to H2 as H0.
   decompose. subst.
   lapply linear H to H4, H3 as H0.
   decompose.
 ]; apply ex_intro; [| auto new timeout=100 || auto new timeout=100 ]. (**)
qed.
*)
