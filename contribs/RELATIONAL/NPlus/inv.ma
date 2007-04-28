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

set "baseuri" "cic:/matita/RELATIONAL/NPlus/inv".

include "NPlus/defs.ma".

(* Inversion lemmas *********************************************************)

theorem nplus_inv_zero_1: \forall q,r. (zero + q == r) \to q = r.
 intros. elim H; clear H q r; auto.
qed.

theorem nplus_inv_succ_1: \forall p,q,r. ((succ p) + q == r) \to 
                          \exists s. r = (succ s) \land p + q == s.
 intros. elim H; clear H q r; intros;
 [ auto depth = 4
 | clear H1. decompose. subst. auto depth = 4
 ]
qed.

theorem nplus_inv_zero_2: \forall p,r. (p + zero == r) \to p = r.
 intros. inversion H; clear H; intros; subst. auto.
qed.

theorem nplus_inv_succ_2: \forall p,q,r. (p + (succ q) == r) \to 
                          \exists s. r = (succ s) \land p + q == s.
 intros. inversion H; clear H; intros; subst. auto depth = 4.
qed.

theorem nplus_inv_zero_3: \forall p,q. (p + q == zero) \to 
                          p = zero \land q = zero.
 intros. inversion H; clear H; intros; subst. auto.
qed.

theorem nplus_inv_succ_3: \forall p,q,r. (p + q == (succ r)) \to
                          \exists s. p = succ s \land (s + q == r) \lor
                                     q = succ s \land p + s == r.
 intros. inversion H; clear H; intros; subst; auto depth = 4.
qed.

(* Corollaries to inversion lemmas ******************************************)

theorem nplus_inv_succ_2_3: \forall p,q,r.
                            (p + (succ q) == (succ r)) \to p + q == r.
 intros. 
 lapply linear nplus_inv_succ_2 to H. decompose. subst. auto.
qed.

theorem nplus_inv_succ_1_3: \forall p,q,r.
                            ((succ p) + q == (succ r)) \to p + q == r.
 intros. 
 lapply linear nplus_inv_succ_1 to H. decompose. subst. auto.
qed.

theorem nplus_inv_eq_2_3: \forall p,q. (p + q == q) \to p = zero.
 intros 2. elim q; clear q;
 [ lapply linear nplus_inv_zero_2 to H
 | lapply linear nplus_inv_succ_2_3 to H1
 ]; auto.
qed.

theorem nplus_inv_eq_1_3: \forall p,q. (p + q == p) \to q = zero.
 intros 1. elim p; clear p;
 [ lapply linear nplus_inv_zero_1 to H
 | lapply linear nplus_inv_succ_1_3 to H1.
 ]; auto.
qed.
