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

set "baseuri" "cic:/matita/RELATIONAL/NPlus/props".

include "NPlus/fwd.ma".

theorem nplus_zero_1: \forall q. zero + q == q.
 intros. elim q; clear q; auto new.
qed.

theorem nplus_succ_1: \forall p,q,r. NPlus p q r \to 
                      (succ p) + q == (succ r).
 intros 2. elim q; clear q;
 [ lapply linear nplus_gen_zero_2 to H as H0.
   subst
 | lapply linear nplus_gen_succ_2 to H1 as H0.
   decompose.
   subst
 ]; auto new.
qed.

theorem nplus_sym: \forall p,q,r. (p + q == r) \to q + p == r.
 intros 2. elim q; clear q;
 [ lapply linear nplus_gen_zero_2 to H as H0.
   subst
 | lapply linear nplus_gen_succ_2 to H1 as H0.
   decompose.
   subst
 ]; auto new.
qed.

theorem nplus_shift_succ_sx: \forall p,q,r. 
                             (p + (succ q) == r) \to (succ p) + q == r.
 intros.
 lapply linear nplus_gen_succ_2 to H as H0.
 decompose. subst. auto new.
qed.

theorem nplus_shift_succ_dx: \forall p,q,r. 
                             ((succ p) + q == r) \to p + (succ q) == r.
 intros.
 lapply linear nplus_gen_succ_1 to H as H0.
 decompose. subst. auto new.
qed.

theorem nplus_trans_1: \forall p,q1,r1. (p + q1 == r1) \to 
                       \forall q2,r2. (r1 + q2 == r2) \to
                       \exists q. (q1 + q2 == q) \land p + q == r2.
 intros 2; elim q1; clear q1; intros;
 [ lapply linear nplus_gen_zero_2 to H as H0.
   subst.
 | lapply linear nplus_gen_succ_2 to H1 as H0.
   decompose. subst.
   lapply linear nplus_gen_succ_1 to H2 as H0.
   decompose. subst.
   lapply linear H to H4, H3 as H0.
   decompose.
 ]; apply ex_intro; [| auto new || auto new ]. (**)
qed.

theorem nplus_trans_2: \forall p1,q,r1. (p1 + q == r1) \to 
                       \forall p2,r2. (p2 + r1 == r2) \to
                       \exists p. (p1 + p2 == p) \land p + q == r2.
 intros 2; elim q; clear q; intros;
 [ lapply linear nplus_gen_zero_2 to H as H0.
   subst
 | lapply linear nplus_gen_succ_2 to H1 as H0.
   decompose. subst.
   lapply linear nplus_gen_succ_2 to H2 as H0.
   decompose. subst.
   lapply linear H to H4, H3 as H0.
   decompose.
 ]; apply ex_intro; [| auto new || auto new ]. (**)
qed.

theorem nplus_conf: \forall p,q,r1. (p + q == r1) \to 
                    \forall r2. (p + q == r2) \to r1 = r2.
 intros 2. elim q; clear q; intros;
 [ lapply linear nplus_gen_zero_2 to H as H0.
   subst
 | lapply linear nplus_gen_succ_2 to H1 as H0.
   decompose. subst.
   lapply linear nplus_gen_succ_2 to H2 as H0.
   decompose. subst.
 ]; auto new.
qed.
