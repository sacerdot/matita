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

set "baseuri" "cic:/matita/RELATIONAL-ARITHMETICS/add_props".

include "add_gen.ma".

theorem add_O_1: \forall q. add O q q.
 intros. elim q; clear q; auto.
qed.

theorem add_S_1: \forall p,q,r. add p q r \to add (S p) q (S r).
 intros 2. elim q; clear q;
 [ lapply add_gen_O_2 to H as H0. clear H.
   rewrite > H0. clear H0. clear p
 | lapply add_gen_S_2 to H1 as H0. clear H1.
   decompose H0.
   rewrite > H2. clear H2. clear r
 ]; auto.
qed.

theorem add_sym: \forall p,q,r. add p q r \to add q p r.
 intros 2. elim q; clear q;
 [ lapply add_gen_O_2 to H as H0. clear H.
   rewrite > H0. clear H0. clear p
 | lapply add_gen_S_2 to H1 as H0. clear H1.
   decompose H0.
   rewrite > H2. clear H2. clear r
 ]; auto.
qed.

theorem add_shift_S_sx: \forall p,q,r. add p (S q) r \to add (S p) q r.
 intros.
 lapply add_gen_S_2 to H as H0. clear H.
 decompose H0.
 rewrite > H1. clear H1. clear r.
 auto.
qed.


theorem add_shift_S_dx: \forall p,q,r. add (S p) q r \to add p (S q) r.
 intros.
 lapply add_gen_S_1 to H as H0. clear H.
 decompose H0.
 rewrite > H1. clear H1. clear r.
 auto.
qed.

theorem add_trans_1: \forall p,q1,r1. add p q1 r1 \to 
                     \forall q2,r2. add r1 q2 r2 \to
                     \exists q. add q1 q2 q \land add p q r2.
 intros 2; elim q1; clear q1; intros;
 [ lapply add_gen_O_2 to H as H0. clear H.
   rewrite > H0. clear H0. clear p
 | lapply add_gen_S_2 to H1 as H0. clear H1.
   decompose H0.
   rewrite > H3. rewrite > H3 in H2. clear H3. clear r1.
   lapply add_gen_S_1 to H2 as H0. clear H2.
   decompose H0.
   rewrite > H2. clear H2. clear r2.
   lapply H to H4, H3 as H0. clear H. clear H4. clear H3.
   decompose H0.
 ]; apply ex_intro; [| auto || auto ]. (**)
qed.

theorem add_trans_2: \forall p1,q,r1. add p1 q r1 \to 
                     \forall p2,r2. add p2 r1 r2 \to
                     \exists p. add p1 p2 p \land add p q r2.
 intros 2; elim q; clear q; intros;
 [ lapply add_gen_O_2 to H as H0. clear H.
   rewrite > H0. clear H0. clear p1
 | lapply add_gen_S_2 to H1 as H0. clear H1.
   decompose H0.
   rewrite > H3. rewrite > H3 in H2. clear H3. clear r1.
   lapply add_gen_S_2 to H2 as H0. clear H2.
   decompose H0.
   rewrite > H2. clear H2. clear r2.
   lapply H to H4, H3 as H0. clear H. clear H4. clear H3. 
   decompose H0.
 ]; apply ex_intro; [| auto || auto ]. (**)
qed.

theorem add_conf: \forall p,q,r1. add p q r1 \to 
                  \forall r2. add p q r2 \to r1 = r2.
 intros 2. elim q; clear q; intros;
 [ lapply add_gen_O_2 to H as H0. clear H.
   rewrite > H0 in H1. clear H0. clear p
 | lapply add_gen_S_2 to H1 as H0. clear H1.
   decompose H0.
   rewrite > H3. clear H3. clear r1.
   lapply add_gen_S_2 to H2 as H0. clear H2.
   decompose H0.
   rewrite > H2. clear H2. clear r2.
 ]; auto.
qed.



theorem add_gen_eq_2_3: \forall p,q. add p q q \to p = O.
 intros 2. elim q; clear q; intros;
 [ lapply add_gen_O_2 to H as H0. clear H.
   rewrite > H0. clear H0. clear p
 | lapply add_gen_S_2 to H1 as H0. clear H1.
   decompose H0.
   lapply eq_gen_S_S to H2 as H0. clear H2.
   rewrite < H0 in H3. clear H0. clear a
 ]; auto.
qed.

theorem add_gen_eq_1_3: \forall p,q. add p q p \to q = O.
 intros. 
 lapply add_sym to H. clear H.
 auto.
qed.
