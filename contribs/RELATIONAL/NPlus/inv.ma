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

(* primitive generation lemmas proved by elimination and inversion *)

theorem nplus_gen_zero_1: \forall q,r. (zero + q == r) \to q = r.
 intros. elim H; clear H q r; intros;
 [ reflexivity
 | clear H1. auto new timeout=30
 ].
qed.

theorem nplus_gen_succ_1: \forall p,q,r. ((succ p) + q == r) \to 
                          \exists s. r = (succ s) \land p + q == s.
 intros. elim H; clear H q r; intros;
 [
 | clear H1.
   decompose.
   subst.
 ]; apply ex_intro; [| auto new timeout=30 || auto new timeout=30 ]. (**)
qed.

theorem nplus_gen_zero_2: \forall p,r. (p + zero == r) \to p = r.
 intros. inversion H; clear H; intros;
 [ auto new timeout=30
 | clear H H1.
   destruct H2.
 ].
qed.

theorem nplus_gen_succ_2: \forall p,q,r. (p + (succ q) == r) \to 
                          \exists s. r = (succ s) \land p + q == s.
 intros. inversion H; clear H; intros;
 [ destruct H.
 | clear H1 H3 r.
   destruct H2; clear H2.
   subst.
   apply ex_intro; [| auto new timeout=30 ] (**)
 ].
qed.

theorem nplus_gen_zero_3: \forall p,q. (p + q == zero) \to 
                          p = zero \land q = zero.
 intros. inversion H; clear H; intros;
 [ subst. auto new timeout=30
 | clear H H1.
   destruct H3.
 ].
qed.

theorem nplus_gen_succ_3: \forall p,q,r. (p + q == (succ r)) \to
                          \exists s. p = succ s \land (s + q == r) \lor
                                     q = succ s \land p + s == r.
 intros. inversion H; clear H; intros;
 [ subst.
 | clear H1.
   destruct H3. clear H3.
   subst.
 ]; apply ex_intro; [| auto new timeout=30 || auto new timeout=30 ] (**)
qed.
(*
(* alternative proofs invoking nplus_gen_2 *)

variant nplus_gen_zero_3_alt: \forall p,q. (p + q == zero) \to 
                              p = zero \land q = zero.
 intros 2. elim q; clear q; intros;
 [ lapply linear nplus_gen_zero_2 to H as H0.
   subst. auto new timeout=30
 | clear H.
   lapply linear nplus_gen_succ_2 to H1 as H0.
   decompose.
   lapply linear eq_gen_zero_succ to H1 as H0. apply H0
 ].
qed.

variant nplus_gen_succ_3_alt: \forall p,q,r. (p + q == (succ r)) \to
                              \exists s. p = succ s \land (s + q == r) \lor
                                         q = succ s \land p + s == r.
 intros 2. elim q; clear q; intros;
 [ lapply linear nplus_gen_zero_2 to H as H0.
   subst
 | clear H.
   lapply linear nplus_gen_succ_2 to H1 as H0.
   decompose.
   lapply linear eq_gen_succ_succ to H1 as H0.
   subst
 ]; apply ex_intro; [| auto new timeout=30 || auto new timeout=30 ]. (**)
qed.
*)
(* other simplification lemmas *)

theorem nplus_gen_eq_2_3: \forall p,q. (p + q == q) \to p = zero.
 intros 2. elim q; clear q; intros;
 [ lapply linear nplus_gen_zero_2 to H as H0.
   subst
 | lapply linear nplus_gen_succ_2 to H1 as H0.
   decompose.
   destruct H2. clear H2.
   subst
 ]; auto new timeout=30.
qed.

theorem nplus_gen_eq_1_3: \forall p,q. (p + q == p) \to q = zero.
 intros 1. elim p; clear p; intros;
 [ lapply linear nplus_gen_zero_1 to H as H0.
   subst
 | lapply linear nplus_gen_succ_1 to H1 as H0.
   decompose.
   destruct H2. clear H2.
   subst
 ]; auto new timeout=30.
qed.
