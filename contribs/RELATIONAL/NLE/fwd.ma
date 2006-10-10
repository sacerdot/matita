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

set "baseuri" "cic:/matita/RELATIONAL/NLE/fwd".

include "logic/connectives.ma".

include "Nat/fwd.ma". 
include "NLE/defs.ma".

theorem nle_gen_succ_1: \forall x,y. x < y \to 
                        \exists z. y = succ z \land x <= z.
 intros. inversion H; clear H; intros;
 [ apply (eq_gen_succ_zero ? ? H)
 | lapply linear eq_gen_succ_succ to H2 as H0.
   subst.
   apply ex_intro; [|auto new] (**)
 ].
qed.

theorem nle_gen_succ_succ: \forall x,y. x < succ y \to x <= y.
 intros; inversion H; clear H; intros;
 [ apply (eq_gen_succ_zero ? ? H)
 | lapply linear eq_gen_succ_succ to H2 as H0.
   lapply linear eq_gen_succ_succ to H3 as H2.
   subst. auto new
 ].
qed.

theorem nle_gen_succ_zero: \forall (P:Prop). \forall x. x < zero \to P.
 intros.
 lapply linear nle_gen_succ_1 to H. decompose.
 apply (eq_gen_zero_succ ? ? H1).
qed.

theorem nle_gen_zero_2: \forall x. x <= zero \to x = zero.
 intros 1. elim x; clear x; intros;
 [ auto new
 | apply (nle_gen_succ_zero ? ? H1)
 ].
qed.

theorem nle_gen_succ_2: \forall y,x. x <= succ y \to
                        x = zero \lor \exists z. x = succ z \land z <= y.
 intros 2; elim x; clear x; intros;
 [ auto new
 | lapply linear nle_gen_succ_succ to H1.
   right. apply ex_intro; [|auto new] (**)
 ].
qed.
