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

include "NPlus/fwd.ma".
include "NLE/defs.ma".

theorem nle_inv_succ_1: \forall x,y. x < y \to 
                         \exists z. y = succ z \land x <= z.
 intros. elim H.
 lapply linear nplus_gen_succ_2 to H1.
 decompose. subst. auto depth = 4.
qed.

theorem nle_inv_succ_succ: \forall x,y. x < succ y \to x <= y.
 intros.
 lapply linear nle_inv_succ_1 to H. decompose.
 lapply linear eq_gen_succ_succ to H1. subst.
 auto.
qed.

theorem nle_inv_succ_zero: \forall x. x < zero \to False.
 intros.
 lapply linear nle_inv_succ_1 to H. decompose.
 lapply linear eq_gen_zero_succ to H1. decompose.
qed.

theorem nle_inv_zero_2: \forall x. x <= zero \to x = zero.
 intros 1. elim x; clear x; intros;
 [ auto
 | lapply linear nle_inv_succ_zero to H1. decompose.
 ].
qed.

theorem nle_inv_succ_2: \forall y,x. x <= succ y \to
                        x = zero \lor \exists z. x = succ z \land z <= y.
 intros 2; elim x; clear x; intros;
 [ auto
 | lapply linear nle_inv_succ_succ to H1.
   auto depth = 4.
 ].
qed.
