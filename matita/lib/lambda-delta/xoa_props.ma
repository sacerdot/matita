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

include "lambda-delta/xoa_notation.ma".
include "lambda-delta/xoa.ma".

lemma ex2_1_comm: ∀A0. ∀P0,P1:A0→Prop. (∃∃x0. P0 x0 & P1 x0) → ∃∃x0. P1 x0 & P0 x0.
#A0 #P0 #P1 * /2/
qed.
