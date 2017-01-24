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

include "basic_2/notation/relations/lazyeq_8.ma".
include "basic_2/syntax/genv.ma".
include "basic_2/static/lfdeq_fqup.ma".

(* DEGREE-BASED EQUIVALENCE FOR CLOSURES ON REFERRED ENTRIES ****************)

inductive ffdeq (h) (o) (G) (L1) (T): relation3 genv lenv term ≝
| ffdeq_intro: ∀L2. L1 ≡[h, o, T] L2 → ffdeq h o G L1 T G L2 T
.

interpretation
   "degree-based equivalence on referred entries (closure)"
   'LazyEq h o G1 L1 T1 G2 L2 T2 = (ffdeq h o G1 L1 T1 G2 L2 T2).

(* Basic properties *********************************************************)

lemma ffdeq_sym: ∀h,o. tri_symmetric … (ffdeq h o).
#h #o #G1 #G2 #L1 #L2 #T1 #T2 * -G1 -L1 -T1 /3 width=1 by ffdeq_intro, lfdeq_sym/
qed-.

(* Basic inversion lemmas ***************************************************)

lemma ffdeq_inv_gen: ∀h,o,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ≡[h, o] ⦃G2, L2, T2⦄ →
                     ∧∧ G1 = G2 & L1 ≡[h, o, T1] L2 & T1 = T2.
#h #o #G1 #G2 #L1 #L2 #T1 #T2 * -G2 -L2 -T2 /2 width=1 by and3_intro/
qed-.

(* Basic_2A1: removed theorems 6:
              fleq_refl fleq_sym fleq_inv_gen
              fleq_trans fleq_canc_sn fleq_canc_dx
*)
