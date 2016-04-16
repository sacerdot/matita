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

include "basic_2/notation/relations/lazyeq_6.ma".
include "basic_2/static/lfeq_lreq.ma".
include "basic_2/static/lfeq_fqup.ma".

(* EQUIVALENCE FOR CLOSURES ON REFERRED ENTRIES *****************************)

inductive ffeq (G) (L1) (T): relation3 genv lenv term ≝
| fleq_intro: ∀L2. L1 ≡[T] L2 → ffeq G L1 T G L2 T
.

interpretation
   "equivalence on referred entries (closure)"
   'LazyEq G1 L1 T1 G2 L2 T2 = (ffeq G1 L1 T1 G2 L2 T2).

(* Basic properties *********************************************************)

lemma ffeq_refl: tri_reflexive … ffeq.
/2 width=1 by fleq_intro/ qed.

lemma ffeq_sym: tri_symmetric … ffeq.
#G1 #G2 #L1 #L2 #T1 #T2 * -G1 -L1 -T1 /3 width=1 by fleq_intro, lfeq_sym/
qed-.

(* Basic inversion lemmas ***************************************************)

lemma ffeq_inv_gen: ∀G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ≡ ⦃G2, L2, T2⦄ →
                    ∧∧ G1 = G2 & L1 ≡[T1] L2 & T1 = T2.
#G1 #G2 #L1 #L2 #T1 #T2 * -G2 -L2 -T2 /2 width=1 by and3_intro/
qed-.

(* Basic_2A1: removed theorems 6:
              fleq_refl fleq_sym fleq_inv_gen
              fleq_trans fleq_canc_sn fleq_canc_dx
*)
