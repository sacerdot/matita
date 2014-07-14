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

include "basic_2/notation/relations/lazyeq_7.ma".
include "basic_2/grammar/genv.ma".
include "basic_2/multiple/lleq.ma".

(* LAZY EQUIVALENCE FOR CLOSURES ********************************************)

inductive fleq (d) (G) (L1) (T): relation3 genv lenv term ≝
| fleq_intro: ∀L2. L1 ≡[T, d] L2 → fleq d G L1 T G L2 T
.

interpretation
   "lazy equivalence (closure)"
   'LazyEq d G1 L1 T1 G2 L2 T2 = (fleq d G1 L1 T1 G2 L2 T2).

(* Basic properties *********************************************************)

lemma fleq_refl: ∀d. tri_reflexive … (fleq d).
/2 width=1 by fleq_intro/ qed.

lemma fleq_sym: ∀d. tri_symmetric … (fleq d).
#d #G1 #L1 #T1 #G2 #L2 #T2 * /3 width=1 by fleq_intro, lleq_sym/
qed-.

(* Basic inversion lemmas ***************************************************)

lemma fleq_inv_gen: ∀G1,G2,L1,L2,T1,T2,d. ⦃G1, L1, T1⦄ ≡[d] ⦃G2, L2, T2⦄ →
                    ∧∧ G1 = G2 & L1 ≡[T1, d] L2 & T1 = T2.
#G1 #G2 #L1 #L2 #T1 #T2 #d * -G2 -L2 -T2 /2 width=1 by and3_intro/
qed-.
