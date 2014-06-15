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

include "basic_2/notation/relations/lazyeq_4.ma".
include "basic_2/grammar/term.ma".
include "basic_2/static/sd.ma".

(* STRATIFIED EQUIVALENCE FOR TERMS *****************************************)

inductive steq (h) (g): relation term ≝
| steq_refl: ∀T. steq h g T T
| steq_zero: ∀k1,k2. deg h g k1 0 → deg h g k2 0 → steq h g (⋆k1) (⋆k2)
.

interpretation
   "stratified equivalence (term)"
   'LazyEq h g T1 T2 = (steq h g T1 T2).

(* Basic inversion lemmas ****************************************************)

lemma steq_inv: ∀h,g,T1,T2. T1 ≡[h, g] T2 → T1 = T2 ∨
                ∃∃k1,k2. deg h g k1 0 & deg h g k2 0 & T1 = ⋆k1 & T2 = ⋆k2.
#h #g #T1 #T2 * /3 width=6 by or_introl, or_intror, ex4_2_intro/
qed-.

(* Basic properties *********************************************************)

lemma steq_sym: ∀h,g. symmetric … (steq h g).
#h #g #T1 #T2 * /2 width=1 by steq_zero/
qed-.
