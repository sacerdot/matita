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

include "lambda/subterms/boolean.ma".

include "lambda/notation/functions/projectsame_2.ma".

include "lambda/xoa/ex_4_3.ma".

(* BOOLEANIZED SUBSET (EMPTY OR FULL) ***************************************)

definition booleanized: bool → subterms → subterms ≝
   λb,F. ❴b❵⇑⇓F.

interpretation "booleanized (subterms)"
   'ProjectSame b F = (booleanized b F).

lemma booleanized_inv_vref: ∀j,c,b,F. ❴b❵⇕ F = ❴c❵#j →
                            ∃∃b1. b = c & F = ❴b1❵#j.
#j #c #b #F #H
elim (boolean_inv_vref … H) -H #H0 #H
elim (carrier_inv_vref … H) -H /2 width=2/
qed-.

lemma booleanized_inv_abst: ∀U,c,b,F. ❴b❵⇕ F = ❴c❵𝛌.U →
                            ∃∃b1,T. b = c & ❴b❵⇕T = U & F = ❴b1❵𝛌.T.
#U #c #b #F #H
elim (boolean_inv_abst … H) -H #C #H0 #H1 #H
elim (carrier_inv_abst … H) -H #b1 #U1 #H3 destruct /2 width=4/
qed-.

lemma booleanized_inv_appl: ∀W,U,c,b,F. ❴b❵⇕ F = ❴c❵@W.U →
                            ∃∃b1,V,T. b = c & ❴b❵⇕V = W & ❴b❵⇕T = U & F = ❴b1❵@V.T.
#W #U #c #b #F #H
elim (boolean_inv_appl … H) -H #D #C #H0 #H1 #H2 #H
elim (carrier_inv_appl … H) -H #b1 #W1 #U1 #H3 #H4 destruct /2 width=6/
qed-.

lemma booleanized_booleanized: ∀c,b,F. ❴b❵⇕ ❴c❵⇕ F = ❴b❵⇕ F.
normalize //
qed.

lemma booleanized_lift: ∀b,h,F,d. ❴b❵⇕ ↑[d, h] F = ↑[d, h] ❴b❵⇕ F.
normalize //
qed.

lemma booleanized_dsubst: ∀b,G,F,d. ❴b❵⇕ [d ↙ G] F = [d ↙ ❴b❵⇕ G] ❴b❵⇕ F.
normalize //
qed.
