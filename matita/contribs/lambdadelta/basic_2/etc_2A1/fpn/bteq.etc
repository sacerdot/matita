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

include "basic_2/notation/relations/bteq_6.ma".
include "basic_2/grammar/lenv_length.ma".
include "basic_2/grammar/genv.ma".

(* EQUIVALENT "BIG TREE" NORMAL FORMS ***************************************)

definition bteq: tri_relation genv lenv term ≝
                 λG1,L1,T1,G2,L2,T2.
                 ∧∧ G1 = G2 & |L1| = |L2| & T1 = T2.

interpretation
   "equivalent 'big tree' normal forms (closure)"
   'BTEq G1 L1 T1 G2 L2 T2 = (bteq G1 L1 T1 G2 L2 T2).

(* Basic_properties *********************************************************)

lemma bteq_refl: tri_reflexive … bteq.
/2 width=1 by and3_intro/ qed.

lemma bteq_sym: tri_symmetric … bteq.
#G1 #G2 #L1 #L2 #T1 #T2 * //
qed-.

lemma bteq_dec: ∀G1,G2,L1,L2,T1,T2. Decidable (⦃G1, L1, T1⦄ ⋕ ⦃G2, L2, T2⦄).
#G1 #G2 #L1 #L2 #T1 #T2 elim (genv_eq_dec G1 G2)
#H1G [2: @or_intror * #H2G #H2L #H2T destruct /2 width=1 by/ ]
elim (eq_nat_dec (|L1|) (|L2|))
#H1L [2: @or_intror * #H2G #H2L #H2T destruct /2 width=1 by/ ]
elim (term_eq_dec T1 T2)
#H1T [2: @or_intror * #H2G #H2L #H2T destruct /2 width=1 by/ ]
/3 width=1 by and3_intro, or_introl/
qed-.
