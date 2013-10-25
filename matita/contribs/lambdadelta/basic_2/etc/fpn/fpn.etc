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

include "basic_2/notation/relations/predsn_8.ma".
include "basic_2/grammar/bteq.ma".
include "basic_2/reduction/lpx.ma".

(* ADJACENT "BIG TREE" NORMAL FORMS *****************************************)

definition fpn: ∀h. sd h → tri_relation genv lenv term ≝
                λh,g,G1,L1,T1,G2,L2,T2.
                ∧∧ G1 = G2 & ⦃G1, L1⦄ ⊢ ➡[h, g] L2 & T1 = T2.

interpretation
   "adjacent 'big tree' normal forms (closure)"
   'PRedSn h g G1 L1 T1 G2 L2 T2 = (fpn h g G1 L1 T1 G2 L2 T2).

(* Basic_properties *********************************************************)

lemma fpn_refl: ∀h,g. tri_reflexive … (fpn h g).
/2 width=1 by and3_intro/ qed.

(* Basic forward lemmas *****************************************************)

lemma fpn_fwd_bteq: ∀h,g,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊢➡[h, g] ⦃G2, L2, T2⦄ →
                    ⦃G1, L1, T1⦄ ⋕ ⦃G2, L2, T2⦄.
#h #g #G1 #G2 #L1 #L2 #T1 #T2 * /3 width=4 by lpx_fwd_length, and3_intro/
qed-.
