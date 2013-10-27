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

include "basic_2/notation/relations/fleq_8.ma".
include "basic_2/computation/lpxs.ma".

(* EQUIVALENT "BIG TREE" NORMAL FORMS ***************************************)

(* Note: this definition works but is not symmetric nor decidable *)
definition fleq: ∀h. sd h → tri_relation genv lenv term ≝
                 λh,g,G1,L1,T1,G2,L2,T2.
                 ∧∧ G1 = G2 & ⦃G1, L1⦄ ⊢ ➡*[h, g] L2 & T1 = T2.

interpretation
   "equivalent 'big tree' normal forms (closure)"
   'FLEq h g G1 L1 T1 G2 L2 T2 = (fleq h g G1 L1 T1 G2 L2 T2).

(* Basic_properties *********************************************************)

lemma fleq_refl: ∀h,g. tri_reflexive … (fleq h g).
/2 width=1 by and3_intro/ qed.
