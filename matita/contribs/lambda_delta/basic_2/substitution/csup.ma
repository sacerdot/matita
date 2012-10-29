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

include "basic_2/substitution/ldrop.ma".

(* SUPCLOSURE ***************************************************************)

inductive csup: bi_relation lenv term ≝
| csup_lref   : ∀I,L,K,V,i. ⇩[0, i] L ≡ K.ⓑ{I}V → csup L (#i) K V
| csup_bind_sn: ∀a,I,L,V,T. csup L (ⓑ{a,I}V.T) L V
| csup_bind_dx: ∀a,I,L,V,T. csup L (ⓑ{a,I}V.T) (L.ⓑ{I}V) T 
| csup_flat_sn: ∀I,L,V,T.   csup L (ⓕ{I}V.T) L V
| csup_flat_dx: ∀I,L,V,T.   csup L (ⓕ{I}V.T) L T
.

interpretation
   "structural predecessor (closure)"
   'SupTerm L1 T1 L2 T2 = (csup L1 T1 L2 T2).

(* Basic forward lemmas *****************************************************)

lemma csup_fwd_cw: ∀L1,L2,T1,T2. ⦃L1, T1⦄ > ⦃L2, T2⦄ → #{L2, T2} < #{L1, T1}.
#L1 #L2 #T1 #T2 * -L1 -L2 -T1 -T2 /width=1/ /2 width=4 by ldrop_pair2_fwd_cw/
qed-.
