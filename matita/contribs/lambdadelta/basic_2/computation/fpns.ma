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

include "basic_2/notation/relations/btpredsnstar_8.ma".
include "basic_2/substitution/lleq.ma".
include "basic_2/computation/lpxs.ma".

(* PARALLEL COMPUTATION FOR "BIG TREE" NORMAL FORMS *************************)

inductive fpns (h) (g) (G) (L1) (T): relation3 genv lenv term ≝
| fpns_intro: ∀L2. ⦃G, L1⦄ ⊢ ➡*[h, g] L2 → L1 ⋕[T, 0] L2 → fpns h g G L1 T G L2 T
.

interpretation
   "computation for 'big tree' normal forms (closure)"
   'BTPRedSnStar h g G1 L1 T1 G2 L2 T2 = (fpns h g G1 L1 T1 G2 L2 T2).

(* Basic_properties *********************************************************)

lemma fpns_refl: ∀h,g. tri_reflexive … (fpns h g).
/2 width=1 by fpns_intro/ qed.

(* Basic inversion lemmas ***************************************************) 

lemma fpns_inv_gen: ∀h,g,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊢ ⋕➡*[h, g] ⦃G2, L2, T2⦄ →
                    ∧∧ G1 = G2 & ⦃G1, L1⦄ ⊢ ➡*[h, g] L2 & L1 ⋕[T1, 0] L2 & T1 = T2.
#h #g #G1 #G2 #L1 #L2 #T1 #T2 * -G2 -L2 -T2 /2 width=1 by and4_intro/
qed-.
