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

include "basic_2/notation/relations/btpredstaralt_8.ma".
include "basic_2/computation/fpbs_fpbs.ma".

(* "BIG TREE" PARALLEL COMPUTATION FOR CLOSURES *****************************)

(* Note: alternative definition of fpbs *)
definition fpbsa: ∀h. sd h → tri_relation genv lenv term ≝
                  λh,g,G1,L1,T1,G2,L2,T2.
                  ∃∃L,T. ⦃G1, L1, T1⦄ ⊃* ⦃G2, L, T⦄ & ⦃G2, L⦄ ⊢ T ➡*[h, g] T2 & ⦃G2, L⦄ ⊢ ➡*[h, g] L2.

interpretation "'big tree' parallel computation (closure) alternative"
   'BTPRedStarAlt h g G1 L1 T1 G2 L2 T2 = (fpbsa h g G1 L1 T1 G2 L2 T2).

(* Main inversion lemmas ****************************************************)

theorem fpbsa_inv_fpbs: ∀h,g,G1,G2,L1,L2,T1,T2.
                        ⦃G1, L1, T1⦄ ≥≥[h, g] ⦃G2, L2, T2⦄ → ⦃G1, L1, T1⦄ ≥[h, g] ⦃G2, L2, T2⦄.
#h #g #G1 #G2 #L1 #L2 #T1 #T2 * 
/4 width=5 by fpbs_trans, fsups_fpbs, cpxs_fpbs, lpxs_fpbs/
qed-.
