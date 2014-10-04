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

include "basic_2/notation/relations/lazybtpredstarproper_8.ma".
include "basic_2/reduction/fpb.ma".
include "basic_2/computation/fpbs.ma".

(* "QRST" PROPER PARALLEL COMPUTATION FOR CLOSURES **************************)

definition fpbg: ∀h. sd h → tri_relation genv lenv term ≝
                 λh,g,G1,L1,T1,G2,L2,T2.
                 ∃∃G,L,T. ⦃G1, L1, T1⦄ ≻[h, g] ⦃G, L, T⦄ & ⦃G, L, T⦄ ≥[h, g] ⦃G2, L2, T2⦄.

interpretation "'qrst' proper parallel computation (closure)"
   'LazyBTPRedStarProper h g G1 L1 T1 G2 L2 T2 = (fpbg h g G1 L1 T1 G2 L2 T2).

(* Basic properties *********************************************************)

lemma fpb_fpbg: ∀h,g,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ≻[h, g] ⦃G2, L2, T2⦄ →
                ⦃G1, L1, T1⦄ >≡[h, g] ⦃G2, L2, T2⦄.
/2 width=5 by ex2_3_intro/ qed.

lemma fpbg_fpbq_trans: ∀h,g,G1,G,G2,L1,L,L2,T1,T,T2.
                       ⦃G1, L1, T1⦄ >≡[h, g] ⦃G, L, T⦄ → ⦃G, L, T⦄ ≽[h, g] ⦃G2, L2, T2⦄ →
                       ⦃G1, L1, T1⦄ >≡[h, g] ⦃G2, L2, T2⦄.
#h #g #G1 #G #G2 #L1 #L #L2 #T1 #T #T2 *
/3 width=9 by fpbs_strap1, ex2_3_intro/
qed-.
