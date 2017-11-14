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

include "basic_2/static/lfdeq_lfdeq.ma".
include "basic_2/static/ffdeq.ma".

(* DEGREE-BASED EQUIVALENCE FOR CLOSURES ON REFERRED ENTRIES ****************)

(* Main properties **********************************************************)

theorem ffdeq_trans: ∀h,o. tri_transitive … (ffdeq h o).
#h #o #G1 #G #L1 #L #T1 #T * -G -L -T
#L #HL1 #G2 #L2 #T2 * -G2 -L2 -T2 /3 width=3 by ffdeq_intro, lfdeq_trans/
qed-.

theorem ffdeq_canc_sn: ∀h,o,G,G1,G2,L,L1,L2,T,T1,T2.
                       ⦃G, L, T⦄ ≛[h, o] ⦃G1, L1, T1⦄→ ⦃G, L, T⦄ ≛[h, o] ⦃G2, L2, T2⦄ → ⦃G1, L1, T1⦄ ≛[h, o] ⦃G2, L2, T2⦄.
/3 width=5 by ffdeq_trans, ffdeq_sym/ qed-.

theorem ffdeq_canc_dx: ∀h,o,G1,G2,G,L1,L2,L,T1,T2,T.
                       ⦃G1, L1, T1⦄ ≛[h, o] ⦃G, L, T⦄ → ⦃G2, L2, T2⦄ ≛[h, o] ⦃G, L, T⦄ → ⦃G1, L1, T1⦄ ≛[h, o] ⦃G2, L2, T2⦄.
/3 width=5 by ffdeq_trans, ffdeq_sym/ qed-.
