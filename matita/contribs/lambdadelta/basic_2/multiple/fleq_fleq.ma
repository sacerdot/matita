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

include "basic_2/multiple/lleq_lleq.ma".
include "basic_2/multiple/fleq.ma".

(* LAZY EQUIVALENCE FOR CLOSURES  *******************************************)

(* Main properties **********************************************************)

theorem fleq_trans: ∀d. tri_transitive … (fleq d).
#d #G1 #G #L1 #L #T1 #T * -G -L -T
#L #HT1 #G2 #L2 #T2 * -G2 -L2 -T2
/3 width=3 by lleq_trans, fleq_intro/
qed-.

theorem fleq_canc_sn: ∀G,G1,G2,L,L1,L2,T,T1,T2,d.
                      ⦃G, L, T⦄ ≡[d] ⦃G1, L1, T1⦄→ ⦃G, L, T⦄ ≡[d] ⦃G2, L2, T2⦄ → ⦃G1, L1, T1⦄ ≡[d] ⦃G2, L2, T2⦄.
/3 width=5 by fleq_trans, fleq_sym/ qed-.

theorem fleq_canc_dx: ∀G1,G2,G,L1,L2,L,T1,T2,T,d.
                      ⦃G1, L1, T1⦄ ≡[d] ⦃G, L, T⦄ → ⦃G2, L2, T2⦄ ≡[d] ⦃G, L, T⦄ → ⦃G1, L1, T1⦄ ≡[d] ⦃G2, L2, T2⦄.
/3 width=5 by fleq_trans, fleq_sym/ qed-.
