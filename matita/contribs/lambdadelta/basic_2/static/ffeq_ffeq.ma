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

include "basic_2/static/lfeq_lfeq.ma".
include "basic_2/static/ffeq.ma".

(* EQUIVALENCE FOR CLOSURES ON REFERRED ENTRIES *****************************)

(* Main properties **********************************************************)

theorem ffeq_trans: tri_transitive … ffeq.
#G1 #G #L1 #L #T1 #T * -G -L -T
#L #HL1 #G2 #L2 #T2 * -G2 -L2 -T2 /3 width=3 by fleq_intro, lfeq_trans/
qed-.

theorem ffeq_canc_sn: ∀G,G1,G2,L,L1,L2,T,T1,T2.
                      ⦃G, L, T⦄ ≡ ⦃G1, L1, T1⦄→ ⦃G, L, T⦄ ≡ ⦃G2, L2, T2⦄ → ⦃G1, L1, T1⦄ ≡ ⦃G2, L2, T2⦄.
/3 width=5 by ffeq_trans, ffeq_sym/ qed-.

theorem ffeq_canc_dx: ∀G1,G2,G,L1,L2,L,T1,T2,T.
                      ⦃G1, L1, T1⦄ ≡ ⦃G, L, T⦄ → ⦃G2, L2, T2⦄ ≡ ⦃G, L, T⦄ → ⦃G1, L1, T1⦄ ≡ ⦃G2, L2, T2⦄.
/3 width=5 by ffeq_trans, ffeq_sym/ qed-.
