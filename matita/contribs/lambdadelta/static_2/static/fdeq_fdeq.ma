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

include "static_2/static/rdeq_rdeq.ma".
include "static_2/static/fdeq.ma".

(* SORT-IRRELEVANT EQUIVALENCE FOR CLOSURES ON REFERRED ENTRIES *************)

(* Advanced properties ******************************************************)

lemma fdeq_sym: tri_symmetric … fdeq.
#G1 #G2 #L1 #L2 #T1 #T2 * -G1 -L1 -T1
/3 width=1 by fdeq_intro_dx, rdeq_sym, tdeq_sym/
qed-.

(* Main properties **********************************************************)

theorem fdeq_trans: tri_transitive … fdeq.
#G1 #G #L1 #L #T1 #T * -G -L -T
#L #T #HL1 #HT1 #G2 #L2 #T2 * -G2 -L2 -T2
/4 width=5 by fdeq_intro_sn, rdeq_trans, tdeq_rdeq_div, tdeq_trans/
qed-.

theorem fdeq_canc_sn: ∀G,G1,L,L1,T,T1. ⦃G, L, T⦄ ≛ ⦃G1, L1, T1⦄→
                      ∀G2,L2,T2. ⦃G, L, T⦄ ≛ ⦃G2, L2, T2⦄ → ⦃G1, L1, T1⦄ ≛ ⦃G2, L2, T2⦄.
/3 width=5 by fdeq_trans, fdeq_sym/ qed-.

theorem fdeq_canc_dx: ∀G1,G,L1,L,T1,T. ⦃G1, L1, T1⦄ ≛ ⦃G, L, T⦄ →
                      ∀G2,L2,T2. ⦃G2, L2, T2⦄ ≛ ⦃G, L, T⦄ → ⦃G1, L1, T1⦄ ≛ ⦃G2, L2, T2⦄.
/3 width=5 by fdeq_trans, fdeq_sym/ qed-.

(* Main inversion lemmas with degree-based equivalence on terms *************)

theorem fdeq_tdneq_repl_dx: ∀G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ≛ ⦃G2, L2, T2⦄ →
                            ∀U1,U2. ⦃G1, L1, U1⦄ ≛ ⦃G2, L2, U2⦄ →
                            (T2 ≛ U2 → ⊥) → (T1 ≛ U1 → ⊥).
#G1 #G2 #L1 #L2 #T1 #T2 #HT #U1 #U2 #HU #HnTU2 #HTU1
elim (fdeq_inv_gen_sn … HT) -HT #_ #_ #HT
elim (fdeq_inv_gen_sn … HU) -HU #_ #_ #HU
/3 width=5 by tdeq_repl/
qed-.
