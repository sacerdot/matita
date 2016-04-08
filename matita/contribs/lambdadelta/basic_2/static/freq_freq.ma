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

include "basic_2/relocation/lreq_lreq.ma".
include "basic_2/relocation/frees_frees.ma".
include "basic_2/relocation/freq.ma".

(* RANGED EQUIVALENCE FOR CLOSURES  *****************************************)

(* Main properties **********************************************************)

theorem freq_trans: tri_transitive … freq.
#G1 #G #L1 #L #T1 #T * -G -L -T
#L #f1 #H1T11 #Hf1 #G2 #L2 #T2 * -G2 -L2 -T2 #L2 #f2 #HT12 #Hf2
lapply (frees_lreq_conf … H1T11 … Hf1) #HT11
lapply (frees_mono … HT12 … HT11) -HT11 -HT12
/4 width=7 by fleq_intro, lreq_eq_repl_back, lreq_trans/
qed-.

theorem freq_canc_sn: ∀G,G1,G2,L,L1,L2,T,T1,T2.
                      ⦃G, L, T⦄ ≡ ⦃G1, L1, T1⦄→ ⦃G, L, T⦄ ≡ ⦃G2, L2, T2⦄ → ⦃G1, L1, T1⦄ ≡ ⦃G2, L2, T2⦄.
/3 width=5 by freq_trans, freq_sym/ qed-.

theorem freq_canc_dx: ∀G1,G2,G,L1,L2,L,T1,T2,T.
                      ⦃G1, L1, T1⦄ ≡ ⦃G, L, T⦄ → ⦃G2, L2, T2⦄ ≡ ⦃G, L, T⦄ → ⦃G1, L1, T1⦄ ≡ ⦃G2, L2, T2⦄.
/3 width=5 by freq_trans, freq_sym/ qed-.
