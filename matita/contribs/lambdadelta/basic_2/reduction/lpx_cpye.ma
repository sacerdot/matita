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

include "basic_2/substitution/cpye_cpye.ma".
include "basic_2/reduction/lpx_cpys.ma".

axiom cpx_cpys_conf_lpx: ∀h,g,G,d,e.
                         ∀L0,T0,T1. ⦃G, L0⦄ ⊢ T0 ➡[h, g] T1 → ∀L1. ⦃G, L0⦄ ⊢ ➡[h, g] L1 →
                         ∀T2. ⦃G, L0⦄ ⊢ T0 ▶*[d, e] T2 →
                         ∃∃T. ⦃G, L1⦄ ⊢ T1 ▶*[d, e] T & ⦃G, L0⦄ ⊢ T2 ➡[h, g] T.

(* SN EXTENDED PARALLEL REDUCTION ON LOCAL ENVIRONMENTS *********************)

(* Forward lemmas on evaluation for extended substitution *******************)

lemma cpx_cpys_cpye_fwd_lpx: ∀h,g,G,L1,T1,T2. ⦃G, L1⦄ ⊢ T1 ➡[h, g] T2 →
                             ∀L2. ⦃G, L1⦄ ⊢ ➡[h, g] L2 →
                             ∀U1,d,e. ⦃G, L1⦄ ⊢ T1 ▶*[d, e] U1 →
                             ∀U2. ⦃G, L2⦄ ⊢ T2 ▶*[d, e] 𝐍⦃U2⦄ →
                             ⦃G, L1⦄ ⊢ U1 ➡[h, g] U2.
#h #g #G #L1 #T1 #T2 #HT12 #L2 #HL12 #U1 #d #e #HTU1
elim (cpx_cpys_conf_lpx … HT12 … HL12 … HTU1) -T1
/3 width=9 by cpx_cpys_trans_lpx, cpye_cpys_conf/
qed-.

lemma cpx_cpye_fwd_lpx: ∀h,g,G,L1,T1,T2. ⦃G, L1⦄ ⊢ T1 ➡[h, g] T2 →
                        ∀L2. ⦃G, L1⦄ ⊢ ➡[h, g] L2 →
                        ∀U1,d,e. ⦃G, L1⦄ ⊢ T1 ▶*[d, e] 𝐍⦃U1⦄ →
                        ∀U2. ⦃G, L2⦄ ⊢ T2 ▶*[d, e] 𝐍⦃U2⦄ →
                        ⦃G, L1⦄ ⊢ U1 ➡[h, g] U2.
#h #g #G #L1 #T1 #T2 #HT12 #L2 #HL12 #U1 #d #e *
/2 width=9 by cpx_cpys_cpye_fwd_lpx/
qed-.
