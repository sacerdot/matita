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

include "basic_2/substitution/cpye_lift.ma".
include "basic_2/reduction/lpx_cpye.ma".
include "basic_2/computation/cpxs_cpxs.ma".
include "basic_2/computation/lpxs.ma".

(* SN EXTENDED PARALLEL COMPUTATION ON LOCAL ENVIRONMENTS *******************)

(* Forward lemmas on evaluation for extended substitution *******************)

lemma cpx_cpye_fwd_lpxs: ∀h,g,G,L1,L2. ⦃G, L1⦄ ⊢ ➡*[h, g] L2 →
                         ∀T1,T2. ⦃G, L1⦄ ⊢ T1 ➡[h, g] T2 →
                         ∀U1,d,e. ⦃G, L1⦄ ⊢ T1 ▶*[d, e] 𝐍⦃U1⦄ →
                         ∀U2. ⦃G, L2⦄ ⊢ T2 ▶*[d, e] 𝐍⦃U2⦄ →
                         ⦃G, L1⦄ ⊢ U1 ➡*[h, g] U2.
#h #g #G #L1 #L2 #H @(lpxs_ind_dx … H) -L1
[ /3 width=9 by cpx_cpxs, cpx_cpye_fwd_lpx/
| #L1 #L #HL1 #_ #IHL2 #T1 #T2 #HT12 #U1 #d #e #HTU1 #U2 #HTU2
  elim (cpye_total G L T2 d e) #X2 #HTX2
  lapply (cpx_cpye_fwd_lpx … HT12 … HL1 … HTU1 … HTX2) -T1
  /4 width=9 by lpx_cpxs_trans, cpxs_strap2/ (**) (* full auto too long: 41s *)
]
qed-.
