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

include "basic_2/reduction/cpx_cpys.ma".
include "basic_2/computation/lpxs_cpye.ma".
include "basic_2/computation/csx_alt.ma".
include "basic_2/computation/lsx_lpxs.ma".

(* SN EXTENDED STRONGLY NORMALIZING LOCAL ENVIRONMENTS **********************)

(* Advanced properties ******************************************************)

axiom lpxs_cpye_csx_lsx: ∀h,g,G,L1,U. ⦃G, L1⦄ ⊢ ⬊*[h, g] U →
                         ∀L2. ⦃G, L1⦄ ⊢ ➡*[h, g] L2 → ∀T.  ⦃G, L2⦄ ⊢ T ▶*[0, ∞] 𝐍⦃U⦄ →
                         G ⊢ ⋕⬊*[h, g, T] L2.
(*
#h #g #G #L1 #U #H @(csx_ind_alt … H) -U
#U0 #_ #IHU0 #L0 #HL10 #T #H0 @lsx_intro
#L2 #HL02 #HnT elim (cpye_total G L2 T 0 (∞))
#U2 #H2 elim (eq_term_dec U0 U2) #H destruct
[ -IHU0
| -HnT /4 width=9 by lpxs_trans, lpxs_cpxs_trans, cpx_cpye_fwd_lpxs/
]
*)
(* Main properties **********************************************************)

lemma csx_lsx: ∀h,g,G,L,T. ⦃G, L⦄ ⊢ ⬊*[h, g] T → G ⊢ ⋕⬊*[h, g, T] L.
#h #g #G #L #T #HT elim (cpye_total G L T 0 (∞))
#U #HTU elim HTU
/4 width=5 by lpxs_cpye_csx_lsx, csx_cpx_trans, cpys_cpx/
qed.