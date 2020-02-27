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

include "basic_2A/computation/lpxs_lpxs.ma".
include "basic_2A/computation/lsx_alt.ma".

(* SN EXTENDED STRONGLY NORMALIZING LOCAL ENVIRONMENTS **********************)

(* Advanced properties ******************************************************)

fact lsx_bind_lpxs_aux: ∀h,g,a,I,G,L1,V,l. G ⊢ ⬊*[h, g, V, l] L1 →
                        ∀Y,T. G ⊢ ⬊*[h, g, T, ↑l] Y →
                        ∀L2. Y = L2.ⓑ{I}V → ⦃G, L1⦄ ⊢ ➡*[h, g] L2 →
                        G ⊢ ⬊*[h, g, ⓑ{a,I}V.T, l] L2.
#h #g #a #I #G #L1 #V #l #H @(lsx_ind_alt … H) -L1
#L1 #HL1 #IHL1 #Y #T #H @(lsx_ind_alt … H) -Y
#Y #HY #IHY #L2 #H #HL12 destruct @lsx_intro_alt
#L0 #HL20 lapply (lpxs_trans … HL12 … HL20)
#HL10 #H elim (nlleq_inv_bind … H) -H [ -HL1 -IHY | -HY -IHL1 ]
[ #HnV elim (lleq_dec V L1 L2 l)
  [ #HV @(IHL1 … L0) /3 width=5 by lsx_lpxs_trans, lpxs_pair, lleq_canc_sn/ (**) (* full auto too slow *)
  | -HnV -HL10 /4 width=5 by lsx_lpxs_trans, lpxs_pair/
  ]
| /3 width=4 by lpxs_pair/
]
qed-.

lemma lsx_bind: ∀h,g,a,I,G,L,V,l. G ⊢ ⬊*[h, g, V, l] L →
                ∀T. G ⊢ ⬊*[h, g, T, ↑l] L.ⓑ{I}V →
                G ⊢ ⬊*[h, g, ⓑ{a,I}V.T, l] L.
/2 width=3 by lsx_bind_lpxs_aux/ qed.

lemma lsx_flat_lpxs: ∀h,g,I,G,L1,V,l. G ⊢ ⬊*[h, g, V, l] L1 →
                     ∀L2,T. G ⊢ ⬊*[h, g, T, l] L2 → ⦃G, L1⦄ ⊢ ➡*[h, g] L2 →
                     G ⊢ ⬊*[h, g, ⓕ{I}V.T, l] L2.
#h #g #I #G #L1 #V #l #H @(lsx_ind_alt … H) -L1
#L1 #HL1 #IHL1 #L2 #T #H @(lsx_ind_alt … H) -L2
#L2 #HL2 #IHL2 #HL12 @lsx_intro_alt
#L0 #HL20 lapply (lpxs_trans … HL12 … HL20)
#HL10 #H elim (nlleq_inv_flat … H) -H [ -HL1 -IHL2 | -HL2 -IHL1 ]
[ #HnV elim (lleq_dec V L1 L2 l)
  [ #HV @(IHL1 … L0) /3 width=3 by lsx_lpxs_trans, lleq_canc_sn/ (**) (* full auto too slow: 47s *)
  | -HnV -HL10 /3 width=4 by lsx_lpxs_trans/
  ]
| /3 width=1 by/
]
qed-.

lemma lsx_flat: ∀h,g,I,G,L,V,l. G ⊢ ⬊*[h, g, V, l] L →
                ∀T. G ⊢ ⬊*[h, g, T, l] L → G ⊢ ⬊*[h, g, ⓕ{I}V.T, l] L.
/2 width=3 by lsx_flat_lpxs/ qed.
