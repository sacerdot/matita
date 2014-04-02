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

include "basic_2/computation/llpxs_llpxs.ma".
include "basic_2/computation/llsx_alt.ma".

(* SN EXTENDED STRONGLY NORMALIZING LOCAL ENVIRONMENTS **********************)

(* Advanced properties ******************************************************)

fact llsx_bind_llpxs_aux: ∀h,g,a,I,G,L1,V,d. G ⊢ ⋕⬊*[h, g, V, d] L1 →
                          ∀Y,T. G ⊢ ⋕⬊*[h, g, T, ⫯d] Y →
                          ∀L2. Y = L2.ⓑ{I}V → ⦃G, L1⦄ ⊢ ➡*[h, g, ⓑ{a,I}V.T, d] L2 →
                          G ⊢ ⋕⬊*[h, g, ⓑ{a,I}V.T, d] L2.
#h #g #a #I #G #L1 #V #d #H @(llsx_ind_alt … H) -L1
#L1 #HL1 #IHL1 #Y #T #H @(llsx_ind_alt … H) -Y
#Y #HY #IHY #L2 #H #HL12 destruct @llsx_intro_alt
#L0 #HL20 lapply (llpxs_fwd_bind_dx … HL20)
lapply (llpxs_trans … HL12 … HL20)
#HL10 #HT #H elim (nlleq_inv_bind … H) -H [ -HL1 -IHY | -HY -IHL1 ]
[ #HnV elim (lleq_dec V L1 L2 d)
  [  -HL20 #HV @(IHL1 … L0)
     /3 width=4 by llsx_llpxs_trans, llpxs_fwd_bind_sn, lleq_canc_sn/ (**) (* full auto too slow *)
  | -HnV -HL10
     /3 width=4 by llsx_llpxs_trans, llpxs_fwd_bind_sn/
  ]
| /3 width=4 by/
]
qed-.

lemma llsx_bind: ∀h,g,a,I,G,L,V,d. G ⊢ ⋕⬊*[h, g, V, d] L →
                 ∀T. G ⊢ ⋕⬊*[h, g, T, ⫯d] L.ⓑ{I}V →
                 G ⊢ ⋕⬊*[h, g, ⓑ{a,I}V.T, d] L.
/2 width=3 by llsx_bind_llpxs_aux/ qed.

lemma llsx_flat_llpxs: ∀h,g,I,G,L1,V,d. G ⊢ ⋕⬊*[h, g, V, d] L1 →
                       ∀L2,T. G ⊢ ⋕⬊*[h, g, T, d] L2 → ⦃G, L1⦄ ⊢ ➡*[h, g, ⓕ{I}V.T, d] L2 →
                       G ⊢ ⋕⬊*[h, g, ⓕ{I}V.T, d] L2.
#h #g #I #G #L1 #V #d #H @(llsx_ind_alt … H) -L1
#L1 #HL1 #IHL1 #L2 #T #H @(llsx_ind_alt … H) -L2
#L2 #HL2 #IHL2 #HL12 @llsx_intro_alt
#L0 #HL20 lapply (llpxs_fwd_flat_dx … HL20)
lapply (llpxs_trans … HL12 … HL20)
#HL10 #HT #H elim (nlleq_inv_flat … H) -H [ -HL1 -IHL2 | -HL2 -IHL1 ]
[ #HnV elim (lleq_dec V L1 L2 d)
  [ #HV @(IHL1 … L0) /3 width=3 by llsx_llpxs_trans, llpxs_fwd_flat_sn, lleq_canc_sn/ (**) (* full auto too slow: 47s *)
  | -HnV -HL10 /3 width=4 by llsx_llpxs_trans, llpxs_fwd_flat_sn/
  ]
| /3 width=1 by/
]
qed-.

lemma llsx_flat: ∀h,g,I,G,L,V,d. G ⊢ ⋕⬊*[h, g, V, d] L →
                 ∀T. G ⊢ ⋕⬊*[h, g, T, d] L → G ⊢ ⋕⬊*[h, g, ⓕ{I}V.T, d] L.
/2 width=3 by llsx_flat_llpxs/ qed.
