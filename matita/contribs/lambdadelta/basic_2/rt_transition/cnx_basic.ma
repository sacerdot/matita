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

include "static_2/relocation/lifts_teqx.ma".
include "basic_2/rt_transition/cpx_drops_basic.ma".
include "basic_2/rt_transition/cnx.ma".

(* NORMAL TERMS FOR UNBOUND CONTEXT-SENSITIVE PARALLEL RT-TRANSITION ********)

(* Advanced inversion lemmas ************************************************)

lemma cnx_inv_abbr_pos (h) (G) (L): ∀V,T.  ⦃G,L⦄ ⊢ ⬈[h] 𝐍⦃+ⓓV.T⦄ → ⊥.
#h #G #L #V #U1 #H
elim (cpx_subst h G (L.ⓓV) U1 … 0) [|*: /2 width=4 by drops_refl/ ] #U2 #T2 #HU12 #HTU2
elim (teqx_dec U1 U2) #HnU12 [ -HU12 | -HTU2 ]
[ elim (teqx_inv_lifts_dx … HnU12 … HTU2) -U2 #T1 #HTU1 #_ -T2
  lapply (H T1 ?) -H [ /2 width=3 by cpx_zeta/ ] #H
  /2 width=9 by teqx_lifts_inv_pair_sn/
| lapply (H (+ⓓV.U2) ?) -H [ /2 width=1 by cpx_bind/ ] -HU12 #H
  elim (teqx_inv_pair … H) -H #_ #_ /2 width=1 by/
]
qed-.
