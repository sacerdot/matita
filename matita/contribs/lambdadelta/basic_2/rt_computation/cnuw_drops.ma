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

include "static_2/relocation/lifts_tweq.ma".
include "basic_2/rt_computation/cpms_drops.ma".
include "basic_2/rt_computation/cnuw.ma".

(* NORMAL TERMS FOR T-UNUNBOUND WHD RT-TRANSITION ***************************)

(* Properties with generic relocation ***************************************)

lemma cnuw_lifts (h) (G): d_liftable1 … (cnuw h G).
#h #G #K #T #HT #b #f #L #HLK #U #HTU #n #U0 #H
elim (cpms_inv_lifts_sn … H … HLK … HTU) -b -L #T0 #HTU0 #HT0
lapply (HT … HT0) -G -K /2 width=6 by tweq_lifts_bi/
qed-.

(* Inversion lemmas with generic relocation *********************************)

lemma cnuw_inv_lifts (h) (G): d_deliftable1 … (cnuw h G).
#h #G #L #U #HU #b #f #K #HLK #T #HTU #n #T0 #H
elim (cpms_lifts_sn … H … HLK … HTU) -b -K #U0 #HTU0 #HU0
lapply (HU … HU0) -G -L /2 width=6 by tweq_inv_lifts_bi/
qed-.

(* Advanced properties ******************************************************)

lemma cnuw_lref (h) (I) (G) (L):
      ∀i. ❪G,L❫ ⊢ ➡𝐍𝐖*[h] #i → ❪G,L.ⓘ[I]❫ ⊢ ➡𝐍𝐖*[h] #↑i.
#h #I #G #L #i #Hi #n #X2 #H
elim (cpms_inv_lref_sn … H) -H *
[ #H #_ destruct //
| #T2 #HT2 #HTX2
  lapply (Hi … HT2) -Hi -HT2 #H
  lapply (tweq_inv_lref_sn … H) -H #H destruct
  lapply (lifts_inv_lref1_uni … HTX2) -HTX2 #H destruct //
]
qed.

lemma cnuw_atom_drops (h) (b) (G) (L):
      ∀i. ⇩*[b,𝐔❨i❩] L ≘ ⋆ → ❪G,L❫ ⊢ ➡𝐍𝐖*[h] #i.
#h #b #G #L #i #Hi #n #X #H
elim (cpms_inv_lref1_drops … H) -H * [ // || #m ] #K #V1 #V2 #HLK
lapply (drops_gen b … HLK) -HLK #HLK
lapply (drops_mono … Hi … HLK) -L #H destruct
qed.

lemma cnuw_unit_drops (h) (I) (G) (L):
      ∀K,i. ⇩*[i] L ≘ K.ⓤ[I] → ❪G,L❫ ⊢ ➡𝐍𝐖*[h] #i.
#h #I #G #L #K #i #HLK #n #X #H
elim (cpms_inv_lref1_drops … H) -H * [ // || #m ] #Y #V1 #V2 #HLY
lapply (drops_mono … HLK … HLY) -L #H destruct
qed.
