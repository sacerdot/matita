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

include "static_2/relocation/lifts_theq.ma".
include "basic_2/rt_transition/cpm_drops.ma".
include "basic_2/rt_transition/cnh.ma".

(* NORMAL TERMS FOR HEAD T-UNUNBOUND RT-TRANSITION **************************)

(* Advanced properties ******************************************************)

lemma cnh_atom_drops (h) (b) (G) (L):
      ∀i. ⬇*[b,𝐔❴i❵] L ≘ ⋆ → ⦃G,L⦄ ⊢ ⥲[h] 𝐍⦃#i⦄.
#h #b #G #L #i #Hi #n #X #H
elim (cpm_inv_lref1_drops … H) -H * [ // || #m ] #K #V1 #V2 #HLK
lapply (drops_gen b … HLK) -HLK #HLK
lapply (drops_mono … Hi … HLK) -L #H destruct
qed.

lemma cnh_unit_drops (h) (I) (G) (L):
      ∀K,i. ⬇*[i] L ≘ K.ⓤ{I} → ⦃G,L⦄ ⊢ ⥲[h] 𝐍⦃#i⦄.
#h #I #G #L #K #i #HLK #n #X #H
elim (cpm_inv_lref1_drops … H) -H * [ // || #m ] #Y #V1 #V2 #HLY
lapply (drops_mono … HLK … HLY) -L #H destruct
qed.

(* Properties with generic relocation ***************************************)

lemma cnh_lifts (h) (G): d_liftable1 … (cnh h G).
#h #G #K #T #HT #b #f #L #HLK #U #HTU #n #U0 #H
elim (cpm_inv_lifts_sn … H … HLK … HTU) -b -L #T0 #HTU0 #HT0
lapply (HT … HT0) -G -K /2 width=6 by theq_lifts_bi/
qed-.

(* Inversion lemmas with generic relocation *********************************)

lemma cnh_inv_lifts (h) (G): d_deliftable1 … (cnh h G).
#h #G #L #U #HU #b #f #K #HLK #T #HTU #n #T0 #H
elim (cpm_lifts_sn … H … HLK … HTU) -b -K #U0 #HTU0 #HU0
lapply (HU … HU0) -G -L /2 width=6 by theq_inv_lifts_bi/
qed-.
