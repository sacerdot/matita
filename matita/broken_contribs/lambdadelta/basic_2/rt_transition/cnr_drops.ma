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

include "basic_2/rt_transition/cpr_drops.ma".
include "basic_2/rt_transition/cnr.ma".

(* NORMAL TERMS FOR CONTEXT-SENSITIVE R-TRANSITION **************************)

(* Advanced properties ******************************************************)

(* Basic_1: was only: nf2_csort_lref *)
lemma cnr_lref_atom (h) (b) (G) (L):
      ∀i. ⇩*[b,𝐔❨i❩] L ≘ ⋆ → ❨G,L❩ ⊢ ➡𝐍[h,0] #i.
#h #b #G #L #i #Hi #X #H
elim (cpr_inv_lref1_drops … H) -H // * #K #V1 #V2 #HLK
lapply (drops_gen b … HLK) -HLK #HLK
lapply (drops_mono … Hi … HLK) -L #H destruct
qed.

(* Basic_1: was: nf2_lref_abst *)
lemma cnr_lref_abst (h) (G) (L):
      ∀K,V,i. ⇩[i] L ≘ K.ⓛV → ❨G,L❩ ⊢ ➡𝐍[h,0] #i.
#h #G #L #K #V #i #HLK #X #H
elim (cpr_inv_lref1_drops … H) -H // *
#K0 #V1 #V2 #HLK0 #_ #_
lapply (drops_mono … HLK … HLK0) -L #H destruct
qed.

lemma cnr_lref_unit (h) (I) (G) (L):
      ∀K,i. ⇩[i] L ≘ K.ⓤ[I] → ❨G,L❩ ⊢ ➡𝐍[h,0] #i.
#h #I #G #L #K #i #HLK #X #H
elim (cpr_inv_lref1_drops … H) -H // *
#K0 #V1 #V2 #HLK0 #_ #_
lapply (drops_mono … HLK … HLK0) -L #H destruct
qed.

(* Properties with generic relocation ***************************************)

(* Basic_1: was: nf2_lift *)
(* Basic_2A1: uses: cnr_lift *)
lemma cnr_lifts (h) (G): d_liftable1 … (cnr h 0 G).
#h #G #K #T #HT #b #f #L #HLK #U #HTU #U0 #H
elim (cpm_inv_lifts_sn … H … HLK … HTU) -b -L #T0 #HTU0 #HT0
lapply (HT … HT0) -G -K #H destruct /2 width=4 by lifts_mono/
qed-.

(* Advanced inversion lemmas ************************************************)

(* Basic_2A1: was: cnr_inv_delta *)
lemma cnr_inv_lref_abbr (h) (G) (L):
      ∀K,V,i. ⇩[i] L ≘ K.ⓓV → ❨G,L❩ ⊢ ➡𝐍[h,0] #i → ⊥.
#h #G #L #K #V #i #HLK #H
elim (lifts_total V 𝐔❨↑i❩) #W #HVW
lapply (H W ?) -H [ /3 width=6 by cpm_delta_drops/ ] -HLK #H destruct
elim (lifts_inv_lref2_uni_lt … HVW) -HVW //
qed-.

(* Inversion lemmas with generic relocation *********************************)

(* Note: this was missing in Basic_1 *)
(* Basic_2A1: uses: cnr_inv_lift *)
lemma cnr_inv_lifts (h) (G): d_deliftable1 … (cnr h 0 G).
#h #G #L #U #HU #b #f #K #HLK #T #HTU #T0 #H
elim (cpm_lifts_sn … H … HLK … HTU) -b -K #U0 #HTU0 #HU0
lapply (HU … HU0) -G -L #H destruct /2 width=4 by lifts_inj/
qed-.
