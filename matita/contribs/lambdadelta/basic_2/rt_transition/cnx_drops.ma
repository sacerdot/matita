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

include "basic_2/relocation/lifts_tdeq.ma".
include "basic_2/rt_transition/cpx_drops.ma".
include "basic_2/rt_transition/cnx.ma".

(* NORMAL TERMS FOR UNCOUNTED CONTEXT-SENSITIVE PARALLEL RT-TRANSITION ******)

(* Properties with generic slicing ******************************************)

lemma cnx_lref_atom: ∀h,o,G,L,i. ⬇*[i] L ≘ ⋆ → ⦃G, L⦄ ⊢ ⬈[h, o] 𝐍⦃#i⦄.
#h #o #G #L #i #Hi #X #H elim (cpx_inv_lref1_drops … H) -H // *
#I #K #V1 #V2 #HLK lapply (drops_mono … Hi … HLK) -L #H destruct
qed.

lemma cnx_lref_unit: ∀h,o,I,G,L,K,i. ⬇*[i] L ≘ K.ⓤ{I} → ⦃G, L⦄ ⊢ ⬈[h, o] 𝐍⦃#i⦄.
#h #o #I #G #L #K #i #HLK #X #H elim (cpx_inv_lref1_drops … H) -H // *
#Z #Y #V1 #V2 #HLY lapply (drops_mono … HLK … HLY) -L #H destruct
qed.

(* Basic_2A1: includes: cnx_lift *)
lemma cnx_lifts: ∀h,o,G. d_liftable1 … (cnx h o G).
#h #o #G #K #T #HT #b #f #L #HLK #U #HTU #U0 #H
elim (cpx_inv_lifts_sn … H … HLK … HTU) -b -L #T0 #HTU0 #HT0
lapply (HT … HT0) -G -K /2 width=6 by tdeq_lifts_bi/
qed-.

(* Inversion lemmas with generic slicing ************************************)

(* Basic_2A1: was: cnx_inv_delta *)
lemma cnx_inv_lref_pair: ∀h,o,I,G,L,K,V,i. ⬇*[i] L ≘ K.ⓑ{I}V → ⦃G, L⦄ ⊢ ⬈[h, o] 𝐍⦃#i⦄ → ⊥.
#h #o #I #G #L #K #V #i #HLK #H
elim (lifts_total V (𝐔❴↑i❵)) #W #HVW
lapply (H W ?) -H /2 width=7 by cpx_delta_drops/ -HLK
#H lapply (tdeq_inv_lref1 … H) -H #H destruct
/2 width=5 by lifts_inv_lref2_uni_lt/
qed-.

(* Basic_2A1: includes: cnx_inv_lift *)
lemma cnx_inv_lifts: ∀h,o,G. d_deliftable1 … (cnx h o G).
#h #o #G #L #U #HU #b #f #K #HLK #T #HTU #T0 #H
elim (cpx_lifts_sn … H … HLK … HTU) -b -K #U0 #HTU0 #HU0
lapply (HU … HU0) -G -L /2 width=6 by tdeq_inv_lifts_bi/
qed-.
