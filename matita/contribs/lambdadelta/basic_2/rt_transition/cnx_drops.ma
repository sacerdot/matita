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

include "basic_2/rt_transition/cpx_drops.ma".
include "basic_2/rt_transition/cnx.ma".

(* NORMAL TERMS FOR UNCOUNTED CONTEXT-SENSITIVE PARALLEL RT-TRANSITION ******)

(* Properties with generic slicing ******************************************)

lemma cnx_lref_atom: ∀h,o,G,L,i. ⬇*[i] L ≡ ⋆ → ⦃G, L⦄ ⊢ ⬈[h, o] 𝐍⦃#i⦄.
#h #o #G #L #i #Hi #X #H elim (cpx_inv_lref1_drops … H) -H // *
#I #K #V1 #V2 #HLK lapply (drops_mono … Hi … HLK) -L #H destruct
qed.

(* Inversion lemmas with generic slicing ************************************)

(* Basic_2A1: was: cnx_inv_delta *)
lemma cnx_inv_lref_pair: ∀h,o,I,G,L,K,V,i. ⬇*[i] L ≡ K.ⓑ{I}V → ⦃G, L⦄ ⊢ ⬈[h, o] 𝐍⦃#i⦄ → ⊥.
#h #o #I #G #L #K #V #i #HLK #H
elim (lifts_total V (𝐔❴⫯i❵)) #W #HVW
lapply (H W ?) -H /2 width=7 by cpx_delta_drops/ -HLK
#H lapply (tdeq_inv_lref1 … H) -H #H destruct
/2 width=5 by lifts_inv_lref2_uni_lt/
qed-.

(*
(* Relocation properties ****************************************************)

lemma cnx_lift: ∀h,o,G,L0,L,T,T0,c,l,k. ⦃G, L⦄ ⊢ ➡[h, o] 𝐍⦃T⦄ → ⬇[c, l, k] L0 ≡ L →
                ⬆[l, k] T ≡ T0 → ⦃G, L0⦄ ⊢ ➡[h, o] 𝐍⦃T0⦄.
#h #o #G #L0 #L #T #T0 #c #l #k #HLT #HL0 #HT0 #X #H
elim (cpx_inv_lift1 … H … HL0 … HT0) -L0 #T1 #HT10 #HT1
<(HLT … HT1) in HT0; -L #HT0
>(lift_mono … HT10 … HT0) -T1 -X //
qed.

lemma cnx_inv_lift: ∀h,o,G,L0,L,T,T0,c,l,k. ⦃G, L0⦄ ⊢ ➡[h, o] 𝐍⦃T0⦄ → ⬇[c, l, k] L0 ≡ L →
                    ⬆[l, k] T ≡ T0 → ⦃G, L⦄ ⊢ ➡[h, o] 𝐍⦃T⦄.
#h #o #G #L0 #L #T #T0 #c #l #k #HLT0 #HL0 #HT0 #X #H
elim (lift_total X l k) #X0 #HX0
lapply (cpx_lift … H … HL0 … HT0 … HX0) -L #HTX0
>(HLT0 … HTX0) in HX0; -L0 -X0 #H
>(lift_inj … H … HT0) -T0 -X -l -k //
qed-.
*)
