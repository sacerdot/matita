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

include "basic_2/rt_transition/cpg_drops.ma".
include "basic_2/rt_transition/cpx.ma".

(* UNBOUND CONTEXT-SENSITIVE PARALLEL RT-TRANSITION FOR TERMS ***************)

(* Advanced properties ******************************************************)

(* Basic_2A1: was: cpx_delta *)
lemma cpx_delta_drops: ∀h,I,G,L,K,V,V2,W2,i.
                       ⇩*[i] L ≘ K.ⓑ{I}V → ⦃G,K⦄ ⊢ V ⬈[h] V2 →
                       ⇧*[↑i] V2 ≘ W2 → ⦃G,L⦄ ⊢ #i ⬈[h] W2.
#h * #G #L #K #V #V2 #W2 #i #HLK *
/3 width=7 by cpg_ell_drops, cpg_delta_drops, ex_intro/
qed.

(* Advanced inversion lemmas ************************************************)

(* Basic_2A1: was: cpx_inv_atom1 *)
lemma cpx_inv_atom1_drops: ∀h,I,G,L,T2. ⦃G,L⦄ ⊢ ⓪{I} ⬈[h] T2 →
                           ∨∨ T2 = ⓪{I}
                            | ∃∃s. T2 = ⋆(⫯[h]s) & I = Sort s
                            | ∃∃J,K,V,V2,i. ⇩*[i] L ≘ K.ⓑ{J}V & ⦃G,K⦄ ⊢ V ⬈[h] V2 &
                                            ⇧*[↑i] V2 ≘ T2 & I = LRef i.
#h #I #G #L #T2 * #c #H elim (cpg_inv_atom1_drops … H) -H *
/4 width=9 by or3_intro0, or3_intro1, or3_intro2, ex4_5_intro, ex2_intro, ex_intro/
qed-.

(* Basic_2A1: was: cpx_inv_lref1 *)
lemma cpx_inv_lref1_drops: ∀h,G,L,T2,i. ⦃G,L⦄ ⊢ #i ⬈[h] T2 →
                           T2 = #i ∨
                           ∃∃J,K,V,V2. ⇩*[i] L ≘ K. ⓑ{J}V & ⦃G,K⦄ ⊢ V ⬈[h] V2 &
                                       ⇧*[↑i] V2 ≘ T2.
#h #G #L #T1 #i * #c #H elim (cpg_inv_lref1_drops … H) -H *
/4 width=7 by ex3_4_intro, ex_intro, or_introl, or_intror/
qed-.

(* Properties with generic slicing for local environments *******************)

(* Basic_2A1: includes: cpx_lift *)
lemma cpx_lifts_sn: ∀h,G. d_liftable2_sn … lifts (cpx h G).
#h #G #K #T1 #T2 * #cT #HT12 #b #f #L #HLK #U1 #HTU1
elim (cpg_lifts_sn … HT12 … HLK … HTU1) -K -T1
/3 width=4 by ex2_intro, ex_intro/
qed-.

lemma cpx_lifts_bi: ∀h,G. d_liftable2_bi … lifts (cpx h G).
#h #G #K #T1 #T2 * /3 width=10 by cpg_lifts_bi, ex_intro/
qed-.

(* Inversion lemmas with generic slicing for local environments *************)

(* Basic_2A1: includes: cpx_inv_lift1 *)
lemma cpx_inv_lifts_sn: ∀h,G. d_deliftable2_sn … lifts (cpx h G).
#h #G #L #U1 #U2 * #cU #HU12 #b #f #K #HLK #T1 #HTU1
elim (cpg_inv_lifts_sn … HU12 … HLK … HTU1) -L -U1
/3 width=4 by ex2_intro, ex_intro/
qed-.

lemma cpx_inv_lifts_bi: ∀h,G. d_deliftable2_bi …lifts (cpx h G).
#h #G #L #U1 #U2 * /3 width=10 by cpg_inv_lifts_bi, ex_intro/
qed-.
