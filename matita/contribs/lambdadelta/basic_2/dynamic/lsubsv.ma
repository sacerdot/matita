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

include "basic_2/notation/relations/lrsubeqv_5.ma".
include "basic_2/dynamic/shnv.ma".

(* LOCAL ENVIRONMENT REFINEMENT FOR STRATIFIED NATIVE VALIDITY **************)

(* Note: this is not transitive *)
inductive lsubsv (h) (g) (G): relation lenv ≝
| lsubsv_atom: lsubsv h g G (⋆) (⋆)
| lsubsv_pair: ∀I,L1,L2,V. lsubsv h g G L1 L2 →
               lsubsv h g G (L1.ⓑ{I}V) (L2.ⓑ{I}V)
| lsubsv_beta: ∀L1,L2,W,V,l1. ⦃G, L1⦄ ⊢ ⓝW.V ¡[h, g, l1] → ⦃G, L2⦄ ⊢ W ¡[h, g] →
               ⦃G, L1⦄ ⊢ V ▪[h, g] l1+1 → ⦃G, L2⦄ ⊢ W ▪[h, g] l1 →
               lsubsv h g G L1 L2 → lsubsv h g G (L1.ⓓⓝW.V) (L2.ⓛW)
.

interpretation
  "local environment refinement (stratified native validity)"
  'LRSubEqV h g G L1 L2 = (lsubsv h g G L1 L2).

(* Basic inversion lemmas ***************************************************)

fact lsubsv_inv_atom1_aux: ∀h,g,G,L1,L2. G ⊢ L1 ⫃¡[h, g] L2 → L1 = ⋆ → L2 = ⋆.
#h #g #G #L1 #L2 * -L1 -L2
[ //
| #I #L1 #L2 #V #_ #H destruct
| #L1 #L2 #W #V #l1 #_ #_ #_ #_ #_ #H destruct
]
qed-.

lemma lsubsv_inv_atom1: ∀h,g,G,L2. G ⊢ ⋆ ⫃¡[h, g] L2 → L2 = ⋆.
/2 width=6 by lsubsv_inv_atom1_aux/ qed-.

fact lsubsv_inv_pair1_aux: ∀h,g,G,L1,L2. G ⊢ L1 ⫃¡[h, g] L2 →
                           ∀I,K1,X. L1 = K1.ⓑ{I}X →
                           (∃∃K2. G ⊢ K1 ⫃¡[h, g] K2 & L2 = K2.ⓑ{I}X) ∨
                           ∃∃K2,W,V,l1. ⦃G, K1⦄ ⊢ ⓝW.V ¡[h, g, l1] & ⦃G, K2⦄ ⊢ W ¡[h, g] &
                                       ⦃G, K1⦄ ⊢ V ▪[h, g] l1+1 & ⦃G, K2⦄ ⊢ W ▪[h, g] l1 &
                                        G ⊢ K1 ⫃¡[h, g] K2 &
                                        I = Abbr & L2 = K2.ⓛW & X = ⓝW.V.
#h #g #G #L1 #L2 * -L1 -L2
[ #J #K1 #X #H destruct
| #I #L1 #L2 #V #HL12 #J #K1 #X #H destruct /3 width=3 by ex2_intro, or_introl/
| #L1 #L2 #W #V #l1 #HWV #HW #HVl1 #HWl1 #HL12 #J #K1 #X #H destruct /3 width=11 by or_intror, ex8_4_intro/
]
qed-.

lemma lsubsv_inv_pair1: ∀h,g,I,G,K1,L2,X. G ⊢ K1.ⓑ{I}X ⫃¡[h, g] L2 →
                        (∃∃K2. G ⊢ K1 ⫃¡[h, g] K2 & L2 = K2.ⓑ{I}X) ∨
                        ∃∃K2,W,V,l1. ⦃G, K1⦄ ⊢ ⓝW.V ¡[h, g, l1] & ⦃G, K2⦄ ⊢ W ¡[h, g] &
                                     ⦃G, K1⦄ ⊢ V ▪[h, g] l1+1 & ⦃G, K2⦄ ⊢ W ▪[h, g] l1 &
                                     G ⊢ K1 ⫃¡[h, g] K2 &
                                     I = Abbr & L2 = K2.ⓛW & X = ⓝW.V.
/2 width=3 by lsubsv_inv_pair1_aux/ qed-.

fact lsubsv_inv_atom2_aux: ∀h,g,G,L1,L2. G ⊢ L1 ⫃¡[h, g] L2 → L2 = ⋆ → L1 = ⋆.
#h #g #G #L1 #L2 * -L1 -L2
[ //
| #I #L1 #L2 #V #_ #H destruct
| #L1 #L2 #W #V #l1 #_ #_ #_ #_ #_ #H destruct
]
qed-.

lemma lsubsv_inv_atom2: ∀h,g,G,L1. G ⊢ L1 ⫃¡[h, g] ⋆ → L1 = ⋆.
/2 width=6 by lsubsv_inv_atom2_aux/ qed-.

fact lsubsv_inv_pair2_aux: ∀h,g,G,L1,L2. G ⊢ L1 ⫃¡[h, g] L2 →
                           ∀I,K2,W. L2 = K2.ⓑ{I}W →
                           (∃∃K1. G ⊢ K1 ⫃¡[h, g] K2 & L1 = K1.ⓑ{I}W) ∨
                           ∃∃K1,V,l1. ⦃G, K1⦄ ⊢ ⓝW.V ¡[h, g, l1] & ⦃G, K2⦄ ⊢ W ¡[h, g] &
                                      ⦃G, K1⦄ ⊢ V ▪[h, g] l1+1 & ⦃G, K2⦄ ⊢ W ▪[h, g] l1 &
                                      G ⊢ K1 ⫃¡[h, g] K2 & I = Abst & L1 = K1.ⓓⓝW.V.
#h #g #G #L1 #L2 * -L1 -L2
[ #J #K2 #U #H destruct
| #I #L1 #L2 #V #HL12 #J #K2 #U #H destruct /3 width=3 by ex2_intro, or_introl/
| #L1 #L2 #W #V #l1 #HWV #HW #HVl1 #HWl1 #HL12 #J #K2 #U #H destruct /3 width=8 by or_intror, ex7_3_intro/
]
qed-.

lemma lsubsv_inv_pair2: ∀h,g,I,G,L1,K2,W. G ⊢ L1 ⫃¡[h, g] K2.ⓑ{I}W →
                        (∃∃K1. G ⊢ K1 ⫃¡[h, g] K2 & L1 = K1.ⓑ{I}W) ∨
                        ∃∃K1,V,l1. ⦃G, K1⦄ ⊢ ⓝW.V ¡[h, g, l1] & ⦃G, K2⦄ ⊢ W ¡[h, g] &
                                   ⦃G, K1⦄ ⊢ V ▪[h, g] l1+1 & ⦃G, K2⦄ ⊢ W ▪[h, g] l1 &
                                   G ⊢ K1 ⫃¡[h, g] K2 & I = Abst & L1 = K1.ⓓⓝW.V.
/2 width=3 by lsubsv_inv_pair2_aux/ qed-.

(* Basic forward lemmas *****************************************************)

lemma lsubsv_fwd_lsubr: ∀h,g,G,L1,L2. G ⊢ L1 ⫃¡[h, g] L2 → L1 ⫃ L2.
#h #g #G #L1 #L2 #H elim H -L1 -L2 /2 width=1 by lsubr_pair, lsubr_beta/
qed-.

(* Basic properties *********************************************************)

lemma lsubsv_refl: ∀h,g,G,L. G ⊢ L ⫃¡[h, g] L.
#h #g #G #L elim L -L /2 width=1 by lsubsv_pair/
qed.

lemma lsubsv_cprs_trans: ∀h,g,G,L1,L2. G ⊢ L1 ⫃¡[h, g] L2 →
                         ∀T1,T2. ⦃G, L2⦄ ⊢ T1 ➡* T2 → ⦃G, L1⦄ ⊢ T1 ➡* T2.
/3 width=6 by lsubsv_fwd_lsubr, lsubr_cprs_trans/
qed-.

(* Note: the constant 0 cannot be generalized *)
lemma lsubsv_drop_O1_conf: ∀h,g,G,L1,L2. G ⊢ L1 ⫃¡[h, g] L2 →
                           ∀K1,s,e. ⇩[s, 0, e] L1 ≡ K1 →
                           ∃∃K2. G ⊢ K1 ⫃¡[h, g] K2 & ⇩[s, 0, e] L2 ≡ K2.
#h #g #G #L1 #L2 #H elim H -L1 -L2
[ /2 width=3 by ex2_intro/
| #I #L1 #L2 #V #_ #IHL12 #K1 #s #e #H
  elim (drop_inv_O1_pair1 … H) -H * #He #HLK1
  [ destruct
    elim (IHL12 L1 s 0) -IHL12 // #X #HL12 #H
    <(drop_inv_O2 … H) in HL12; -H /3 width=3 by lsubsv_pair, drop_pair, ex2_intro/
  | elim (IHL12 … HLK1) -L1 /3 width=3 by drop_drop_lt, ex2_intro/
  ]
| #L1 #L2 #W #V #l1 #HWV #HW #HVl1 #HWl1 #_ #IHL12 #K1 #s #e #H
  elim (drop_inv_O1_pair1 … H) -H * #He #HLK1
  [ destruct
    elim (IHL12 L1 s 0) -IHL12 // #X #HL12 #H
    <(drop_inv_O2 … H) in HL12; -H /3 width=4 by lsubsv_beta, drop_pair, ex2_intro/
  | elim (IHL12 … HLK1) -L1 /3 width=3 by drop_drop_lt, ex2_intro/
  ]
]
qed-.

(* Note: the constant 0 cannot be generalized *)
lemma lsubsv_drop_O1_trans: ∀h,g,G,L1,L2. G ⊢ L1 ⫃¡[h, g] L2 →
                            ∀K2,s, e. ⇩[s, 0, e] L2 ≡ K2 →
                            ∃∃K1. G ⊢ K1 ⫃¡[h, g] K2 & ⇩[s, 0, e] L1 ≡ K1.
#h #g #G #L1 #L2 #H elim H -L1 -L2
[ /2 width=3 by ex2_intro/
| #I #L1 #L2 #V #_ #IHL12 #K2 #s #e #H
  elim (drop_inv_O1_pair1 … H) -H * #He #HLK2
  [ destruct
    elim (IHL12 L2 s 0) -IHL12 // #X #HL12 #H
    <(drop_inv_O2 … H) in HL12; -H /3 width=3 by lsubsv_pair, drop_pair, ex2_intro/
  | elim (IHL12 … HLK2) -L2 /3 width=3 by drop_drop_lt, ex2_intro/
  ]
| #L1 #L2 #W #V #l1 #HWV #HW #HVl1 #HWl1 #_ #IHL12 #K2 #s #e #H
  elim (drop_inv_O1_pair1 … H) -H * #He #HLK2
  [ destruct
    elim (IHL12 L2 s 0) -IHL12 // #X #HL12 #H
    <(drop_inv_O2 … H) in HL12; -H /3 width=4 by lsubsv_beta, drop_pair, ex2_intro/
  | elim (IHL12 … HLK2) -L2 /3 width=3 by drop_drop_lt, ex2_intro/
  ]
]
qed-.
