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

include "basic_2/unwind/sstas.ma".
include "basic_2/reducibility/ysc.ma".
include "basic_2/computation/cprs.ma".

(* "BIG TREE" ORDER FOR CLOSURES ********************************************)

definition ygt: ∀h. sd h → bi_relation lenv term ≝
                λh,g. bi_TC … (ysc h g).

interpretation "'big tree' order (closure)"
   'BTGreaterThan h g L1 T1 L2 T2 = (ygt h g L1 T1 L2 T2).

(* Basic eliminators ********************************************************)

lemma ygt_ind: ∀h,g,L1,T1. ∀R:relation2 lenv term.
               (∀L2,T2. h ⊢ ⦃L1, T1⦄ ≻[g] ⦃L2, T2⦄ → R L2 T2) →
               (∀L,T,L2,T2. h ⊢ ⦃L1, T1⦄ >[g] ⦃L, T⦄ → h ⊢ ⦃L, T⦄ ≻[g] ⦃L2, T2⦄ → R L T → R L2 T2) →
               ∀L2,T2. h ⊢ ⦃L1, T1⦄ >[g] ⦃L2, T2⦄ → R L2 T2.
#h #g #L1 #T1 #R #IH1 #IH2 #L2 #T2 #H
@(bi_TC_ind  … IH1 IH2 L2 T2 H)
qed-. (**) (* /3 width=6 by bi_TC_ind/ fails *)

lemma ygt_ind_dx: ∀h,g,L2,T2. ∀R:relation2 lenv term.
                  (∀L1,T1. h ⊢ ⦃L1, T1⦄ ≻[g] ⦃L2, T2⦄ → R L1 T1) →
                  (∀L1,L,T1,T. h ⊢ ⦃L1, T1⦄ ≻[g] ⦃L, T⦄ → h ⊢ ⦃L, T⦄ >[g] ⦃L2, T2⦄ → R L T → R L1 T1) →
                  ∀L1,T1. h ⊢ ⦃L1, T1⦄ >[g] ⦃L2, T2⦄ → R L1 T1.
/3 width=6 by bi_TC_ind_dx/ qed-.

(* Basic properties *********************************************************)

lemma ygt_strap1: ∀h,g,L1,L,L2,T1,T,T2. h ⊢ ⦃L1, T1⦄ >[g] ⦃L, T⦄ →
                  h ⊢ ⦃L, T⦄ ≻[g] ⦃L2, T2⦄ → h ⊢ ⦃L1, T1⦄ >[g] ⦃L2, T2⦄.
/2 width=4/ qed-.

lemma ygt_strap2: ∀h,g,L1,L,L2,T1,T,T2. h ⊢ ⦃L1, T1⦄ ≻[g] ⦃L, T⦄ →
                  h ⊢ ⦃L, T⦄ >[g] ⦃L2, T2⦄ → h ⊢ ⦃L1, T1⦄ >[g] ⦃L2, T2⦄.
/2 width=4/ qed-.

lemma ygt_cprs_trans: ∀h,g,L1,L,T1,T. h ⊢ ⦃L1, T1⦄ >[g] ⦃L, T⦄ →
                      ∀T2. L ⊢ T ➡* T2 → h ⊢ ⦃L1, T1⦄ >[g] ⦃L, T2⦄.
#h #g #L1 #L #T1 #T #HLT1 #T2 #H @(cprs_ind … H) -T2 //
#T0 #T2 #_ #HT02 #IHT0 -HLT1
elim (term_eq_dec T0 T2) #HT02 destruct //
@(ygt_strap1 … IHT0) /3 width=1/
qed-.

lemma ygt_sstas_trans: ∀h,g,L1,L,T1,T. h ⊢ ⦃L1, T1⦄ >[g] ⦃L, T⦄ →
                       ∀T2. ⦃h, L⦄ ⊢ T •*[g] T2 → h ⊢ ⦃L1, T1⦄ >[g] ⦃L, T2⦄.
#h #g #L1 #L #T1 #T #HLT1 #T2 #H @(sstas_ind … H) -T2 //
#T0 #T2 #l #_ #HT02 #IHT0 -HLT1
@(ygt_strap1 … IHT0) -IHT0 /2 width=2/
qed-.

lemma cprs_ygt_trans: ∀h,g,L,T1,T. L ⊢ T1 ➡* T → 
                      ∀L2,T2. h ⊢ ⦃L, T⦄ >[g] ⦃L2, T2⦄ → h ⊢ ⦃L, T1⦄ >[g] ⦃L2, T2⦄.
#h #g #L #T1 #T #H @(cprs_ind … H) -T //
#T0 #T #_ #HT0 #IHT10 #L2 #T2 #HLT2
elim (term_eq_dec T0 T) #HT0 destruct /2 width=1/
@IHT10 -IHT10 @(ygt_strap2 … HLT2) /3 width=1/
qed-.

lemma sstas_ygt_trans: ∀h,g,L,T1,T.  ⦃h, L⦄ ⊢ T1 •*[g] T →
                       ∀L2,T2. h ⊢ ⦃L, T⦄ >[g] ⦃L2, T2⦄ → h ⊢ ⦃L, T1⦄ >[g] ⦃L2, T2⦄.
#h #g #L #T1 #T #H @(sstas_ind … H) -T //
#T0 #T #l #_ #HT0 #IHT10 #L2 #T2 #HLT2
@IHT10 -IHT10 @(ygt_strap2 … HLT2) /2 width=2/
qed-.

lemma fw_ygt: ∀h,g,L1,L2,T1,T2. ♯{L2, T2} < ♯{L1, T1} → h ⊢ ⦃L1, T1⦄ >[g] ⦃L2, T2⦄.
/3 width=1/ qed.

lemma cprs_ygt: ∀h,g,L,T1,T2. L ⊢ T1 ➡* T2 → (T1 = T2 → ⊥) → h ⊢ ⦃L, T1⦄ >[g] ⦃L, T2⦄.
#h #g #L #T1 #T2 #H @(cprs_ind … H) -T2
[ #H elim H -H //
| #T #T2 #_ #HT2 #IHT1 #H
  elim (term_eq_dec T1 T) #HT1 destruct
  [ -IHT1 /4 width=1 by ysc_cpr, bi_inj/ (**) (* auto too slow without trace *)
  | -H /4 width=3 by inj, ygt_cprs_trans/
  ]
]
qed.
