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

include "basic_2/notation/relations/btpredstarproper_6.ma".
include "basic_2/dynamic/ysc.ma".
include "basic_2/dynamic/yprs.ma".

(* "BIG TREE" PROPER PARALLEL COMPUTATION FOR CLOSURES **********************)

inductive ygt (h) (g) (L1) (T1): relation2 lenv term ≝
| ygt_inj : ∀L,L2,T,T2. h ⊢ ⦃L1, T1⦄ ≥[h, g] ⦃L, T⦄ → h ⊢ ⦃L, T⦄ ≻[h, g] ⦃L2, T2⦄ →
            ygt h g L1 T1 L2 T2
| ygt_step: ∀L,L2,T. ygt h g L1 T1 L T → ⦃G, L⦄ ⊢ ➡ L2 → ygt h g L1 T1 L2 T
.

interpretation "'big tree' proper parallel computation (closure)"
   'BTPRedStarProper h g L1 T1 L2 T2 = (ygt h g L1 T1 L2 T2).

(* Basic forvard lemmas *****************************************************)

lemma ygt_fwd_yprs: ∀h,g,L1,L2,T1,T2. h ⊢ ⦃L1, T1⦄ >[h, g] ⦃L2, T2⦄ →
                    h ⊢ ⦃L1, T1⦄ ≥[h, g] ⦃L2, T2⦄.
#h #g #L1 #L2 #T1 #T2 #H elim H -L2 -T2
/3 width=4 by yprs_strap1, ysc_ypr, ypr_lpr/
qed-.

(* Basic properties *********************************************************)

lemma ysc_ygt: ∀h,g,L1,L2,T1,T2. h ⊢ ⦃L1, T1⦄ ≻[h, g] ⦃L2, T2⦄ →
               h ⊢ ⦃L1, T1⦄ >[h, g] ⦃L2, T2⦄.
/3 width=4/ qed.

lemma ygt_strap1: ∀h,g,L1,L,L2,T1,T,T2. h ⊢ ⦃L1, T1⦄ >[h, g] ⦃L, T⦄ →
                  h ⊢ ⦃L, T⦄ ≽[h, g] ⦃L2, T2⦄ → h ⊢ ⦃L1, T1⦄ >[h, g] ⦃L2, T2⦄.
#h #g #L1 #L #L2 #T1 #T #T2 #H1 #H2
lapply (ygt_fwd_yprs … H1) #H0
elim (ypr_inv_ysc … H2) -H2 [| * #HL2 #H destruct ] /2 width=4/
qed-.

lemma ygt_strap2: ∀h,g,L1,L,L2,T1,T,T2. h ⊢ ⦃L1, T1⦄ ≽[h, g] ⦃L, T⦄ →
                  h ⊢ ⦃L, T⦄ >[h, g] ⦃L2, T2⦄ → h ⊢ ⦃L1, T1⦄ >[h, g] ⦃L2, T2⦄.
#h #g #L1 #L #L2 #T1 #T #T2 #H1 #H2 elim H2 -L2 -T2
[ /3 width=4 by ygt_inj, yprs_strap2/ | /2 width=3/ ]
qed-.

lemma ygt_yprs_trans: ∀h,g,L1,L,L2,T1,T,T2. h ⊢ ⦃L1, T1⦄ >[h, g] ⦃L, T⦄ →
                      h ⊢ ⦃L, T⦄ ≥[h, g] ⦃L2, T2⦄ → h ⊢ ⦃L1, T1⦄ >[h, g] ⦃L2, T2⦄.
#h #g #L1 #L #L2 #T1 #T #T2 #HT1 #HT2 @(yprs_ind … HT2) -L2 -T2 //
/2 width=4 by ygt_strap1/
qed-.

lemma yprs_ygt_trans: ∀h,g,L1,L,T1,T. h ⊢ ⦃L1, T1⦄ ≥[h, g] ⦃L, T⦄ →
                      ∀L2,T2. h ⊢ ⦃L, T⦄ >[h, g] ⦃L2, T2⦄ → h ⊢ ⦃L1, T1⦄ >[h, g] ⦃L2, T2⦄.
#h #g #L1 #L #T1 #T #HT1 @(yprs_ind … HT1) -L -T //
/3 width=4 by ygt_strap2/
qed-.

lemma fsupp_ygt: ∀h,g,L1,L2,T1,T2. ⦃L1, T1⦄ ⊃+ ⦃L2, T2⦄ → h ⊢ ⦃L1, T1⦄ >[h, g] ⦃L2, T2⦄.
#h #g #L1 #L2 #T1 #T2 #H @(fsupp_ind … L2 T2 H) -L2 -T2 /3 width=1/ /3 width=4/
qed.

lemma cprs_ygt: ∀h,g,L,T1,T2. ⦃G, L⦄ ⊢ T1 ➡* T2 → (T1 = T2 → ⊥) →
                h ⊢ ⦃L, T1⦄ >[h, g] ⦃L, T2⦄.
#h #g #L #T1 #T2 #H @(cprs_ind … H) -T2
[ #H elim H //
| #T #T2 #_ #HT2 #IHT1 #HT12
  elim (term_eq_dec T1 T) #H destruct
  [ -IHT1 /4 width=1/
  | lapply (IHT1 … H) -IHT1 -H -HT12 #HT1
    @(ygt_strap1 … HT1) -HT1 /2 width=1/
  ]
]
qed.

lemma sstas_ygt: ∀h,g,L,T1,T2. ⦃G, L⦄ ⊢ T1 •*[h, g] T2 → (T1 = T2 → ⊥) →
                 h ⊢ ⦃L, T1⦄ >[h, g] ⦃L, T2⦄.
#h #g #L #T1 #T2 #H @(sstas_ind … H) -T2
[ #H elim H //
| #T #T2 #l #_ #HT2 #IHT1 #HT12 -HT12
  elim (term_eq_dec T1 T) #H destruct
  [ -IHT1 /3 width=2/
  | lapply (IHT1 … H) -IHT1 -H #HT1
    @(ygt_strap1 … HT1) -HT1 /2 width=2/
  ]
]
qed.

lemma lsubsv_ygt: ∀h,g,L1,L2,T. h ⊢ L2 ¡⊑[h, g] L1 → (L1 = L2 → ⊥) →
                  h ⊢ ⦃L1, T⦄ >[h, g] ⦃L2, T⦄.
/4 width=1/ qed.
