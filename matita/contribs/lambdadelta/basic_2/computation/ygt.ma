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

include "basic_2/notation/relations/btpredstarproper_8.ma".
include "basic_2/reduction/ysc.ma".
include "basic_2/computation/yprs.ma".

(* "BIG TREE" PROPER PARALLEL COMPUTATION FOR CLOSURES **********************)

inductive ygt (h) (g) (G1) (L1) (T1): relation3 genv lenv term ≝
| ygt_inj : ∀G,G2,L,L2,T,T2. ⦃G1, L1, T1⦄ ≥[h, g] ⦃G, L, T⦄ → ⦃G, L, T⦄ ≻[h, g] ⦃G2, L2, T2⦄ →
            ygt h g G1 L1 T1 G2 L2 T2
| ygt_step: ∀G,L,L2,T. ygt h g G1 L1 T1 G L T → ⦃G, L⦄ ⊢ ➡ L2 → ygt h g G1 L1 T1 G L2 T
.

interpretation "'big tree' proper parallel computation (closure)"
   'BTPRedStarProper h g G1 L1 T1 G2 L2 T2 = (ygt h g G1 L1 T1 G2 L2 T2).

(* Basic forvard lemmas *****************************************************)

lemma ygt_fwd_yprs: ∀h,g,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ >[h, g] ⦃G2, L2, T2⦄ →
                    ⦃G1, L1, T1⦄ ≥[h, g] ⦃G2, L2, T2⦄.
#h #g #G1 #G2 #L1 #L2 #T1 #T2 #H elim H -G2 -L2 -T2
/3 width=5 by yprs_strap1, ysc_ypr, ypr_lpr/
qed-.

(* Basic properties *********************************************************)

lemma ysc_ygt: ∀h,g,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ≻[h, g] ⦃G2, L2, T2⦄ →
               ⦃G1, L1, T1⦄ >[h, g] ⦃G2, L2, T2⦄.
/3 width=5 by ygt_inj, ygt_step/ qed.

lemma ygt_strap1: ∀h,g,G1,G,G2,L1,L,L2,T1,T,T2. ⦃G1, L1, T1⦄ >[h, g] ⦃G, L, T⦄ →
                  ⦃G, L, T⦄ ≽[h, g] ⦃G2, L2, T2⦄ →  ⦃G1, L1, T1⦄ >[h, g] ⦃G2, L2, T2⦄.
#h #g #G1 #G #G2 #L1 #L #L2 #T1 #T #T2 #H1 #H2
lapply (ygt_fwd_yprs … H1) #H0
elim (ypr_inv_ysc … H2) -H2 [| * #HG2 #HL2 #HT2 destruct ]
/2 width=5 by ygt_inj, ygt_step/
qed-.

lemma ygt_strap2: ∀h,g,G1,G,G2,L1,L,L2,T1,T,T2. ⦃G1, L1, T1⦄ ≽[h, g] ⦃G, L, T⦄ →
                  ⦃G, L, T⦄ >[h, g] ⦃G2, L2, T2⦄ → ⦃G1, L1, T1⦄ >[h, g] ⦃G2, L2, T2⦄.
#h #g #G1 #G #G2 #L1 #L #L2 #T1 #T #T2 #H1 #H2 elim H2 -G2 -L2 -T2
/3 width=5 by ygt_step, ygt_inj, yprs_strap2/
qed-.

lemma ygt_yprs_trans: ∀h,g,G1,G,G2,L1,L,L2,T1,T,T2. ⦃G1, L1, T1⦄ >[h, g] ⦃G, L, T⦄ →
                      ⦃G, L, T⦄ ≥[h, g] ⦃G2, L2, T2⦄ → ⦃G1, L1, T1⦄ >[h, g] ⦃G2, L2, T2⦄.
#h #g #G1 #G #G2 #L1 #L #L2 #T1 #T #T2 #HT1 #HT2 @(yprs_ind … HT2) -G2 -L2 -T2
/2 width=5 by ygt_strap1/
qed-.

lemma yprs_ygt_trans: ∀h,g,G1,G,L1,L,T1,T. ⦃G1, L1, T1⦄ ≥[h, g] ⦃G, L, T⦄ →
                      ∀G2,L2,T2. ⦃G, L, T⦄ >[h, g] ⦃G2, L2, T2⦄ → ⦃G1, L1, T1⦄ >[h, g] ⦃G2, L2, T2⦄.
#h #g #G1 #G #L1 #L #T1 #T #HT1 @(yprs_ind … HT1) -G -L -T
/3 width=5 by ygt_strap2/
qed-.

lemma fsupp_ygt: ∀h,g,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊃+ ⦃G2, L2, T2⦄ → ⦃G1, L1, T1⦄ >[h, g] ⦃G2, L2, T2⦄.
#h #g #G1 #G2 #L1 #L2 #T1 #T2 #H @(fsupp_ind … L2 T2 H) -G2 -L2 -T2
/3 width=5 by fsupp_yprs, ysc_fsup, ysc_ygt, ygt_inj/
qed.

lemma cprs_ygt: ∀h,g,G,L,T1,T2. ⦃G, L⦄ ⊢ T1 ➡* T2 → (T1 = T2 → ⊥) →
                ⦃G, L, T1⦄ >[h, g] ⦃G, L, T2⦄.
#h #g #G #L #T1 #T2 #H @(cprs_ind … H) -T2
[ #H elim H //
| #T #T2 #_ #HT2 #IHT1 #HT12
  elim (term_eq_dec T1 T) #H destruct
  [ -IHT1 /4 width=1/
  | lapply (IHT1 … H) -IHT1 -H -HT12 #HT1
    @(ygt_strap1 … HT1) -HT1 /2 width=1 by ypr_cpr/
  ]
]
qed.
