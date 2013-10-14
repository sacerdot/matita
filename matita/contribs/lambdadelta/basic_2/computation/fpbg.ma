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
include "basic_2/substitution/fqup.ma".
include "basic_2/reduction/fpbc.ma".
include "basic_2/computation/fpbs.ma".

(* "BIG TREE" PROPER PARALLEL COMPUTATION FOR CLOSURES **********************)

inductive fpbg (h) (g) (G1) (L1) (T1): relation3 genv lenv term ≝
| fpbg_inj : ∀G,G2,L,L2,T,T2. ⦃G1, L1, T1⦄ ≥[h, g] ⦃G, L, T⦄ → ⦃G, L, T⦄ ≻[h, g] ⦃G2, L2, T2⦄ →
             fpbg h g G1 L1 T1 G2 L2 T2
| fpbg_step: ∀G,L,L2,T. fpbg h g G1 L1 T1 G L T → ⦃G, L⦄ ⊢ ➡[h, g] L2 → fpbg h g G1 L1 T1 G L2 T
.

interpretation "'big tree' proper parallel computation (closure)"
   'BTPRedStarProper h g G1 L1 T1 G2 L2 T2 = (fpbg h g G1 L1 T1 G2 L2 T2).

(* Basic forvard lemmas *****************************************************)

lemma fpbg_fwd_fpbs: ∀h,g,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ >[h, g] ⦃G2, L2, T2⦄ →
                     ⦃G1, L1, T1⦄ ≥[h, g] ⦃G2, L2, T2⦄.
#h #g #G1 #G2 #L1 #L2 #T1 #T2 #H elim H -G2 -L2 -T2
/3 width=5 by fpbs_strap1, fpbc_fwd_fpb, fpb_lpx/
qed-.

(* Basic properties *********************************************************)

lemma fpbc_fpbg: ∀h,g,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ≻[h, g] ⦃G2, L2, T2⦄ →
                 ⦃G1, L1, T1⦄ >[h, g] ⦃G2, L2, T2⦄.
/3 width=5 by fpbg_inj, fpbg_step/ qed.

lemma fpbg_strap1: ∀h,g,G1,G,G2,L1,L,L2,T1,T,T2. ⦃G1, L1, T1⦄ >[h, g] ⦃G, L, T⦄ →
                   ⦃G, L, T⦄ ≽[h, g] ⦃G2, L2, T2⦄ →  ⦃G1, L1, T1⦄ >[h, g] ⦃G2, L2, T2⦄.
#h #g #G1 #G #G2 #L1 #L #L2 #T1 #T #T2 #H1 #H2
lapply (fpbg_fwd_fpbs … H1) #H0
elim (fpb_fpbc_or_refl … H2) -H2 [| * #HG2 #HL2 #HT2 destruct ]
/2 width=5 by fpbg_inj, fpbg_step/
qed-.

lemma fpbg_strap2: ∀h,g,G1,G,G2,L1,L,L2,T1,T,T2. ⦃G1, L1, T1⦄ ≽[h, g] ⦃G, L, T⦄ →
                   ⦃G, L, T⦄ >[h, g] ⦃G2, L2, T2⦄ → ⦃G1, L1, T1⦄ >[h, g] ⦃G2, L2, T2⦄.
#h #g #G1 #G #G2 #L1 #L #L2 #T1 #T #T2 #H1 #H2 elim H2 -G2 -L2 -T2
/3 width=5 by fpbg_step, fpbg_inj, fpbs_strap2/
qed-.

lemma fpbg_fpbs_trans: ∀h,g,G1,G,G2,L1,L,L2,T1,T,T2. ⦃G1, L1, T1⦄ >[h, g] ⦃G, L, T⦄ →
                       ⦃G, L, T⦄ ≥[h, g] ⦃G2, L2, T2⦄ → ⦃G1, L1, T1⦄ >[h, g] ⦃G2, L2, T2⦄.
#h #g #G1 #G #G2 #L1 #L #L2 #T1 #T #T2 #HT1 #HT2 @(fpbs_ind … HT2) -G2 -L2 -T2
/2 width=5 by fpbg_strap1/
qed-.

lemma fpbs_fpbg_trans: ∀h,g,G1,G,L1,L,T1,T. ⦃G1, L1, T1⦄ ≥[h, g] ⦃G, L, T⦄ →
                       ∀G2,L2,T2. ⦃G, L, T⦄ >[h, g] ⦃G2, L2, T2⦄ → ⦃G1, L1, T1⦄ >[h, g] ⦃G2, L2, T2⦄.
#h #g #G1 #G #L1 #L #T1 #T #HT1 @(fpbs_ind … HT1) -G -L -T
/3 width=5 by fpbg_strap2/
qed-.

lemma fqup_fpbg: ∀h,g,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊃+ ⦃G2, L2, T2⦄ → ⦃G1, L1, T1⦄ >[h, g] ⦃G2, L2, T2⦄.
#h #g #G1 #G2 #L1 #L2 #T1 #T2 #H @(fqup_ind … L2 T2 H) -G2 -L2 -T2
/4 width=5 by fpbg_strap1, fpbc_fpbg, fpbc_fqu, fpb_fquq, fqu_fquq/
qed.

lemma cpxs_fpbg: ∀h,g,G,L,T1,T2. ⦃G, L⦄ ⊢ T1 ➡*[h, g] T2 → (T1 = T2 → ⊥) →
                 ⦃G, L, T1⦄ >[h, g] ⦃G, L, T2⦄.
#h #g #G #L #T1 #T2 #H @(cpxs_ind … H) -T2
[ #H elim H //
| #T #T2 #_ #HT2 #IHT1 #HT12
  elim (term_eq_dec T1 T) #H destruct
  [ -IHT1 /4 width=1/
  | lapply (IHT1 … H) -IHT1 -H -HT12 #HT1
    @(fpbg_strap1 … HT1) -HT1 /2 width=1 by fpb_cpx/
  ]
]
qed.

lemma cprs_fpbg: ∀h,g,G,L,T1,T2. ⦃G, L⦄ ⊢ T1 ➡* T2 → (T1 = T2 → ⊥) →
                 ⦃G, L, T1⦄ >[h, g] ⦃G, L, T2⦄.
/3 width=1 by cprs_cpxs, cpxs_fpbg/ qed.
