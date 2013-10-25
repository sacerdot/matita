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

include "basic_2/notation/relations/btpredstarrestricted_8.ma".
include "basic_2/computation/fpbg.ma".

(* RESTRICTED "BIG TREE" PROPER PARALLEL COMPUTATION FOR CLOSURES ***********)

inductive fpbr (h) (g) (G1) (L1) (T1): relation3 genv lenv term ≝
| fpbr_inj : ∀G2,L2,T2. ⦃G1, L1, T1⦄ ⊃ ⦃G2, L2, T2⦄ → fpbr h g G1 L1 T1 G2 L2 T2
| fpbr_step: ∀G,G2,L,L2,T,T2. fpbr h g G1 L1 T1 G L T → ⦃G, L, T⦄ ≽[h, g] ⦃G2, L2, T2⦄ →
             fpbr h g G1 L1 T1 G2 L2 T2
.

interpretation "restricted 'big tree' proper parallel computation (closure)"
   'BTPRedStarRestricted h g G1 L1 T1 G2 L2 T2 = (fpbr h g G1 L1 T1 G2 L2 T2).

(* Basic forward lemmas *****************************************************)

lemma fpbr_fwd_fpbg: ∀h,g,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊃≥[h, g] ⦃G2, L2, T2⦄ →
                     ⦃G1, L1, T1⦄ >[h, g] ⦃G2, L2, T2⦄.
#h #g #G1 #G2 #L1 #L2 #T1 #T2 #H elim H -G2 -L2 -T2
/3 width=5 by fpbg_strap1, fpbc_fpbg, fpbc_fqu/
qed-.

lemma fpbr_fwd_fpbs: ∀h,g,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊃≥[h, g] ⦃G2, L2, T2⦄ →
                     ⦃G1, L1, T1⦄ ≥[h, g] ⦃G2, L2, T2⦄.
#h #g #G1 #G2 #L1 #L2 #T1 #T2 #H elim H -G2 -L2 -T2
/3 width=5 by fpbs_strap1, fqup_fpbs, fqu_fqup/
qed-.

(* Basic properties *********************************************************)

lemma fqu_fpbs_fpbr: ∀h,g,G1,G,G2,L1,L,L2,T1,T,T2. ⦃G1, L1, T1⦄ ⊃ ⦃G, L, T⦄ →
                     ⦃G, L, T⦄ ≥[h, g] ⦃G2, L2, T2⦄ → ⦃G1, L1, T1⦄ ⊃≥[h, g] ⦃G2, L2, T2⦄.
#h #g #G1 #G #G2 #L1 #L #L2 #T1 #T #T2 #H1 #H @(fpbs_ind … H) -G2 -L2 -T2
/2 width=5 by fpbr_inj, fpbr_step/
qed.

lemma fpbr_strap2: ∀h,g,G1,G,G2,L1,L,L2,T1,T,T2. ⦃G1, L1, T1⦄ ⊃ ⦃G, L, T⦄ →
                   ⦃G, L, T⦄ ⊃≥[h, g] ⦃G2, L2, T2⦄ → ⦃G1, L1, T1⦄ ⊃≥[h, g] ⦃G2, L2, T2⦄.
/3 width=5 by fqu_fpbs_fpbr, fpbr_fwd_fpbs/ qed-.

(* Note: this is used in the closure proof *)
lemma fpbr_fpbs_trans: ∀h,g,G1,G,G2,L1,L,L2,T1,T,T2. ⦃G1, L1, T1⦄ ⊃≥[h, g] ⦃G, L, T⦄ →
                       ⦃G, L, T⦄ ≥[h, g] ⦃G2, L2, T2⦄ → ⦃G1, L1, T1⦄ ⊃≥[h, g] ⦃G2, L2, T2⦄.
#h #g #G1 #G #G2 #L1 #L #L2 #T1 #T #T2 #HT1 #HT2 @(fpbs_ind … HT2) -G2 -L2 -T2
/2 width=5 by fpbr_step/
qed-.

lemma fqup_fpbr_trans: ∀h,g,G1,G,G2,L1,L,L2,T1,T,T2. ⦃G1, L1, T1⦄ ⊃+ ⦃G, L, T⦄ →
                       ⦃G, L, T⦄ ⊃≥[h, g] ⦃G2, L2, T2⦄ → ⦃G1, L1, T1⦄ ⊃≥[h, g] ⦃G2, L2, T2⦄.
#h #g #G1 #G #G2 #L1 #L #L2 #T1 #T #T2 #HT1 @(fqup_ind … HT1) -G -L -T
/3 width=5 by fpbr_strap2/
qed-.

(* Note: this is used in the closure proof *)
lemma fqup_fpbr: ∀h,g,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊃+ ⦃G2, L2, T2⦄ → ⦃G1, L1, T1⦄ ⊃≥[h, g] ⦃G2, L2, T2⦄.
#h #g #G1 #G2 #L1 #L2 #T1 #T2 #H elim (fqup_inv_step_sn … H) -H
/3 width=5 by fqu_fpbs_fpbr, fqus_fpbs/
qed.
