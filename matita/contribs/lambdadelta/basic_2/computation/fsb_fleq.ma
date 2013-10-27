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

include "basic_2/computation/fpbs_fleq.ma".
include "basic_2/computation/fpbg_fpbg.ma".
include "basic_2/computation/fsb.ma".

(* "BIG TREE" STRONGLY NORMALIZING TERMS ************************************)

axiom fleq_fpbc_trans: ∀h,g,G1,G,G2,L1,L,L2,T1,T,T2. ⦃G1, L1, T1⦄ ⋕[h, g] ⦃G, L, T⦄ →
                       ⦃G, L, T⦄ ≻[h, g] ⦃G2, L2, T2⦄ → ⦃G1, L1, T1⦄ ≻[h, g] ⦃G2, L2, T2⦄.

axiom fleq_fpbg_trans: ∀h,g,G1,G,G2,L1,L,L2,T1,T,T2. ⦃G1, L1, T1⦄ ⋕[h, g] ⦃G, L, T⦄ →
                       ⦃G, L, T⦄ >[h, g] ⦃G2, L2, T2⦄ → ⦃G1, L1, T1⦄ >[h, g] ⦃G2, L2, T2⦄.

(* Properties ******************************************************)

lemma fsb_fleq_trans: ∀h,g,G1,L1,T1. ⦃G1, L1⦄ ⊢ ⦥[h, g] T1 →
                      ∀G2,L2,T2. ⦃G1, L1, T1⦄ ⋕[h, g] ⦃G2, L2, T2⦄ → ⦃G2, L2⦄ ⊢ ⦥[h, g] T2.
#h #g #G1 #L1 #T1 #H @(fsb_ind_alt … H) -G1 -L1 -T1
/4 width=5 by fsb_intro, fleq_fpbc_trans/
qed-.

(* Advanced eliminators *****************************************************)

lemma fsb_ind_fpbg_fpbs: ∀h,g. ∀R:relation3 genv lenv term.
                         (∀G1,L1,T1. ⦃G1, L1⦄ ⊢ ⦥[h, g] T1 →
                                     (∀G2,L2,T2. ⦃G1, L1, T1⦄ >[h, g] ⦃G2, L2, T2⦄ → R G2 L2 T2) →
                                     R G1 L1 T1
                         ) →
                         ∀G1,L1,T1. ⦃G1, L1⦄ ⊢ ⦥[h, g] T1 →
                         ∀G2,L2,T2. ⦃G1, L1, T1⦄ ≥[h, g] ⦃G2, L2, T2⦄ → R G2 L2 T2.
#h #g #R #IH #G1 #L1 #T1 #H @(fsb_ind_alt … H) -G1 -L1 -T1
#G1 #L1 #T1 #H1 #IH1 #G2 #L2 #T2 #H12 elim (fpbs_fwd_fpb_sn … H12) -H12
[ #H12 @IH -IH /2 width=5 by fsb_fleq_trans/
  -H1 #G0 #L0 #T0 #H20 lapply (fleq_fpbg_trans … H12 H20) -G2 -L2 -T2
  #H10 elim (fpbg_fwd_fpb_sn … H10) -H10 /2 width=5 by/
| -H1 -IH * /2 width=5 by/
]
qed-.
