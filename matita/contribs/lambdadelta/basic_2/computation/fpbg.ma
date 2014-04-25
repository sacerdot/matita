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

include "basic_2/notation/relations/lazybtpredstarproper_8.ma".
include "basic_2/computation/fpbc.ma".

(* GENEARAL "BIG TREE" PROPER PARALLEL COMPUTATION FOR CLOSURES *************)

definition fpbg: ∀h. sd h → tri_relation genv lenv term ≝
                 λh,g. tri_TC … (fpbc h g).

interpretation "general 'big tree' proper parallel computation (closure)"
   'LazyBTPRedStarProper h g G1 L1 T1 G2 L2 T2 = (fpbg h g G1 L1 T1 G2 L2 T2).

(* Basic properties *********************************************************)

lemma fpbc_fpbg: ∀h,g,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ≻≡[h, g] ⦃G2, L2, T2⦄ →
                 ⦃G1, L1, T1⦄ >≡[h, g] ⦃G2, L2, T2⦄.
/2 width=1 by tri_inj/ qed.

lemma fpbg_strap1: ∀h,g,G1,G,G2,L1,L,L2,T1,T,T2.
                   ⦃G1, L1, T1⦄ >≡[h, g] ⦃G, L, T⦄ → ⦃G, L, T⦄ ≻≡[h, g] ⦃G2, L2, T2⦄ →
                   ⦃G1, L1, T1⦄ >≡[h, g] ⦃G2, L2, T2⦄.
/2 width=5 by tri_step/ qed.

lemma fpbg_strap2: ∀h,g,G1,G,G2,L1,L,L2,T1,T,T2.
                   ⦃G1, L1, T1⦄ ≻≡[h, g] ⦃G, L, T⦄ → ⦃G, L, T⦄ >≡[h, g] ⦃G2, L2, T2⦄ →
                   ⦃G1, L1, T1⦄ >≡[h, g] ⦃G2, L2, T2⦄.
/2 width=5 by tri_TC_strap/ qed.

(* Note: this is used in the closure proof *)
lemma fqup_fpbg: ∀h,g,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊐+ ⦃G2, L2, T2⦄ → ⦃G1, L1, T1⦄ >≡[h, g] ⦃G2, L2, T2⦄.
/4 width=1 by fpbc_fpbg, fpbu_fpbc, fpbu_fqup/ qed.

(* Basic eliminators ********************************************************)

lemma fpbg_ind: ∀h,g,G1,L1,T1. ∀R:relation3 ….
                (∀G2,L2,T2. ⦃G1, L1, T1⦄ ≻≡[h, g] ⦃G2, L2, T2⦄ → R G2 L2 T2) →
                (∀G,G2,L,L2,T,T2. ⦃G1, L1, T1⦄ >≡[h, g] ⦃G, L, T⦄ → ⦃G, L, T⦄ ≻≡[h, g] ⦃G2, L2, T2⦄ → R G L T → R G2 L2 T2) →
                ∀G2,L2,T2. ⦃G1, L1, T1⦄ >≡[h, g] ⦃G2, L2, T2⦄ → R G2 L2 T2.
#h #g #G1 #L1 #T1 #R #IH1 #IH2 #G2 #L2 #T2 #H
@(tri_TC_ind … IH1 IH2 G2 L2 T2 H)
qed-.

lemma fpbg_ind_dx: ∀h,g,G2,L2,T2. ∀R:relation3 ….
                   (∀G1,L1,T1. ⦃G1, L1, T1⦄ ≻≡[h, g] ⦃G2, L2, T2⦄ → R G1 L1 T1) →
                   (∀G1,G,L1,L,T1,T. ⦃G1, L1, T1⦄ ≻≡[h, g] ⦃G, L, T⦄ → ⦃G, L, T⦄ >≡[h, g] ⦃G2, L2, T2⦄ → R G L T → R G1 L1 T1) →
                   ∀G1,L1,T1. ⦃G1, L1, T1⦄ >≡[h, g] ⦃G2, L2, T2⦄ → R G1 L1 T1.
#h #g #G2 #L2 #T2 #R #IH1 #IH2 #G1 #L1 #T1 #H
@(tri_TC_ind_dx … IH1 IH2 G1 L1 T1 H)
qed-.
