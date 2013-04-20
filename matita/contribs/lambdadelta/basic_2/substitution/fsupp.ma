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

include "basic_2/relocation/fsup.ma".

(* PLUS-ITERATED SUPCLOSURE *************************************************)

definition fsupp: bi_relation lenv term ≝ bi_TC … fsup.

interpretation "plus-iterated structural successor (closure)"
   'SupTermPlus L1 T1 L2 T2 = (fsupp L1 T1 L2 T2).

(* Basic eliminators ********************************************************)

lemma fsupp_ind: ∀L1,T1. ∀R:relation2 lenv term.
                 (∀L2,T2. ⦃L1, T1⦄ ⊃ ⦃L2, T2⦄ → R L2 T2) →
                 (∀L,T,L2,T2. ⦃L1, T1⦄ ⊃+ ⦃L, T⦄ → ⦃L, T⦄ ⊃ ⦃L2, T2⦄ → R L T → R L2 T2) →
                 ∀L2,T2. ⦃L1, T1⦄ ⊃+ ⦃L2, T2⦄ → R L2 T2.
#L1 #T1 #R #IH1 #IH2 #L2 #T2 #H
@(bi_TC_ind … IH1 IH2 ? ? H)
qed-.

lemma fsupp_ind_dx: ∀L2,T2. ∀R:relation2 lenv term.
                    (∀L1,T1. ⦃L1, T1⦄ ⊃ ⦃L2, T2⦄ → R L1 T1) →
                    (∀L1,L,T1,T. ⦃L1, T1⦄ ⊃ ⦃L, T⦄ → ⦃L, T⦄ ⊃+ ⦃L2, T2⦄ → R L T → R L1 T1) →
                    ∀L1,T1. ⦃L1, T1⦄ ⊃+ ⦃L2, T2⦄ → R L1 T1.
#L2 #T2 #R #IH1 #IH2 #L1 #T1 #H
@(bi_TC_ind_dx … IH1 IH2 ? ? H)
qed-.

(* Basic properties *********************************************************)

lemma fsup_fsupp: ∀L1,L2,T1,T2. ⦃L1, T1⦄ ⊃ ⦃L2, T2⦄ → ⦃L1, T1⦄ ⊃+ ⦃L2, T2⦄.
/2 width=1/ qed.

lemma fsupp_strap1: ∀L1,L,L2,T1,T,T2. ⦃L1, T1⦄ ⊃+ ⦃L, T⦄ → ⦃L, T⦄ ⊃ ⦃L2, T2⦄ →
                    ⦃L1, T1⦄ ⊃+ ⦃L2, T2⦄.
/2 width=4/ qed.

lemma fsupp_strap2: ∀L1,L,L2,T1,T,T2. ⦃L1, T1⦄ ⊃ ⦃L, T⦄ → ⦃L, T⦄ ⊃+ ⦃L2, T2⦄ →
                    ⦃L1, T1⦄ ⊃+ ⦃L2, T2⦄.
/2 width=4/ qed.

(* Basic forward lemmas *****************************************************)

lemma fsupp_fwd_cw: ∀L1,L2,T1,T2. ⦃L1, T1⦄ ⊃+ ⦃L2, T2⦄ → ♯{L2, T2} < ♯{L1, T1}.
#L1 #L2 #T1 #T2 #H @(fsupp_ind … H) -L2 -T2
/3 width=3 by fsup_fwd_cw, transitive_lt/
qed-.
