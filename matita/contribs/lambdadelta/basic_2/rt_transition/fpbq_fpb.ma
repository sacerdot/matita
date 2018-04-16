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

include "basic_2/rt_transition/fpb_ffdeq.ma".
include "basic_2/rt_transition/fpbq.ma".

(* PARALLEL RST-TRANSITION FOR CLOSURES *************************************)

(* Properties with proper parallel rst-transition for closures **************)

lemma fpb_fpbq: ∀h,o,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ≻[h, o] ⦃G2, L2, T2⦄ →
                ⦃G1, L1, T1⦄ ≽[h, o] ⦃G2, L2, T2⦄.
#h #o #G1 #G2 #L1 #L2 #T1 #T2 * -G2 -L2 -T2
/3 width=1 by fpbq_fquq, fpbq_cpx, fpbq_lfpx, fqu_fquq/
qed.

(* Basic_2A1: fpb_fpbq_alt *)
lemma fpb_fpbq_ffdneq: ∀h,o,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ≻[h, o] ⦃G2, L2, T2⦄ →
                       ∧∧ ⦃G1, L1, T1⦄ ≽[h, o] ⦃G2, L2, T2⦄ & (⦃G1, L1, T1⦄ ≛[h, o] ⦃G2, L2, T2⦄ → ⊥).
/3 width=10 by fpb_fpbq, fpb_inv_ffdeq, conj/ qed-.

(* Inversrion lemmas with proper parallel rst-transition for closures *******)

(* Basic_2A1: uses: fpbq_ind_alt *)
lemma fpbq_inv_fpb: ∀h,o,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ≽[h, o] ⦃G2, L2, T2⦄ →
                    ∨∨ ⦃G1, L1, T1⦄ ≛[h, o] ⦃G2, L2, T2⦄
                     | ⦃G1, L1, T1⦄ ≻[h, o] ⦃G2, L2, T2⦄.
#h #o #G1 #G2 #L1 #L2 #T1 #T2 * -G2 -L2 -T2
[ #G2 #L2 #T2 * [2: * #H1 #H2 #H3 destruct ]
  /3 width=1 by fpb_fqu, ffdeq_intro_sn, or_intror, or_introl/
| #T2 #H elim (tdeq_dec h o T1 T2)
  /4 width=1 by fpb_cpx, ffdeq_intro_sn, or_intror, or_introl/
| #L2 elim (lfdeq_dec h o L1 L2 T1)
  /4 width=1 by fpb_lfpx, ffdeq_intro_sn, or_intror, or_introl/
| /2 width=1 by or_introl/
]
qed-.

(* Basic_2A1: fpbq_inv_fpb_alt *)
lemma fpbq_ffdneq_inv_fpb: ∀h,o,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ≽[h, o] ⦃G2, L2, T2⦄ →
                           (⦃G1, L1, T1⦄ ≛[h, o] ⦃G2, L2, T2⦄ → ⊥) → ⦃G1, L1, T1⦄ ≻[h, o] ⦃G2, L2, T2⦄.
#h #o #G1 #G2 #L1 #L2 #T1 #T2 #H #H0
elim (fpbq_inv_fpb … H) -H // #H elim H0 -H0 //
qed-.