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

include "basic_2/rt_transition/fpb_feqx.ma".
include "basic_2/rt_transition/fpbq.ma".

(* PARALLEL RST-TRANSITION FOR CLOSURES *************************************)

(* Properties with proper parallel rst-transition for closures **************)

lemma fpb_fpbq: ∀h,G1,G2,L1,L2,T1,T2. ❪G1,L1,T1❫ ≻[h] ❪G2,L2,T2❫ →
                ❪G1,L1,T1❫ ≽[h] ❪G2,L2,T2❫.
#h #G1 #G2 #L1 #L2 #T1 #T2 * -G2 -L2 -T2
/3 width=1 by fpbq_fquq, fpbq_cpx, fpbq_lpx, fqu_fquq/
qed.

(* Basic_2A1: fpb_fpbq_alt *)
lemma fpb_fpbq_fneqx: ∀h,G1,G2,L1,L2,T1,T2. ❪G1,L1,T1❫ ≻[h] ❪G2,L2,T2❫ →
                       ∧∧ ❪G1,L1,T1❫ ≽[h] ❪G2,L2,T2❫ & (❪G1,L1,T1❫ ≛ ❪G2,L2,T2❫ → ⊥).
/3 width=10 by fpb_fpbq, fpb_inv_feqx, conj/ qed-.

(* Inversrion lemmas with proper parallel rst-transition for closures *******)

(* Basic_2A1: uses: fpbq_ind_alt *)
lemma fpbq_inv_fpb: ∀h,G1,G2,L1,L2,T1,T2. ❪G1,L1,T1❫ ≽[h] ❪G2,L2,T2❫ →
                    ∨∨ ❪G1,L1,T1❫ ≛ ❪G2,L2,T2❫
                     | ❪G1,L1,T1❫ ≻[h] ❪G2,L2,T2❫.
#h #G1 #G2 #L1 #L2 #T1 #T2 * -G2 -L2 -T2
[ #G2 #L2 #T2 * [2: * #H1 #H2 #H3 destruct ]
  /3 width=1 by fpb_fqu, feqx_intro_sn, or_intror, or_introl/
| #T2 #H elim (teqx_dec T1 T2)
  /4 width=1 by fpb_cpx, feqx_intro_sn, or_intror, or_introl/
| #L2 elim (reqx_dec L1 L2 T1)
  /4 width=1 by fpb_lpx, feqx_intro_sn, or_intror, or_introl/
| /2 width=1 by or_introl/
]
qed-.

(* Basic_2A1: fpbq_inv_fpb_alt *)
lemma fpbq_fneqx_inv_fpb: ∀h,G1,G2,L1,L2,T1,T2. ❪G1,L1,T1❫ ≽[h] ❪G2,L2,T2❫ →
                           (❪G1,L1,T1❫ ≛ ❪G2,L2,T2❫ → ⊥) → ❪G1,L1,T1❫ ≻[h] ❪G2,L2,T2❫.
#h #G1 #G2 #L1 #L2 #T1 #T2 #H #H0
elim (fpbq_inv_fpb … H) -H // #H elim H0 -H0 //
qed-.
