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

include "basic_2/notation/relations/predsubtyproper_6.ma".
include "static_2/static/feqx.ma".
include "basic_2/rt_transition/fpb.ma".

(* PROPER PARALLEL RST-TRANSITION FOR CLOSURES ******************************)

(* Basic_2A1: uses: fpb *)
definition fpbc (G1) (L1) (T1) (G2) (L2) (T2): Prop ≝
           ∧∧ ❪G1,L1,T1❫ ≽ ❪G2,L2,T2❫
            & (❪G1,L1,T1❫ ≅ ❪G2,L2,T2❫ → ⊥).

interpretation
  "proper parallel rst-transition (closure)"
  'PRedSubTyProper G1 L1 T1 G2 L2 T2 = (fpbc G1 L1 T1 G2 L2 T2).

(* Basic properties *********************************************************)

(* Basic_2A1: fpbq_inv_fpb_alt *)
lemma fpbc_intro (G1) (L1) (T1) (G2) (L2) (T2):
      ❪G1,L1,T1❫ ≽ ❪G2,L2,T2❫ → (❪G1,L1,T1❫ ≅ ❪G2,L2,T2❫ → ⊥) →
      ❪G1,L1,T1❫ ≻ ❪G2,L2,T2❫.
/3 width=1 by conj/ qed.

lemma rpx_fpbc (G) (T):
      ∀L1,L2. ❪G,L1❫ ⊢ ⬈[T] L2 → (L1 ≅[T] L2 → ⊥) → ❪G,L1,T❫ ≻ ❪G,L2,T❫.
/4 width=4 by fpbc_intro, rpx_fpb, feqg_fwd_reqg_sn/ qed.  

(* Basic inversion lemmas ***************************************************)

(* Basic_2A1: uses: fpb_fpbq_alt *)
lemma fpbc_inv_gen (S):
      ∀G1,G2,L1,L2,T1,T2. ❪G1,L1,T1❫ ≻ ❪G2,L2,T2❫ →
      ∧∧ ❪G1,L1,T1❫ ≽ ❪G2,L2,T2❫ & (❪G1,L1,T1❫ ≛[S] ❪G2,L2,T2❫ → ⊥).
#S #G1 #G2 #L1 #L2 #T1 #T2 *
/4 width=2 by feqg_feqx, conj/
qed-.

(* Basic forward lemmas *****************************************************)

(* Basic_2A1: uses: fpb_fpbq *)
lemma fpbc_fwd_fpb:
      ∀G1,G2,L1,L2,T1,T2. ❪G1,L1,T1❫ ≻ ❪G2,L2,T2❫ →
      ❪G1,L1,T1❫ ≽ ❪G2,L2,T2❫.
#G1 #G2 #L1 #L2 #T1 #T2 * //
qed-.
