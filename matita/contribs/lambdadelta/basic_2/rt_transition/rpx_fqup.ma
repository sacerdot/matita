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

include "static_2/static/rex_fqup.ma".
include "basic_2/rt_transition/rpx.ma".

(* UNBOUND PARALLEL RT-TRANSITION FOR REFERRED LOCAL ENVIRONMENTS ***********)

(* Advanced properties ******************************************************)

lemma rpx_refl: ∀h,G,T. reflexive … (rpx h G T).
/2 width=1 by rex_refl/ qed.

lemma rpx_pair_refl: ∀h,G,L,V1,V2. ❪G,L❫ ⊢ V1 ⬈[h] V2 →
                     ∀I,T. ❪G,L.ⓑ[I]V1❫ ⊢ ⬈[h,T] L.ⓑ[I]V2.
/2 width=1 by rex_pair_refl/ qed.

(* Advanced inversion lemmas ************************************************)

lemma rpx_inv_bind_void: ∀h,p,I,G,L1,L2,V,T. ❪G,L1❫ ⊢ ⬈[h,ⓑ[p,I]V.T] L2 →
                         ∧∧ ❪G,L1❫ ⊢ ⬈[h,V] L2 & ❪G,L1.ⓧ❫ ⊢ ⬈[h,T] L2.ⓧ.
/2 width=3 by rex_inv_bind_void/ qed-.

(* Advanced forward lemmas **************************************************)

lemma rpx_fwd_bind_dx_void: ∀h,p,I,G,L1,L2,V,T.
                            ❪G,L1❫ ⊢ ⬈[h,ⓑ[p,I]V.T] L2 → ❪G,L1.ⓧ❫ ⊢ ⬈[h,T] L2.ⓧ.
/2 width=4 by rex_fwd_bind_dx_void/ qed-.
