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

include "static_2/static/reqg_fqup.ma".
include "static_2/static/reqx.ma".
include "basic_2/rt_transition/lpx.ma".
include "basic_2/rt_transition/rpx.ma".

(* EXAMPLES *****************************************************************)

(* Lemma "rpx_fwd_lpx_reqx" is not an inversion *****************************)

definition L1 (K) (s1) (s0): lenv ≝ K.ⓛ⋆s1.ⓛⓝ#0.⋆s0.

definition L (K) (s1) (s0): lenv ≝ K.ⓛ⋆s1.ⓛ⋆s0.

definition L2 (K) (i1) (s0): lenv ≝ K.ⓛ#i1.ⓛ⋆s0.

definition T: term ≝ #0.

(* Basic properties *********************************************************)

lemma ex_rpx_fwd_1 (G) (K) (s1) (s0):
      ❨G,L1 K s1 s0❩ ⊢ ⬈ L K s1 s0.
/3 width=1 by lpx_pair, lpx_bind_refl_dx, cpx_eps/ qed.

lemma ex_rpx_fwd_2 (K) (s1) (s0) (i1) (i0):
      L K s1 s0 ≅[T] L2 K i1 i0.
/4 width=1 by reqg_refl, reqg_pair, reqg_sort, teqg_sort/ qed.

lemma ex_rpx_fwd_3 (G) (K) (s1) (s0) (i1) (i0):
      ❨G,L1 K s1 s0❩ ⊢ ⬈[T] L2 K i1 i0 → ⊥.
#G #K #s1 #s0 #i1 #i0 #H
elim (rpx_inv_zero_pair_sn … H) -H #Y2 #X2 #H #_ normalize #H0 destruct
elim (rpx_inv_flat … H) -H #H #_
elim (rpx_inv_zero_pair_sn … H) -H #Y2 #X2 #_ #H #H0 destruct
elim (cpx_inv_sort1 … H) #s2 #H destruct
qed-.

(* Main properties **********************************************************)

theorem ex_rpx_fwd (G) (K) (s1) (s0) (i1) (i0):
        (❨G,L1 K s1 s0❩ ⊢ ⬈ L K s1 s0 → L K s1 s0 ≅[T] L2 K i1 i0 → ❨G,L1 K s1 s0❩ ⊢ ⬈[T] L2 K i1 i0) → ⊥.
/3 width=7 by ex_rpx_fwd_3, ex_rpx_fwd_2, ex_rpx_fwd_1/ qed-.
