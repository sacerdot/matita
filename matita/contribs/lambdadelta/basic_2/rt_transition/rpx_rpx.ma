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

include "static_2/static/rex_rex.ma".
include "basic_2/rt_transition/rpx.ma".

(* EXTENDED PARALLEL RT-TRANSITION FOR REFERRED LOCAL ENVIRONMENTS **********)

(* Main properties **********************************************************)

theorem rpx_bind (G):
        ∀L1,L2,V1. ❨G,L1❩ ⊢ ⬈[V1] L2 →
        ∀I,V2,T. ❨G,L1.ⓑ[I]V1❩ ⊢ ⬈[T] L2.ⓑ[I]V2 →
        ∀p. ❨G,L1❩ ⊢ ⬈[ⓑ[p,I]V1.T] L2.
/2 width=2 by rex_bind/ qed.

theorem rpx_flat (G):
        ∀L1,L2,V. ❨G,L1❩ ⊢ ⬈[V] L2 →
        ∀I,T. ❨G,L1❩ ⊢ ⬈[T] L2 → ❨G,L1❩ ⊢ ⬈[ⓕ[I]V.T] L2.
/2 width=1 by rex_flat/ qed.

theorem rpx_bind_void (G):
        ∀L1,L2,V. ❨G,L1❩ ⊢ ⬈[V] L2 →
        ∀T. ❨G,L1.ⓧ❩ ⊢ ⬈[T] L2.ⓧ →
        ∀p,I. ❨G,L1❩ ⊢ ⬈[ⓑ[p,I]V.T] L2.
/2 width=1 by rex_bind_void/ qed.
