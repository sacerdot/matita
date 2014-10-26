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

include "basic_2/multiple/llpx_sn_lreq.ma".
include "basic_2/multiple/lleq.ma".

(* LAZY EQUIVALENCE FOR LOCAL ENVIRONMENTS **********************************)

(* Properties on equivalence for local environments *************************)

lemma lreq_lleq_trans: ∀L2,L,T,l. L2 ≡[T, l] L →
                       ∀L1. L1 ⩬[l, ∞] L2 → L1 ≡[T, l] L.
/2 width=3 by lreq_llpx_sn_trans/ qed-.

lemma lleq_lreq_trans: ∀L,L1,T,l. L ≡[T, l] L1 →
                       ∀L2. L1 ⩬[l, ∞] L2 → L ≡[T, l] L2.
/2 width=3 by llpx_sn_lreq_trans/ qed-.

lemma lleq_lreq_repl: ∀L1,L2,T,l. L1 ≡[T, l] L2 → ∀K1. K1 ⩬[l, ∞] L1 →
                      ∀K2. L2 ⩬[l, ∞] K2 → K1 ≡[T, l] K2.
/2 width=5 by llpx_sn_lreq_repl/ qed-.

lemma lleq_bind_repl_SO: ∀I1,I2,L1,L2,V1,V2,T. L1.ⓑ{I1}V1 ≡[T, 0] L2.ⓑ{I2}V2 →
                         ∀J1,J2,W1,W2. L1.ⓑ{J1}W1 ≡[T, 1] L2.ⓑ{J2}W2.
/2 width=5 by llpx_sn_bind_repl_SO/ qed-.
