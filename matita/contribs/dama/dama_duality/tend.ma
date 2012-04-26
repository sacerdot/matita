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

include "sequence.ma".
include "metric_space.ma".
include "nat/orders.ma".

definition tends0 ≝ 
  λO:pogroup.λs:sequence O.∀e:O.0 < e → ∃N.∀n.N < n → -e < s n ∧ s n < e.

definition d2s ≝ 
  λR.λms:metric_space R.λs:sequence ms.λk.λn. δ (s n) k.

notation "s ⇝ x" non associative with precedence 55 for @{'tends $s $x}.
interpretation "tends to" 'tends s x = (tends0 ? (d2s ? ? s x)).

