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

include "nat/order.ma".
include "algebra/magmas.ma".

alias symbol "eq" = "leibnitz's equality".
alias id "refl" = "cic:/matita/ng/logic/equality/eq.con(0,1,2)".
nlet rec big_op (M: magma_type) (n: nat) (f: ∀m. lt m n → M) (v: M) on n : M ≝
 (match n return λx.∀p:n=x.? with
   [ O ⇒ λ_.v
   | S n' ⇒ λp.op ? (f n' ?) (big_op M n' ? v) ]) (refl ? n).
##[ nrewrite > p; napply le_n
  | #m; #H; napply (f m); nrewrite > p; napply le_S; nassumption]
nqed.