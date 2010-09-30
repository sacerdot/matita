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

include "nat/plus.ma".

alias num (instance 0) = "natural number".
lemma ex1: ∀n:nat. n ≠ n+0 → n = O+O → (∀n1.¬¬(n≠n1+O)) → False.
 intros (n U V K);
 elim n in U:(? (? ? ? %)) ⊢ %;
  [ apply (H V)
  | apply (K ? H)]
qed.