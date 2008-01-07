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



include "nat/div_and_mod.ma".
include "nat/factorial.ma".
include "nat/primes.ma".

theorem prova : \forall n. (n+O)*(S O) = n.
intro.
applyS times_n_SO.
qed.

lemma foo: ∀n.(S n)! = (S n) * n!.
intro; reflexivity.
qed.

theorem prova2 :
 \forall n. S n \divides (S n)!.
intros.
(* se non trova subito sym_times poi si perde! *)
(* alternativamente si puo' abilitare la are_convertible nella
   is_identity, ma poi va peggio nel resto (conv lunghe) *)
letin www \def sym_times.
clearbody www.
applyS (witness ? ? ? (refl_eq ? ?)).
qed.
