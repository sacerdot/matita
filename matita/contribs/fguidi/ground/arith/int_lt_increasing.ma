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

include "ground/arith/int_lt.ma".

(* STRICT ORDER FOR INTEGERS ************************************************)

definition int_increasing_2: predicate (ℤ→ℤ) ≝
           λf. ∀z1,z2. z1 < z2 → f z1 < f z2.

definition int_increasing_1: predicate (ℤ→ℤ) ≝
           λf. ∀z. f z < f (↑z).

(* Constructions with increasing functions **********************************)

lemma int_increasing_2_1 (f):
      int_increasing_2 f → int_increasing_1 f.
/2 width=1 by/
qed.

lemma int_increasing_1_2 (f):
      int_increasing_1 f → int_increasing_2 f.
#f #Hf #z1 #z2 #Hz elim Hz -z2
/2 width=3 by zlt_trans/
qed-.
