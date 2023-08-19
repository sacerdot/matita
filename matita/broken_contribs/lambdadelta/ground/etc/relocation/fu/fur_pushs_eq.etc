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

include "ground/relocation/fu/fur_pushs.ma".
include "ground/relocation/fu/fur_eq.ma".

(* ITERATED PUSH FOR FINITE RELOCATION MAPS FOR UNWIND **********************)

(* Constructions with fur_eq ************************************************)

lemma fur_pushs_eq_repl (n):
      compatible_2_fwd … fur_eq fur_eq (λf.⫯*[n]f).
#n @(nat_ind_succ … n) -n
/3 width=1 by fur_push_eq_repl/
qed.

lemma fur_pushs_id (n):
      (𝐢) ≐ ⫯*[n]𝐢.
#n @(nat_ind_succ … n) -n
/2 width=1 by fur_push_eq_repl/
qed.
