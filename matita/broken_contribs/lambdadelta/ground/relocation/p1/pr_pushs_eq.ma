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

include "ground/relocation/p1/pr_eq.ma".
include "ground/relocation/p1/pr_pushs.ma".

(* ITERATED PUSH FOR PARTIAL RELOCATION MAPS ********************************)

(* Constructions with pr_eq *************************************************)

(*** pushs_eq_repl *)
lemma pr_pushs_eq_repl (n):
      pr_eq_repl (λf1,f2. ⫯*[n] f1 ≐ ⫯*[n] f2).
#n @(nat_ind_succ … n) -n
/3 width=5 by pr_eq_push/
qed-.
