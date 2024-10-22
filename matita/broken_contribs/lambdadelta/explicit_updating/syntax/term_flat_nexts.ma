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

include "explicit_updating/syntax/term_nexts.ma".
include "explicit_updating/syntax/term_flat_next.ma".

(* FLATTENING FOR TERM ******************************************************)

(* Constructions with term_nexts ********************************************)

lemma term_flat_nexts (n) (t):
      ↑*[n]♭t = ♭↑*[n]t.
#n @(nat_ind_succ … n) -n //
qed.
