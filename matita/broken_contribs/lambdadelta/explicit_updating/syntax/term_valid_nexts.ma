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
include "explicit_updating/syntax/term_valid_next.ma".

(* VALIDITY FOR TERM ********************************************************)

(* Constructions with term_nexts ********************************************)

lemma term_valid_nexts (b) (n) (t):
      b ⊢ t → b ⊢ ↑*[n]t.
#b #n @(nat_ind_succ … n) -n //
#n #IH #t #Ht
/3 width=1 by term_valid_next/
qed.

(* Inversions with term_nexts ***********************************************)

lemma term_valid_inv_nexts (b) (n) (t):
      b ⊢ ↑*[n]t → b ⊢ t.
#b #n @(nat_ind_succ … n) -n //
#n #IH #t #Ht
/3 width=1 by term_valid_inv_next/
qed-.
