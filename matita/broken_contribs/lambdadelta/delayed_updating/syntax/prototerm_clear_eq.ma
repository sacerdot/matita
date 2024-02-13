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

include "delayed_updating/syntax/prototerm_eq.ma".
include "delayed_updating/syntax/prototerm_clear.ma".

(* CLEARED PROTOTERM ********************************************************)

(* Constructions with equivalence for prototerm *****************************)

lemma clear_pt_append (p) (t):
      (⓪p)●(⓪t) ⇔ ⓪(p●t).
#p #t @conj #r * #s * #q #Hq #H1 #H2 destruct
/3 width=1 by pt_append_in, in_comp_term_clear/
qed.
