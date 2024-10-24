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

include "explicit_updating/reduction/xbeta.ma".
include "explicit_updating/reduction/xbeta1.ma".

(* β-REDUCTION STEP *********************************************************)

(* Constructions witth xbeta1 ***********************************************)

alias symbol "subseteq" (instance 1) = "2-relation inclusion".
lemma xbeta_beta1 (b):
      (𝛃b) ⊆ (𝛃′).
#b #t1 #t2 * -t1 -t2
/2 width=5 by xbeta_unwind, xbeta_beta/
qed.
