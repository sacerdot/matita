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

include "explicit_updating/reduction/xbeta_flat.ma".
include "explicit_updating/reduction/xstep.ma".

(* X-REDUCTION **************************************************************)

(* Constructions with xbetaand xbeta1 ***************************************)

lemma xstep_beta_flat:
      flattenable (xstep (𝛃′)) (xstep (𝛃ⓕ)).
#t1 #t2 #Ht elim Ht -t1 -t2
[ /3 width=1 by xbeta_flat, xstep_step/
| /2 width=1 by xstep_abst/
| /3 width=1 by xstep_side, term_flat_eq_repl/
| /3 width=1 by xstep_head, term_flat_eq_repl/
| /2 width=1 by xstep_lift/
]
qed.
