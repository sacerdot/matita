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

include "ground/relocation/fb/fbr_after.ma".
include "ground/relocation/fb/fbr_eq.ma".

(* COMPOSITION FOR FINITE RELOCATION MAPS WITH BOOLEANS *********************)

(* Constructions with fbr_eq ************************************************)

lemma fbr_after_eq_repl:
      compatible_3 … fbr_eq fbr_eq fbr_eq (λg,f.g•f).
#g1 #g2 #Hg elim Hg -g1 -g2 //
[ * #g1 #g2 #_ #IH #f1 #f2 [ #Hf | * ]
  /3 width=1 by fbr_eq_rcons_bi/
| #g2 #_ #IH #f1 #f2 *
  /3 width=1 by fbr_eq_rcons_bi, fbr_eq_id_push/
| #g1 #_ #IH #f1 #f2 *
  /3 width=1 by fbr_eq_rcons_bi, fbr_eq_push_id/
]
qed.
