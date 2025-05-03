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

include "ground/relocation/fb/fbr_lapp.ma".
include "ground/relocation/fb/fbr_dapp_lt.ma".

(* LEVEL APPLICATION FOR FINITE RELOCATION MAPS WITH BOOLEANS ***************)

(* Advanced constructions ***************************************************)

lemma is_fbr_lapp_dec (f) (n2):
      Decidable (∃n1. n2 = f＠§❨n1❩).
#f #n2 elim (is_fbr_dapp_dec f (↑n2))
[ * /3 width=2 by ex_intro, or_introl/
| #H @or_intror * /3 width=2 by ex_intro/
]
qed-.
