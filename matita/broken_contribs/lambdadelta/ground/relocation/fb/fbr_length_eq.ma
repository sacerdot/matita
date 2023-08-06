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

include "ground/relocation/fb/fbr_length.ma".
include "ground/relocation/fb/fbr_eq.ma".

(* LENGTH FOR FINITE RELOCATION MAPS WITH BOOLEANS **************************)

(* Constructions with fbr_eq ************************************************)

lemma fbr_length_eq_repl:
      compatible_2_fwd … fbr_eq (eq …) (λf.↔f).
#f1 #f2 #Hf elim Hf -f1 -f2 // [ * // ]
[ #f1 #f2 #_
  @(insert_eq_1 … (↔f2)) *
  [ #H1 #H2
    <(fbr_length_push_dx_zero f1) //
    <(fbr_length_push_dx_zero f2) //
  | #p #H1 #H2
    <(fbr_length_push_dx_pos f1) //
    <(fbr_length_push_dx_pos f2) //
  ]
| #f2 #_ #H2
  <(fbr_length_push_dx_zero f2) //
| #f1 #_ #H1
  <(fbr_length_push_dx_zero f1) //
]
qed.
