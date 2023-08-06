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

include "ground/relocation/fb/fbr_width.ma".
include "ground/relocation/fb/fbr_eq.ma".

(* WIDTH FOR FINITE RELOCATION MAPS WITH BOOLEANS ***************************)

(* Constructions with fbr_eq ************************************************)

lemma fbr_width_eq_repl:
      compatible_2_fwd … fbr_eq (eq …) (λf.↕f).
#f1 #f2 #Hf elim Hf -f1 -f2 // * //
qed.
