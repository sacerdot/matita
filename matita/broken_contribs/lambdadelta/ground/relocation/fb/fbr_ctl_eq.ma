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

include "ground/relocation/fb/fbr_ctl.ma".
include "ground/relocation/fb/fbr_eq.ma".

(* COARSE TAIL FOR FINITE RELOCATION MAPS WITH BOOLEANS *********************)

lemma fbr_ctl_eq_repl:
      compatible_2_fwd … fbr_eq fbr_eq (λf.⫰f).
#f1 #f2 #Hf elim Hf -f1 -f2 //
* #f1 #f2 #Hf #IH //
qed.
