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

include "ground/relocation/fu/fur_xapp.ma".
include "ground/relocation/fu/fur_eq.ma".

(* Constructions with fur_eq ************************************************)

lemma fur_eq_xapp (f1) (f2):
      (∀n. f1＠❨n❩ = f2＠❨n❩) → f1 ≐ f2.
#f1 #f2 #Hf #p
lapply (Hf (⁤p)) -Hf
<fur_xapp_pos <fur_xapp_pos #H0
lapply (eq_inv_npos_bi … H0) -H0 //
qed.

(* Inversions with fur_eq ***************************************************)

lemma fur_xapp_eq_repl (n):
      compatible_2_fwd … fur_eq (eq …) (λf.f＠❨n❩).
* // #p #f1 #f2 #Hf
<fur_xapp_pos <fur_xapp_pos
<(fur_dapp_eq_repl … Hf) -Hf //
qed-.
