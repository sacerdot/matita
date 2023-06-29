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

include "ground/relocation/fu/fur_lapp.ma".
include "ground/relocation/fu/fur_eq.ma".

(* LEVEL APPLICATION FOR FINITE RELOCATION MAPS FOR UNWIND ******************)

(* Constructions with fur_eq ************************************************)

lemma fur_lapp_eq_repl (n):
      compatible_2_fwd … fur_eq (eq …) (λf.f＠§❨n❩).
/2 width=1 by fur_dapp_eq_repl/
qed.

(* Inversions with fur_eq ***************************************************)

lemma fur_eq_ext_lapp (f1) (f2):
      (∀n. f1＠§❨n❩ = f2＠§❨n❩) → f1 ≐ f2.
#f1 #f2 #Hf #n0
<fur_dapp_lapp <fur_dapp_lapp in ⊢ (???%); //
qed-.
