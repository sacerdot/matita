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
include "ground/relocation/fb/fbr_dapp_eq.ma".

(* LEVEL APPLICATION FOR FINITE RELOCATION MAPS FOR UNWIND ******************)

(* Constructions with fbr_eq ************************************************)

lemma fbr_lapp_eq_repl (n):
      compatible_2_fwd … fbr_eq (eq …) (λf.f＠§❨n❩).
#n #f1 #f2 #Hf
<(fbr_dapp_eq_repl … Hf) -Hf //
qed.

(* Inversions with fbr_eq ***************************************************)

lemma fbr_eq_ext_lapp (f1) (f2):
      (∀n. f1＠§❨n❩ = f2＠§❨n❩) → f1 ≐ f2.
#f1 #f2 #Hf
@fbr_dxeq_inv_eq #p
<fbr_dapp_lapp >(Hf (↓p)) -Hf //
qed-.
