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

include "ground_2/notation/functions/predecessor_1.ma".
include "ground_2/lib/arith.ma".
include "ground_2/ynat/ynat.ma".

(* NATURAL NUMBERS WITH INFINITY ********************************************)

(* the predecessor function *)
definition ypred: ynat → ynat ≝ λm. match m with
[ yinj m ⇒ pred m
| Y      ⇒ Y
].

interpretation "ynat predecessor" 'Predecessor m = (ypred m).

(* Properties ***************************************************************)

lemma ypred_inj_rew: ∀m:nat. ⫰m = pred m.
// qed.

(* Inversion lemmas *********************************************************)

lemma ypred_inv_refl: ∀m. ⫰m = m → m = 0 ∨ m = ∞.
* // #m #H lapply (yinj_inj … H) -H (**) (* destruct lemma needed *)
/4 width=1 by pred_inv_refl, or_introl, eq_f/
qed-.
