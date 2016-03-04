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

include "ground_2/ynat/ynat.ma".

(* NATURAL NUMBERS WITH INFINITY ********************************************)

(* the predecessor function *)
definition ypred: ynat → ynat ≝ λm. match m with
[ yinj m ⇒ ⫰m
| Y      ⇒ Y
].

interpretation "ynat predecessor" 'Predecessor m = (ypred m).

lemma ypred_O: ⫰(yinj 0) = yinj 0.
// qed.

lemma ypred_S: ∀m:nat. ⫰(⫯m) = yinj m.
// qed.

lemma ypred_Y: (⫰∞) = ∞.
// qed.

(* Inversion lemmas *********************************************************)

lemma ypred_inv_refl: ∀m:ynat. ⫰m = m → m = 0 ∨ m = ∞.
* // #m #H lapply (yinj_inj … H) -H (**) (* destruct lemma needed *)
/4 width=1 by pred_inv_refl, or_introl, eq_f/
qed-.
