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

include "ground_2/notation/functions/successor_1.ma".
include "ground_2/ynat/ynat_pred.ma".

(* NATURAL NUMBERS WITH INFINITY ********************************************)

(* the successor function *)
definition ysucc: ynat → ynat ≝ λm. match m with
[ yinj m ⇒ S m
| Y      ⇒ Y
].

interpretation "ynat successor" 'Successor m = (ysucc m).

(* Properties ***************************************************************)

lemma ypred_succ: ∀m. ⫰⫯m = m.
* // qed.

(* Inversion lemmas *********************************************************)

lemma ysucc_inj: ∀m,n. ⫯m = ⫯n → m = n.
#m #n #H <(ypred_succ m) <(ypred_succ n) //
qed-.

lemma ysucc_inv_refl: ∀m. ⫯m = m → m = ∞.
* // normalize
#m #H lapply (yinj_inj … H) -H (**) (* destruct lemma needed *)
#H elim (lt_refl_false m) //
qed-.

lemma ysucc_inv_inj_sn: ∀m2,n1. yinj m2 = ⫯n1 →
                        ∃∃m1. n1 = yinj m1 & m2 = S m1.
#m2 * normalize
[ #n1 #H destruct /2 width=3 by ex2_intro/
| #H destruct
]
qed-.

lemma ysucc_inv_inj_dx: ∀m2,n1. ⫯n1 = yinj m2  →
                        ∃∃m1. n1 = yinj m1 & m2 = S m1.
/2 width=1 by ysucc_inv_inj_sn/ qed-.
