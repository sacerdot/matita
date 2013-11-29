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

lemma ynat_cases: ∀n:ynat. n = 0 ∨ ∃m. n = ⫯m.
*
[ * /2 width=1 by or_introl/
  #n @or_intror @(ex_intro … n) // (**) (* explicit constructor *)
| @or_intror @(ex_intro … (∞)) // (**) (* explicit constructor *)
]
qed-.

lemma ysucc_iter_Y: ∀m. ysucc^m (∞) = ∞.
#m elim m -m //
#m #IHm whd in ⊢ (??%?); >IHm //
qed.

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

lemma ysucc_inv_Y_sn: ∀m. ∞ = ⫯m → m = ∞.
* // normalize
#m #H destruct
qed-.

lemma ysucc_inv_Y_dx: ∀m. ⫯m = ∞ → m = ∞.
/2 width=1 by ysucc_inv_Y_sn/ qed-.

lemma ysucc_inv_O_sn: ∀m. yinj 0 = ⫯m → ⊥. (**) (* explicit coercion *)
#m #H elim (ysucc_inv_inj_sn … H) -H
#n #_ #H destruct
qed-.

lemma ysucc_inv_O_dx: ∀m. ⫯m = 0 → ⊥.
/2 width=2 by ysucc_inv_O_sn/ qed-.
