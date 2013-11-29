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

include "ground_2/ynat/ynat_lt.ma".

(* NATURAL NUMBERS WITH INFINITY ********************************************)

(* addition *)
definition yplus: ynat → ynat → ynat ≝ λx,y. match x with
[ yinj m ⇒ ysucc^m y
| Y      ⇒ Y
].

interpretation "ynat plus" 'plus x y = (yplus x y).

(* Properties on successor **************************************************)

lemma yplus_succ1: ∀m,n. (⫯m) + n = ⫯(m + n).
* //
qed.

lemma yplus_SO1: ∀m. 1 + m = ⫯m.
* //
qed. 

(* Basic properties *********************************************************)

lemma yplus_inj: ∀m,n. yinj m + yinj n = yinj (m + n).
#m elim m -m //
#m #IHm #n >(yplus_succ1 m) >IHm -IHm //
qed.

lemma yplus_Y2: ∀m. (m + ∞) = ∞.
* normalize //
qed.

lemma yplus_comm: commutative … yplus.
* [ #m ] * [1,3: #n ] //
normalize >ysucc_iter_Y //
qed.

lemma yplus_assoc: associative … yplus.
* // #x * //
#y #z >yplus_inj whd in ⊢ (??%%); >iter_plus //
qed.

