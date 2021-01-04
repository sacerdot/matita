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

include "ground/arith/pnat.ma".

(* TRICHOTOMY OPERATOR FOR POSITIVE INTEGERS ********************************)

rec definition ptri (A:Type[0]) p1 p2 a1 a2 a3 on p1 : A ≝
  match p1 with
  [ punit    ⇒ match p2 with [ punit ⇒ a2 | psucc p2 ⇒ a1 ]
  | psucc p1 ⇒ match p2 with [ punit ⇒ a3 | psucc p2 ⇒ ptri A p1 p2 a1 a2 a3 ]
  ].

(* Basic rewrites ***********************************************************)

lemma ptri_unit_bi (A) (a1) (a2) (a3):
      a2 = ptri A (𝟏) (𝟏) a1 a2 a3.
// qed.

lemma ptri_unit_succ (A) (a1) (a2) (a3) (p):
      a1 = ptri A (𝟏) (↑p) a1 a2 a3.
// qed.

lemma ptri_succ_unit (A) (a1) (a2) (a3) (p):
      a3 = ptri A (↑p) (𝟏) a1 a2 a3.
// qed.

lemma ptri_succ_bi (A) (a1) (a2) (a3) (p1) (p2):
      ptri A (p1) (p2) a1 a2 a3 = ptri A (↑p1) (↑p2) a1 a2 a3.
// qed.

(* Advanced rewrites ********************************************************)

lemma ptri_eq (A) (a1) (a2) (a3) (p): a2 = ptri A p p a1 a2 a3.
#A #a1 #a2 #a3 #p elim p -p //
qed.

lemma ptri_f_tri (A) (B) (f) (a1) (a2) (a3) (p1) (p2):
      f (ptri A p1 p2 a1 a2 a3) = ptri B p1 p2 (f a1) (f a2) (f a3).
#A #B #f #a1 #a2 #a3 #p1
elim p1 -p1 [| #p1 #IH ] * //
qed.
