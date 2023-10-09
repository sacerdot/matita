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

include "ground/arith/pnat_tri.ma".
include "ground/arith/nat.ma".

(* TRICHOTOMY OPERATOR FOR NON-NEGATIVE INTEGERS ****************************)

(* Note: this is "if eqb n1 n2 then a2 else if leb n1 n2 then a1 else a3" *)
(*** tri *)
definition ntri (A:Type[0]) (n1) (n2) (a1) (a2) (a3): A ≝
  match n1 with
  [ nzero    ⇒ match n2 with [ nzero ⇒ a2 | npos p2 ⇒ a1 ]
  | npos  p1 ⇒ match n2 with [ nzero ⇒ a3 | npos p2 ⇒ ptri A p1 p2 a1 a2 a3 ]
  ].

(* Basic constructions ******************************************************)

lemma ntri_zero_bi (A) (a1) (a2) (a3):
      a2 = ntri A (𝟎) (𝟎) a1 a2 a3.
// qed.

lemma ntri_zero_pos (A) (a1) (a2) (a3) (p):
      a1 = ntri A (𝟎) (⁤p) a1 a2 a3.
// qed.

lemma ntri_pos_zero (A) (a1) (a2) (a3) (p):
      a3 = ntri A (⁤p) (𝟎) a1 a2 a3.
// qed.

lemma ntri_pos_bi (A) (a1) (a2) (a3) (p1) (p2):
      ptri A (p1) (p2) a1 a2 a3 = ntri A (⁤p1) (⁤p2) a1 a2 a3.
// qed.

(* Advanced constructions ***************************************************)

(*** tri_eq *)
lemma ntri_eq (A) (a1) (a2) (a3) (n): a2 = ntri A n n a1 a2 a3.
#A #a1 #a2 #a3 * //
qed.

lemma ntri_f_tri (A) (B) (f) (a1) (a2) (a3) (n1) (n2):
      f (ntri A n1 n2 a1 a2 a3) = ntri B n1 n2 (f a1) (f a2) (f a3).
#A #B #f #a1 #a2 #a3
* [| #p1 ] * // #p2
<ntri_pos_bi <ntri_pos_bi //
qed.
