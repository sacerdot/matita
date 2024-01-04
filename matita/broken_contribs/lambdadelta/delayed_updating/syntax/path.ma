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

include "ground/lib/list_rcons.ma".
include "ground/notation/functions/element_e_0.ma".
include "ground/notation/functions/black_circle_2.ma".
include "ground/notation/functions/black_halfcircleright_2.ma".
include "ground/notation/functions/black_halfcircleleft_2.ma".
include "delayed_updating/syntax/label.ma".
include "delayed_updating/notation/functions/category_p_0.ma".

(* PATH *********************************************************************)

(* Note: a path is a list of labels *)
(* Note: constructed from the leaf (right end) to the root (left end) *)
interpretation
  "path ()"
  'CategoryP = (list label).

interpretation
  "empty (path)"
  'ElementE = (list_empty label).

interpretation
  "right cons (path)"
  'BlackHalfCircleLeft p l = (list_lcons label l p).

interpretation
  "append (path)"
  'BlackCircle p q = (list_append label q p).

interpretation
  "left cons (path)"
  'BlackHalfCircleRight l p = (list_append label p (list_lcons label l (list_empty label))).

(* Helper constructions *****************************************************)

lemma path_append_pbLq_1 (p) (b) (q):
      (p◖𝗔)●b●(𝗟◗q) = p●𝗔◗b●𝗟◗q.
//
qed-.

lemma path_append_pAbLq_2 (p1) (p2) (b1) (b2) (q) (l):
      (p2●p1●𝗔◗b1●b2●𝗟◗q)◖l = (p2●p1◖𝗔)●(b1●b2●𝗟◗q◖l).
// qed-.

lemma path_append_pAbLq_3 (p1) (p2) (b1) (b2) (q:ℙ):
      p2●p1●𝗔◗b1●b2●𝗟◗q = (p2●p1◖𝗔)●((b1●b2)●𝗟◗q).
// qed-.

lemma path_append_pAbLq_4 (p1) (p2) (b1) (b2) (q:ℙ):
      p2●p1●𝗔◗b1●b2●𝗟◗q = (p2●p1●𝗔◗b1●b2)●(𝗟◗q).
// qed-.

lemma path_append_pLq (p) (b) (q):
      (p●𝗔◗b)●𝗟◗q = p●𝗔◗b●𝗟◗q.
// qed-.

lemma path_append_pL (p) (b):
      (p●𝗔◗b)◖ 𝗟= (p◖𝗔)●b◖𝗟.
// qed-.

lemma path_append_append_lcons (p) (q) (r) (l):
      p●(r◖l)●q = p●r●(l◗q).
// qed-.

lemma path_append_lcons_append (p) (q) (r) (l):
      (p◖l)●r●q = p●(l◗r)●q.
// qed-.
