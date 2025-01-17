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

include "delayed_updating/syntax/path.ma".

(* PATH *********************************************************************)

(* Helper constructions *****************************************************)

lemma path_append_append_lcons (p) (q) (r) (l):
      p●(r◖l)●q = p●r●(l◗q).
// qed-.

lemma path_append_lcons_append (p) (q) (r) (l):
      (p◖l)●r●q = p●(l◗r)●q.
// qed-.

lemma path_append_pLbLq (p) (b1) (b2) (q:ℙ):
      p●𝗟◗(b1●b2●𝗟◗q) = ((p●𝗟◗b1)●b2)●𝗟◗q.
// qed.

lemma path_append_pAbLq_1 (p) (b) (q):
      (p◖𝗔)●b●(𝗟◗q) = p●𝗔◗b●𝗟◗q.
//
qed-.

lemma path_append_pAbLq_2 (p1) (p2) (b1) (b2) (q) (l):
      (p2●p1●𝗔◗b1●b2●𝗟◗q)◖l = (p2●p1◖𝗔)●(b1●b2●𝗟◗q◖l).
// qed-.

lemma path_append_pAbLq_3 (p1) (p2) (b1) (b2) (q):
      p1●p2●𝗔◗b1●b2●𝗟◗q = (p1●p2◖𝗔)●((b1●b2)●𝗟◗q).
// qed-.

lemma path_append_pAbLq_4 (p1) (p2) (b1) (b2) (q):
      p1●p2●𝗔◗b1●b2●𝗟◗q = (p1●p2●𝗔◗b1●b2)●(𝗟◗q).
// qed-.

lemma path_append_pAbLq_5 (p) (b) (q):
      p●𝗔◗b●𝗟◗q = (p●𝗔◗b)●𝗟◗q.
// qed-.

lemma path_append_pAbLq_6 (p) (b) (q):
      (p●𝗔◗b)●𝗟◗q = p●𝗔◗b●𝗟◗q.
// qed-.

lemma path_append_pAbLq_7 (p) (b) (q:ℙ):
      p●(𝗔◗b●𝗟◗q) = (p●𝗔◗b)●𝗟◗q.
// qed.

lemma path_append_pAbLq_8 (p1) (p2) (b) (q):
      (p1●p2)●𝗔◗b●𝗟◗q = p1●(p2◖𝗔)●b●𝗟◗q.
// qed.

lemma path_append_pAbLq_9 (p1) (p2) (b) (q:ℙ) (l):
      (p1●p2●𝗔◗b●𝗟◗q)◖l = p1●(p2●(𝗔◗b●𝗟◗q◖l)).
// qed.

lemma path_append_pAbLq_10 (p) (b1) (b2) (q1) (q):
      p●𝗔◗b1●𝗟◗q1●𝗔◗b2●𝗟◗q =
      (p●𝗔◗b1●𝗟◗q1)●𝗔◗b2●𝗟◗q.
// qed.

lemma path_append_pAbLq_11 (p) (b) (q) (q2) (l):
      (((p◖𝗔)●b◖𝗟)●q)●l◗q2 =
      p●𝗔◗b●𝗟◗q●l◗q2.
// qed.

lemma path_append_pAbLqAbLq_1 (p) (b1) (b2) (q1) (q) (q2) (l):
      p●𝗔◗b1●𝗟◗(q1●𝗔◗b2●𝗟◗q●l◗q2) =
      (p●𝗔◗b1●𝗟◗q1●𝗔◗b2●𝗟◗q◖l)●q2.
// qed.

lemma path_append_pAbLqAbLq_2 (p) (b1) (b2) (q1) (q) (q2) (l1) (l2):
      (p●𝗔◗b1●𝗟◗q1●𝗔◗b2●𝗟◗q)●(l1◗q2◖l2) =
      (p●𝗔◗b1●𝗟◗q1●𝗔◗b2●𝗟◗q●l1◗q2)◖l2.
// qed.
