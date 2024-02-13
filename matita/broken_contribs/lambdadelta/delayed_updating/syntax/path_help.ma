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

lemma path_append_pLbLq (p) (b1) (b2) (q:ℙ):
      p●𝗟◗(b1●b2●𝗟◗q) = ((p●𝗟◗b1)●b2)●𝗟◗q.
// qed.

lemma path_append_append_lcons (p) (q) (r) (l):
      p●(r◖l)●q = p●r●(l◗q).
// qed-.

lemma path_append_lcons_append (p) (q) (r) (l):
      (p◖l)●r●q = p●(l◗r)●q.
// qed-.
