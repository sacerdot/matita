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

include "ground/notation/functions/exp_3.ma".
include "ground/arith/pnat.ma".

(* ITERATED FUNCTION FOR POSITIVE INTEGERS **********************************)

rec definition piter (p:pnat) (A:Type[0]) (f:A→A) (a:A) ≝
match p with
[ punit   ⇒ f a
| psucc q ⇒ f (piter q A f a)
].

interpretation
  "iterated function (positive integers)"
  'Exp A f p = (piter p A f).

(* Basic rewrites ***********************************************************)

lemma piter_unit (A) (f) (a): f a = (f^{A}𝟏) a.
// qed.

lemma piter_succ (A) (f) (p) (a): f (f^p a) = f^{A}(↑p) a.
// qed.

(* Advanced rewrites ********************************************************)

lemma piter_appl (A) (f) (p) (a): f (f^p a) = f^{A}p (f a).
#A #f #p elim p -p //
#p #IH #a <piter_succ <piter_succ //
qed.
