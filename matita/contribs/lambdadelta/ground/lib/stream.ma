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

include "ground/notation/functions/oplusright_3.ma".
include "ground/lib/relations.ma".

(* STREAMS ******************************************************************)

coinductive stream (A:Type[0]): Type[0] ≝
| stream_cons: A → stream A → stream A
.

interpretation
  "cons (streams)"
  'OPlusRight A a u = (stream_cons A a u).

(* Basic constructions ******************************************************)

(*** stream_rew *)
lemma stream_unfold (A) (t:stream A):
      match t with [ stream_cons a u ⇒ a ⨮ u ] = t.
#A * //
qed.

(* Basic inversions *********************************************************)

lemma eq_inv_stream_cons_bi (A) (a1,a2:A) (u1) (u2):
      a1 ⨮ u1 = a2 ⨮ u2 → ∧∧ a1 = a2 & u1 = u2.
#A #a1 #a2 #u1 #u2 #H destruct
/2 width=1 by conj/
qed-.
