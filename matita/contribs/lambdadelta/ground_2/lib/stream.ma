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

include "ground_2/notation/functions/oplusright_3.ma".
include "ground_2/lib/relations.ma".

(* STREAMS ******************************************************************)

coinductive stream (A:Type[0]): Type[0] ≝
| seq: A → stream A → stream A
.

interpretation "cons (stream)" 'OPlusRight A a u = (seq A a u).

(* Basic properties *********************************************************)

lemma stream_rew (A) (t:stream A): match t with [ seq a u ⇒ a ⨮ u ] = t.
#A * //
qed.
