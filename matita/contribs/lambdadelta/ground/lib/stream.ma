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

lemma stream_rew (A) (t:stream A): match t with [ stream_cons a u ⇒ a ⨮ u ] = t.
#A * //
qed.
