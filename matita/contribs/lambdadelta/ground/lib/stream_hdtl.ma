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

include "ground/notation/functions/downharpoonleft_2.ma".
include "ground/notation/functions/downharpoonright_2.ma".
include "ground/lib/stream.ma".

(* HEAD AND TAIL FOR STREAMS ************************************************)

definition stream_hd (A:Type[0]): stream A → A.
#A * #a #_ @a
defined.

interpretation
  "head (streams)"
  'DownHarpoonLeft A t = (stream_hd A t).

definition stream_tl (A:Type[0]): stream A → stream A.
#A * #_ #t @t
defined.

interpretation
  "tail (streams)"
  'DownHarpoonRight A t = (stream_tl A t).

(* Basic constructions ******************************************************)

lemma stream_hd_lcons (A) (a) (t):
      a = ⇃{A}(a⨮t).
// qed.

lemma stream_tl_lcons (A) (a) (t):
      t = ⇂{A}(a⨮t).
// qed.

lemma stream_split_tl (A) (t):
      ⇃{A}t ⨮ ⇂t = t.
#A * //
qed.
