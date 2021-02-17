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

include "ground/notation/functions/downspoon_2.ma".
include "ground/lib/stream_eq.ma".

(* HEAD AND TAIL FOR STREAMS ************************************************)

definition stream_hd (A:Type[0]): stream A → A ≝
           λt. match t with [ stream_cons a _ ⇒ a ].

definition stream_tl (A:Type[0]): stream A → stream A ≝
           λt. match t with [ stream_cons _ t ⇒ t ].

interpretation
  "tail (streams)"
  'DownSpoon A t = (stream_tl A t).

(* Basic constructions ******************************************************)

lemma stream_hd_cons (A) (a) (t):
      a = stream_hd A (a⨮t).
// qed.

lemma stream_tl_cons (A) (a) (t):
      t = ⫰{A}(a⨮t).
// qed.

lemma eq_stream_split_hd_tl (A) (t):
      stream_hd … t ⨮ ⫰t ≗{A} t.
#A * //
qed.
