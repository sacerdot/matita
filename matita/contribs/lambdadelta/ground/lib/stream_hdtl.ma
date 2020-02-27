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
include "ground/lib/arith.ma".

(* STREAMS ******************************************************************)

definition hd (A:Type[0]): stream A → A ≝
              λt. match t with [ seq a _ ⇒ a ].

definition tl (A:Type[0]): stream A → stream A ≝
              λt. match t with [ seq _ t ⇒ t ].

interpretation "tail (stream)" 'DownSpoon A t = (tl A t).

(* basic properties *********************************************************)

lemma hd_rew (A) (a) (t): a = hd A (a⨮t).
// qed.

lemma tl_rew (A) (a) (t): t = tl A (a⨮t).
// qed.

lemma eq_stream_split (A) (t): (hd … t) ⨮ ⫰t ≗{A} t.
#A * //
qed.
