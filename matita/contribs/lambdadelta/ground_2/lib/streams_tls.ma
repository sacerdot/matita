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

include "ground_2/notation/functions/drops_2.ma".
include "ground_2/lib/streams_hdtl.ma".

(* STREAMS ******************************************************************)

let rec tls (A:Type[0]) (n:nat) on n: stream A → stream A ≝ ?.
cases n -n [ #t @t | #n #t @tl @(tls … n t) ]
qed.

interpretation "recursive tail (strams)" 'Drops n f = (tls ? n f).

(* basic properties *********************************************************)

lemma tls_rew_O (A) (t): t = tls A 0 t.
// qed.

lemma tls_rew_S (A) (n) (t): ↓↓*[n]t = tls A (⫯n) t.
// qed.

lemma tls_S1 (A) (n) (t): ↓*[n]↓t = tls A (⫯n) t.
#A #n elim n -n //
qed.

lemma tls_eq_repl (A) (n): eq_stream_repl A (λt1,t2. ↓*[n] t1 ≐ ↓*[n] t2).
#A #n elim n -n //
#n #IH * #n1 #t1 * #n2 #t2 #H elim (eq_stream_inv_seq … H) /2 width=7 by/
qed.
