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

include "ground/notation/functions/downspoonstar_3.ma".
include "ground/lib/stream_hdtl.ma".

(* STREAMS ******************************************************************)

rec definition tls (A:Type[0]) (n:nat) on n: stream A → stream A ≝ ?.
cases n -n [ #t @t | #n #t @tl @(tls … n t) ]
defined.

interpretation "iterated tail (stram)" 'DownSpoonStar A n f = (tls A n f).

(* basic properties *********************************************************)

lemma tls_rew_O (A) (t): t = tls A 0 t.
// qed.

lemma tls_rew_S (A) (n) (t): ⫰⫰*[n]t = tls A (↑n) t.
// qed.

lemma tls_S1 (A) (n) (t): ⫰*[n]⫰t = tls A (↑n) t.
#A #n elim n -n //
qed.

lemma tls_eq_repl (A) (n): eq_stream_repl A (λt1,t2. ⫰*[n] t1 ≗ ⫰*[n] t2).
#A #n elim n -n //
#n #IH * #n1 #t1 * #n2 #t2 #H elim (eq_stream_inv_seq … H) /2 width=7 by/
qed.
