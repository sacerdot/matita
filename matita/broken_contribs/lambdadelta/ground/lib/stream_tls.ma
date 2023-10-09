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

include "ground/notation/functions/downharpoonrightstar_3.ma".
include "ground/arith/nat_succ_iter.ma".
include "ground/lib/stream_hdtl.ma".

(* ITERATED TAIL FOR STREAMS ************************************************)

definition stream_tls (A) (n): stream A → stream A ≝
           (stream_tl A)^n.

interpretation
  "iterated tail (strams)"
  'DownHarpoonRightStar A n f = (stream_tls A n f).

(* Basic constructions ******************************************************)

lemma stream_tls_zero (A) (t):
      t = ⇂*{A}[𝟎]t.
// qed.

lemma stream_tls_tl (A) (n) (t):
      (⇂⇂*[n]t) = ⇂*{A}[n]⇂t.
#A #n #t
@(niter_appl … (stream_tl …))
qed.

lemma stream_tls_succ (A) (n) (t):
      (⇂⇂*[n]t) = ⇂*{A}[⁤↑n]t.
#A #n #t
@(niter_succ … (stream_tl …))
qed.

lemma stream_tls_swap (A) (n) (t):
      (⇂*[n]⇂t) = ⇂*{A}[⁤↑n]t.
// qed.

(* Advanced constructions ***************************************************)

lemma stream_tls_unit (A) (t):
      ⇂t = ⇂*{A}[⁤𝟏]t.
// qed.

lemma stream_tls_succ_lcons (A) (n) (a) (t):
      ⇂*[n]t = ⇂*{A}[⁤↑n](a⨮t).
// qed.
