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

include "ground/lib/stream_hdtl.ma".
include "ground/lib/stream_eq.ma".

(* HEAD AND TAIL FOR STREAMS ************************************************)

(* Constructions with stream_eq *********************************************)

lemma stream_hd_eq_repl (A):
      stream_eq_repl A (λt1,t2. ⇃t1 = ⇃t2).
#A * #a1 #t1 * #a2 #t2 #H
elim (stream_eq_inv_cons_bi … H) -H
/2 width=7 by/
qed.

lemma stream_tl_eq_repl (A):
      stream_eq_repl A (λt1,t2. ⇂t1 ≗ ⇂t2).
#A * #a1 #t1 * #a2 #t2 #H
elim (stream_eq_inv_cons_bi … H) -H
/2 width=7 by/
qed.
