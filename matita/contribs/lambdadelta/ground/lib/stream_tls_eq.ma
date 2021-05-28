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

include "ground/lib/stream_eq.ma".
include "ground/lib/stream_tls.ma".

(* ITERATED TAIL FOR STREAMS ************************************************)

(* Properties with stream_eq *)

lemma stream_tls_eq_repl (A) (n):
      stream_eq_repl A (λt1,t2. ⫰*[n] t1 ≗ ⫰*[n] t2).
#A #n @(nat_ind_succ … n) -n //
#n #IH * #n1 #t1 * #n2 #t2 #H
elim (stream_eq_inv_cons_bi … H) /2 width=7 by/
qed.
