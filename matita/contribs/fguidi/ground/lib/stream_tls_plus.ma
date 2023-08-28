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

include "ground/arith/nat_plus.ma".
include "ground/lib/stream_tls.ma".

(* ITERATED TAIL FOR STREAMS ************************************************)

(* Constructions with nplus *************************************************)

lemma stream_tls_plus (A) (n1) (n2) (t):
      ⇂*[n1]⇂*[n2]t = ⇂*{A}[n1+n2]t.
#A #n1 #n2 #t
<nplus_comm @(niter_plus … t)
qed.
