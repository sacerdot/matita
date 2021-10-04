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

include "ground/notation/functions/downspoonstar_2.ma".
include "ground/lib/stream_tls.ma".
include "ground/relocation/pr_tl.ma".

(* ITERATED TAIL FOR PARTIAL RELOCATION MAPS ********************************)

(*** tls *)
definition pr_tls (n) (f:pr_map) ≝ ⇂*[n]f.

interpretation
  "iterated tail (partial relocation maps)"
  'DownSpoonStar n f = (pr_tls n f).

(* Basic constructions (specific) *******************************************)

(*** tls_O *)
lemma pr_tls_zero (f): f = ⫰*[𝟎] f.
// qed.

(*** tls_swap *)
lemma pr_tls_tl (n) (f): ⫰⫰*[n] f = ⫰*[n] ⫰f.
/2 width=1 by stream_tls_tl/ qed.

(*** tls_S *)
lemma pr_tls_succ (n) (f): ⫰⫰*[n] f = ⫰*[↑n] f.
/2 width=1 by stream_tls_succ/ qed.

(*** tls_xn *)
lemma pr_tls_swap (n) (f): ⫰*[n] ⫰f = ⫰*[↑n] f.
// qed.
