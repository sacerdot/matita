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

include "ground/notation/functions/droppreds_2.ma".
include "ground/lib/stream_tls.ma".
include "ground/relocation/gr_tl.ma".

(* ITERATED TAIL FOR GENERIC RELOCATION MAPS ***********************************************************)

(*** tls *)
definition gr_tls (n) (f:gr_map) ≝ ⫰*[n]f.

interpretation
  "iterated tail (generic relocation maps)"
  'DropPreds n f = (gr_tls n f).

(* Basic properties (specific) *********************************************************)

(*** tls_O *)
lemma gr_tls_zero (f): f = ⫱*[𝟎] f.
// qed.

(*** tls_swap *)
lemma gr_tls_tl (n) (f): ⫱⫱*[n] f = ⫱*[n] ⫱f.
/2 width=1 by stream_tls_tl/ qed.

(*** tls_S *)
lemma gr_tls_succ (n) (f): ⫱⫱*[n] f = ⫱*[↑n] f.
/2 width=1 by stream_tls_succ/ qed.

(*** tls_xn *)
lemma gr_tls_swap (n) (f): ⫱*[n] ⫱f = ⫱*[↑n] f.
// qed.
