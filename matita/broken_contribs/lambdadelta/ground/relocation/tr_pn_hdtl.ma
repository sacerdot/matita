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
include "ground/relocation/tr_pn.ma".

(* PUSH AND NEXT FOR TOTAL RELOCATION MAPS **********************************)

(* Constructions with stream_tl *********************************************)

(*** tl_push *)
lemma tr_tl_push (f):
      f = ⇂⫯f.
// qed.

(*** tl_next *)
lemma tr_tl_next (f):
      ⇂f = ⇂↑f.
* // qed.
