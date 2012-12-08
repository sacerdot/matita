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

include "pointer_order.ma".

(* POINTER SEQUENCE *********************************************************)

(* Policy: pointer sequence metavariables: r, s *)
definition pseq: Type[0] ≝ list ptr.

(* Note: a "head" computation contracts just redexes in the head *)
definition is_head: predicate pseq ≝ All … in_head.

(* Note: to us, a "normal" computation contracts redexes in non-decreasing positions *)
definition is_le: predicate pseq ≝ Allr … ple.

theorem is_head_is_le: ∀s. is_head s → is_le s.
#s elim s -s //
#p #s elim s -s //
#q #s #_ #IHs * #Hp * /4 width=1/
qed.
