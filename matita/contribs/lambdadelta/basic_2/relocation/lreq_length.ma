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

include "basic_2/relocation/lexs_length.ma".
include "basic_2/relocation/lreq.ma".

(* RANGED EQUIVALENCE FOR LOCAL ENVIRONMENTS ********************************)

(* Forward lemmas on length for local environments **************************)

(* Basic_2A1: includes: lreq_fwd_length *)
lemma lreq_fwd_length: ∀L1,L2,f. L1 ≡[f] L2 → |L1| = |L2|.
/2 width=4 by lexs_fwd_length/ qed-.
