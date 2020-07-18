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

include "static_2/relocation/sex_length.ma".
include "static_2/relocation/seq.ma".

(* SYNTACTIC EQUIVALENCE FOR SELECTED LOCAL ENVIRONMENTS ********************)

(* Forward lemmas with length for local environments ************************)

(* Basic_2A1: includes: lreq_fwd_length *)
lemma seq_fwd_length (f):
      ∀L1,L2. L1 ≡[f] L2 → |L1| = |L2|.
/2 width=4 by sex_fwd_length/ qed-.
