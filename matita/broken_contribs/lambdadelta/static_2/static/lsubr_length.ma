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

include "static_2/syntax/lenv_length.ma".
include "static_2/static/lsubr.ma".

(* RESTRICTED REFINEMENT FOR LOCAL ENVIRONMENTS *****************************)

(* Forward lemmas with length for local environments ************************)

lemma lsubr_fwd_length: ∀L1,L2. L1 ⫃ L2 → |L2| = |L1|.
#L1 #L2 #H elim H -L1 -L2 normalize //
qed-.
