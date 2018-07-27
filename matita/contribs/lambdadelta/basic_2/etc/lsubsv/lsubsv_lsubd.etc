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

include "static_2/static/lsubd.ma".
include "basic_2/dynamic/lsubsv.ma".

(* LOCAL ENVIRONMENT REFINEMENT FOR STRATIFIED NATIVE VALIDITY **************)

(* Forward lemmas on lenv refinement for degree assignment ******************)

lemma lsubsv_fwd_lsubd: ∀h,o,G,L1,L2. G ⊢ L1 ⫃¡[h, o] L2 → G ⊢ L1 ⫃▪[h, o] L2.
#h #o #G #L1 #L2 #H elim H -L1 -L2 /2 width=3 by lsubd_pair, lsubd_beta/
qed-.
