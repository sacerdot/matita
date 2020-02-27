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

include "ground/lib/ltc_ctc.ma".
include "basic_2/rt_computation/cpms.ma".

(* CONTEXT-SENSITIVE PARALLEL R-COMPUTATION FOR TERMS ***********************)

(* Properties with contextual transitive closure ****************************)

lemma cprs_CTC (h) (G) (L): CTC … (λL. cpm h G L 0) L ⊆ cpms h G L 0.
/2 width=1 by ltc_CTC/ qed.

(* Inversion lemmas with contextual transitive closure **********************)

lemma cprs_inv_CTC (h) (G) (L): cpms h G L 0 ⊆ CTC … (λL. cpm h G L 0) L.
#h #G @ltc_inv_CTC //
(**) (* this shoould be just @plus_inv_O3 *)
#x1 #x2 #Hx12 elim (plus_inv_O3 x1 x2) /2 width=1 by conj/
qed-.
