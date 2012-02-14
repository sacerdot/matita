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

include "Basic_2/reducibility/cpr_cpr.ma".
include "Basic_2/computation/csn.ma".

(* CONTEXT-SENSITIVE STRONGLY NORMALIZING TERMS *****************************)

(* Advanced forvard lemmas **************************************************)

fact csn_fwd_pair_sn_aux: ∀L,U. L ⊢ ⬇* U → ∀I,V,T. U = ②{I} V. T → L ⊢ ⬇* V.
#L #U #H elim H -H #U0 #_ #IH #I #V #T #H destruct
@csn_intro #V2 #HLV2 #HV2
@(IH (②{I} V2. T)) -IH // /2 width=1/ -HLV2 #H destruct /2 width=1/
qed.

(* Basic_1: was: sn3_gen_head *)
lemma csn_fwd_pair_sn: ∀I,L,V,T. L ⊢ ⬇* ②{I} V. T → L ⊢ ⬇* V.
/2 width=5/ qed.

fact csn_fwd_bind_dx_aux: ∀L,U. L ⊢ ⬇* U →
                          ∀I,V,T. U = ⓑ{I} V. T → L. ⓑ{I} V ⊢ ⬇* T.
#L #U #H elim H -H #U0 #_ #IH #I #V #T #H destruct
@csn_intro #T2 #HLT2 #HT2
@(IH (ⓑ{I} V. T2)) -IH // /2 width=1/ -HLT2 #H destruct /2 width=1/
qed.

(* Basic_1: was: sn3_gen_bind *)
lemma csn_fwd_bind_dx: ∀I,L,V,T. L ⊢ ⬇* ⓑ{I} V. T → L. ⓑ{I} V ⊢ ⬇* T.
/2 width=3/ qed.
