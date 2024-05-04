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

include "static_2/notation/relations/approxeqsn_6.ma".
include "static_2/static/reqx.ma".
include "static_2/static/feqg.ma".

(* SORT-IRRELEVANT EQUIVALENCE FOR CLOSURES ON REFERRED ENTRIES *************)

interpretation
  "sort-irrelevant equivalence on referred entries (closure)"
  'ApproxEqSn G1 L1 T1 G2 L2 T2 = (feqg sfull G1 L1 T1 G2 L2 T2).

(* Basic_properties *********************************************************)

lemma feqg_feqx (S) (G1) (G2) (L1) (L2) (T1) (T2):
      ❨G1,L1,T1❩ ≛[S] ❨G2,L2,T2❩ → ❨G1,L1,T1❩ ≅ ❨G2,L2,T2❩.
#S #G1 #G2 #L1 #L2 #T1 #T2 #H
elim (feqg_inv_gen_sn … H) -H
/3 width=2 by feqg_intro_sn, reqg_reqx, teqg_teqx/
qed.
