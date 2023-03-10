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

include "static_2/static/rex_length.ma".
include "static_2/i_static/rexs.ma".

(* ITERATED EXTENSION ON REFERRED ENTRIES OF A CONTEXT-SENSITIVE REALTION ***)

(* Forward lemmas with length for local environments ************************)

(* Basic_2A1: uses: TC_lpx_sn_fwd_length *)
lemma rexs_fwd_length: ∀R,L1,L2,T. L1 ⪤*[R,T] L2 → |L1| = |L2|.
#R #L1 #L2 #T #H elim H -L2
[ #L2 #HL12 >(rex_fwd_length … HL12) -HL12 //
| #L #L2 #_ #HL2 #IHL1
  >IHL1 -L1 >(rex_fwd_length … HL2) -HL2 //
]
qed-.
