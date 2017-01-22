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

include "basic_2/syntax/lenv_length.ma".
include "basic_2/relocation/lexs.ma".

(* GENERIC ENTRYWISE EXTENSION OF CONTEXT-SENSITIVE REALTIONS FOR TERMS *****)

(* Forward lemmas with length for local environments ************************)

(* Basic_2A1: includes: lpx_sn_fwd_length *)
lemma lexs_fwd_length: ∀RN,RP,f,L1,L2. L1 ⦻*[RN, RP, f] L2 → |L1| = |L2|.
#RM #RP #f #L1 #L2 #H elim H -f -L1 -L2 //
#f #I #L1 #L2 #V1 #V2 >length_pair >length_pair //
qed-.
