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

include "basic_2/grammar/lenv_length.ma".
include "basic_2/relocation/lexs.ma".

(* GENERAL ENTRYWISE EXTENSION OF A CONTEXT-SENSITIVE REALTION FOR TERMS ****)

(* Forward lemmas on length for local environments **************************)

(* Basic_2A1: includes: lpx_sn_fwd_length *)
lemma lexs_fwd_length: ∀RN,RP,L1,L2,f. L1 ⦻*[RN, RP, f] L2 → |L1| = |L2|.
#RM #RP #L1 #L2 #f #H elim H -L1 -L2 -f //
qed-.
