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

(* Basic_2A1: uses: lpx_sn_fwd_length *)
lemma lexs_fwd_length: ∀RN,RP,f,L1,L2. L1 ⪤*[RN, RP, f] L2 → |L1| = |L2|.
#RM #RP #f #L1 #L2 #H elim H -f -L1 -L2 //
#f #I1 #I2 #L1 #L2 >length_bind >length_bind //
qed-.

(* Properties with length for local environments ****************************)

lemma lexs_length_cfull: ∀L1,L2. |L1| = |L2| → ∀f. L1 ⪤*[cfull, cfull, f] L2.
#L1 elim L1 -L1
[ #Y2 #H >(length_inv_zero_sn … H) -Y2 //
| #L1 #I1 #IH #Y2 #H #f
  elim (length_inv_succ_sn … H) -H #I2 #L2 #HL12 #H destruct
  elim (pn_split f) * #g #H destruct /3 width=1 by lexs_next, lexs_push/
]
qed.
