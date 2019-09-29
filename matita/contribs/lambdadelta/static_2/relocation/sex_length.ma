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
include "static_2/relocation/sex.ma".

(* GENERIC ENTRYWISE EXTENSION OF CONTEXT-SENSITIVE REALTIONS FOR TERMS *****)

(* Forward lemmas with length for local environments ************************)

(* Note: "#f #I1 #I2 #L1 #L2 >length_bind >length_bind //" was needed to conclude *)
lemma sex_fwd_length: ∀RN,RP,f,L1,L2. L1 ⪤[RN,RP,f] L2 → |L1| = |L2|.
#RN #RP #f #L1 #L2 #H elim H -f -L1 -L2 //
qed-.

(* Properties with length for local environments ****************************)

lemma sex_length_cfull: ∀L1,L2. |L1| = |L2| → ∀f. L1 ⪤[cfull,cfull,f] L2.
#L1 elim L1 -L1
[ #Y2 #H >(length_inv_zero_sn … H) -Y2 //
| #L1 #I1 #IH #Y2 #H #f
  elim (length_inv_succ_sn … H) -H #I2 #L2 #HL12 #H destruct
  elim (pn_split f) * #g #H destruct /3 width=1 by sex_next, sex_push/
]
qed.

lemma sex_length_isid: ∀R,L1,L2. |L1| = |L2| →
                       ∀f. 𝐈⦃f⦄ → L1 ⪤[R,cfull,f] L2.
#R #L1 elim L1 -L1
[ #Y2 #H >(length_inv_zero_sn … H) -Y2 //
| #L1 #I1 #IH #Y2 #H #f #Hf
  elim (length_inv_succ_sn … H) -H #I2 #L2 #HL12 #H destruct
  elim (isid_inv_gen … Hf) -Hf #g #Hg #H destruct /3 width=1 by sex_push/
]
qed.
