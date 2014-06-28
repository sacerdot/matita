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

include "ground_2/ynat/ynat_plus.ma".
include "basic_2/grammar/leq.ma".

(* EQUIVALENCE FOR LOCAL ENVIRONMENTS ***************************************)

(* Main properties **********************************************************)

theorem leq_trans: ∀d,e. Transitive … (leq d e).
#d #e #L1 #L2 #H elim H -L1 -L2 -d -e
[ #d #e #X #H lapply (leq_inv_atom1 … H) -H
  #H destruct //
| #I1 #I #L1 #L #V1 #V #_ #IHL1 #X #H elim (leq_inv_zero1 … H) -H
  #I2 #L2 #V2 #HL2 #H destruct /3 width=1 by leq_zero/
| #I #L1 #L #V #e #_ #IHL1 #X #H elim (leq_inv_pair1 … H) -H //
  #L2 #HL2 #H destruct /3 width=1 by leq_pair/
| #I1 #I #L1 #L #V1 #V #d #e #_ #IHL1 #X #H elim (leq_inv_succ1 … H) -H //
  #I2 #L2 #V2 #HL2 #H destruct /3 width=1 by leq_succ/
]
qed-.

theorem leq_canc_sn: ∀d,e,L,L1,L2. L ⩬[d, e] L1 → L ⩬[d, e] L2 → L1 ⩬[d, e] L2.
/3 width=3 by leq_trans, leq_sym/ qed-.

theorem leq_canc_dx: ∀d,e,L,L1,L2. L1 ⩬[d, e] L → L2 ⩬[d, e] L → L1 ⩬[d, e] L2.
/3 width=3 by leq_trans, leq_sym/ qed-.

theorem leq_join: ∀L1,L2,d,i. L1 ⩬[d, i] L2 →
                  ∀e. L1 ⩬[i+d, e] L2 → L1 ⩬[d, i+e] L2.
#L1 #L2 #d #i #H elim H -L1 -L2 -d -i //
[ #I #L1 #L2 #V #e #_ #IHL12 #e #H
  lapply (leq_inv_succ … H ?) -H // >ypred_succ /3 width=1 by leq_pair/
| #I1 #I2 #L1 #L2 #V1 #V2 #d #e #_ #IHL12 #e #H
  lapply (leq_inv_succ … H ?) -H // >yplus_succ2 >ypred_succ /3 width=1 by leq_succ/
]
qed-.
