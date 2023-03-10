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

include "ground/ynat/ynat_plus.ma".
include "basic_2A/grammar/lreq.ma".

(* EQUIVALENCE FOR LOCAL ENVIRONMENTS ***************************************)

(* Main properties **********************************************************)

theorem lreq_trans: ∀l,m. Transitive … (lreq l m).
#l #m #L1 #L2 #H elim H -L1 -L2 -l -m
[ #l #m #X #H lapply (lreq_inv_atom1 … H) -H
  #H destruct //
| #I1 #I #L1 #L #V1 #V #_ #IHL1 #X #H elim (lreq_inv_zero1 … H) -H
  #I2 #L2 #V2 #HL2 #H destruct /3 width=1 by lreq_zero/
| #I #L1 #L #V #m #_ #IHL1 #X #H elim (lreq_inv_pair1 … H) -H //
  #L2 #HL2 #H destruct /3 width=1 by lreq_pair/
| #I1 #I #L1 #L #V1 #V #l #m #_ #IHL1 #X #H elim (lreq_inv_succ1 … H) -H //
  #I2 #L2 #V2 #HL2 #H destruct /3 width=1 by lreq_succ/
]
qed-.

theorem lreq_canc_sn: ∀l,m,L,L1,L2. L ⩬[l, m] L1 → L ⩬[l, m] L2 → L1 ⩬[l, m] L2.
/3 width=3 by lreq_trans, lreq_sym/ qed-.

theorem lreq_canc_dx: ∀l,m,L,L1,L2. L1 ⩬[l, m] L → L2 ⩬[l, m] L → L1 ⩬[l, m] L2.
/3 width=3 by lreq_trans, lreq_sym/ qed-.

theorem lreq_join: ∀L1,L2,l,i. L1 ⩬[l, i] L2 →
                   ∀m. L1 ⩬[i+l, m] L2 → L1 ⩬[l, i+m] L2.
#L1 #L2 #l #i #H elim H -L1 -L2 -l -i //
[ #I #L1 #L2 #V #m #_ #IHL12 #m #H
  lapply (lreq_inv_succ … H ?) -H // >ypred_succ /3 width=1 by lreq_pair/
| #I1 #I2 #L1 #L2 #V1 #V2 #l #m #_ #IHL12 #m #H
  lapply (lreq_inv_succ … H ?) -H // >yplus_succ2 >ypred_succ /3 width=1 by lreq_succ/
]
qed-.
