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

include "basic_2/relocation/lifts_lifts.ma".
include "basic_2/relocation/lifts_bind.ma".

(* GENERIC RELOCATION FOR BINDERS *******************************************)

(* Main properties **********************************************************)

theorem liftsb_div3: ∀f2,I,I2. ⬆*[f2] I2 ≡ I → ∀f,I1. ⬆*[f] I1 ≡ I →
                     ∀f1. f2 ⊚ f1 ≡ f → ⬆*[f1] I1 ≡ I2.
#f2 #I #I2 * -I -I2 #I [2: #V #V2 #HV2 ] #f #I1 #H
[ elim (liftsb_inv_pair_dx … H) | lapply (liftsb_inv_unit_dx … H) ] -H
/3 width=6 by lifts_div3, ext2_pair, ext2_unit/
qed-.

theorem liftsb_trans: ∀f1,I1,I. ⬆*[f1] I1 ≡ I → ∀f2,I2. ⬆*[f2] I ≡ I2 →
                      ∀f. f2 ⊚ f1 ≡ f → ⬆*[f] I1 ≡ I2.
#f1 #I1 #I * -I1 -I #I1 [2: #V1 #V #HV1 ] #f2 #I2 #H
[ elim (liftsb_inv_pair_sn … H) | lapply (liftsb_inv_unit_sn … H) ] -H
/3 width=6 by lifts_trans, ext2_pair, ext2_unit/
qed-.
