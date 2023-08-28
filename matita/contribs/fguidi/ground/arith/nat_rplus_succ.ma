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

include "ground/arith/nat_succ_iter.ma".
include "ground/arith/nat_rplus.ma".

(* RIGHT ADDITION FOR NON-NEGATIVE INTEGERS *********************************)

(* Constructions with nsucc *************************************************)

lemma nrplus_succ_dx (p) (n): ↑(p+n) = p + (⁤↑n).
#p #n @(niter_succ … psucc)
qed.

lemma nrplus_succ_shift (p) (n): ↑p + n = p + (⁤↑n).
// qed.

lemma nrplus_unit_sn (n): ↑n = 𝟏 + n.
#n @(nat_ind_succ … n) -n //
qed.

(* Advanced constructions ***************************************************)

lemma nrplus_comm_23 (p) (n1) (n2):
      p + n1 + n2 = p + n2 + n1.
#p #n1 @(nat_ind_succ … n1) -n1 //
qed.

(* Advanced inversions ******************************************************)

lemma eq_inv_refl_nrplus_dx (n) (p): p = p + n → 𝟎 = n.
#n #p elim p -p
/3 width=1 by eq_inv_psucc_bi/
qed-.
