(**************************************************************************)
(*       ___                                                              *)
(*      ||M||                                                             *)
(*      ||A||       A project by Andrea Asperti                           *)
(*      ||T||                                                             *)
(*      ||I||       Developers:                                           *)
(*      ||T||         The HELM team.                                      *)
(*      ||A||         http://helm.tcs.unibo.it                            *)
(*      \   /                                                             *)
(*       \ /        This file is distributed under the terms of the       *)
(*        v         GNU General Public License Version 2                  *)
(*                                                                        *)
(**************************************************************************)

include "ground/arith/nat_plus.ma".
include "ground/relocation/rtmap_uni.ma".
include "ground/relocation/rtmap_nat.ma".

(* NON-NEGATIVE APPLICATION FOR RELOCATION MAPS *****************************)

(* Properties with uniform relocations **************************************)

lemma rm_nat_uni (n) (l): @↑❪l,𝐔❨n❩❫ ≘ l+n.
#n @(nat_ind_succ … n) -n /2 width=5 by rm_nat_next/
qed.

(* Inversion lemmas with uniform relocations ********************************)

lemma rm_nat_inv_uni (n) (l) (k): @↑❪l,𝐔❨n❩❫ ≘ k → k = l+n.
/2 width=4 by rm_nat_mono/ qed-.
