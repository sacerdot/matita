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

include "ground/arith/nat_plus_rplus.ma".
include "ground/relocation/gr_pat_uni.ma".
include "ground/relocation/gr_nat_nat.ma".

(* NON-NEGATIVE APPLICATION FOR GENERIC RELOCATION MAPS *********************)

(* Constructions with gr_uni ************************************************)

lemma gr_nat_uni (n) (l):
      @↑❪l,𝐮❨n❩❫ ≘ l+n.
/2 width=1 by gr_nat_pred_bi/
qed.

(* Inversions with gr_uni ***************************************************)

lemma gr_nat_inv_uni (n) (l) (k):
      @↑❪l,𝐮❨n❩❫ ≘ k → k = l+n.
/2 width=4 by gr_nat_mono/ qed-.
