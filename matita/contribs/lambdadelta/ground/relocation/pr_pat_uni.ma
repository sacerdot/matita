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

include "ground/arith/nat_rplus_succ.ma".
include "ground/relocation/pr_uni.ma".
include "ground/relocation/pr_pat_pat_id.ma".

(* POSITIVE APPLICATION FOR PARTIAL RELOCATION MAPS *************************)

(* Constructions with pr_uni ************************************************)

(*** at_uni *)
lemma pr_pat_uni (n) (i):
      @❨i,𝐮❨n❩❩ ≘ i+n.
#n @(nat_ind_succ … n) -n
/2 width=5 by pr_pat_next/
qed.

(* Inversions with pr_uni ***************************************************)

(*** at_inv_uni *)
lemma pr_pat_inv_uni (n) (i) (j):
      @❨i,𝐮❨n❩❩ ≘ j → j = i+n.
/2 width=4 by pr_pat_mono/ qed-.
