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

include "ground/relocation/pr_nat_basic.ma".

(* POSITIVE APPLICATION FOR PARTIAL RELOCATION MAPS *************************)

(* Constructions with pr_basic **********************************************)

(*** at_basic_lt *)
lemma pr_pat_basic_lt (m) (n) (i):
      npos i ≤ m → ＠⧣❨i, 𝐛❨m,n❩❩ ≘ i.
#m #n #i >(npsucc_pnpred i) #Hmi
/2 width=1 by pr_nat_basic_lt/
qed.

(*** at_basic_ge *)
lemma pr_pat_basic_ge (m) (n) (i):
      m < npos i → ＠⧣❨i, 𝐛❨m,n❩❩ ≘ i+n.
#m #n #i >(npsucc_pnpred i) #Hmi <nrplus_npsucc_sn
/3 width=1 by pr_nat_basic_ge, nlt_inv_succ_dx/
qed.

(* Inversions with pr_basic *************************************************)

(*** at_basic_inv_lt *)
lemma pr_pat_basic_inv_lt (m) (n) (i) (j):
      npos i ≤ m → ＠⧣❨i, 𝐛❨m,n❩❩ ≘ j → i = j.
/3 width=4 by pr_pat_basic_lt, pr_pat_mono/ qed-.

(*** at_basic_inv_ge *)
lemma pr_pat_basic_inv_ge (m) (n) (i) (j):
      m < npos i → ＠⧣❨i, 𝐛❨m,n❩❩ ≘ j → i+n = j.
/3 width=4 by pr_pat_basic_ge, pr_pat_mono/ qed-.
