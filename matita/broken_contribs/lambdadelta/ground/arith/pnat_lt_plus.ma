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

include "ground/arith/pnat_le_plus.ma".
include "ground/arith/pnat_lt.ma".

(* STRICT ORDER FOR POSITIVE INTEGERS ***************************************)

(* Constructions with pplus *************************************************)

lemma plt_plus_bi_dx (p) (q1) (q2): q1 < q2 → q1 + p < q2 + p.
#p #q1 #q2 #H
@plt_i >pplus_succ_sn /2 width=1 by ple_plus_bi_dx/
qed.

lemma plt_plus_bi_sn (p) (q1) (q2): q1 < q2 → p + q1 < p + q2.
#p #q1 #q2 #H
@plt_i >pplus_succ_dx /2 width=1 by ple_plus_bi_sn/
qed.

lemma plt_plus_dx_dx_refl (p) (q): p < p + q.
/2 width=1 by ple_plus_bi_sn/ qed.

lemma plt_plus_dx_sn_refl (p) (q): p < q + p.
/2 width=1 by ple_plus_bi_dx/ qed.

lemma plt_plus_dx_sn (r) (p) (q): q ≤ p → q < r + p.
/2 width=3 by ple_plt_trans/ qed.

lemma plt_plus_dx_dx (r) (p) (q): q ≤ p → q < p + r.
/2 width=3 by ple_plt_trans/ qed.
