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

include "ground/relocation/pr_pat_pat.ma".
include "ground/relocation/tr_pat.ma".
include "ground/relocation/tr_pap.ma".

(* POSITIVE APPLICATION FOR TOTAL RELOCATION MAPS ***************************)

(* Constructions with pr_pat ***********************************************)

(*** at_total *)
lemma tr_pat_total: ∀i1,f. @❨i1,𝐭❨f❩❩ ≘ f@❨i1❩.
#i1 elim i1 -i1
[ * // | #i #IH * /3 width=1 by tr_pat_succ_sn/ ]
qed.

(* Inversions with pr_pat ***************************************************)

(*** at_inv_total *)
lemma tr_pat_inv_total (f):
      ∀i1,i2. @❨i1, 𝐭❨f❩❩ ≘ i2 → f@❨i1❩ = i2.
/2 width=6 by pr_pat_mono/ qed-.
