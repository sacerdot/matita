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

include "ground/relocation/pr_nat.ma".
include "ground/relocation/pr_isi_pat.ma".

(* IDENTITY CONDITION FOR PARTIAL RELOCATION MAPS ***************************)

(* Advanced constructions with pr_isi and pr_nat ****************************)

lemma pr_isi_nat (f): (∀l. ＠§❨l,f❩ ≘ l) → 𝐈❨f❩.
/2 width=1 by pr_isi_pat/ qed.

(* Inversions with pr_nat ***************************************************)

lemma pr_isi_inv_nat (f) (l): 𝐈❨f❩ → ＠§❨l,f❩ ≘ l.
/2 width=1 by pr_isi_inv_pat/ qed-.

(* Destructions with pr_nat *************************************************)

lemma pr_isi_nat_des (f) (l1) (l2): 𝐈❨f❩ → ＠§❨l1,f❩ ≘ l2 → l1 = l2.
/3 width=3 by pr_isi_pat_des, eq_inv_npsucc_bi/ qed-.
