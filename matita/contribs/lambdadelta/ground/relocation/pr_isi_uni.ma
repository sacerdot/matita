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

include "ground/relocation/pr_uni.ma".
include "ground/relocation/pr_isi_id.ma".

(* IDENTITY CONDITION FOR PARTIAL RELOCATION MAPS ***************************)

(* Constructions with pr_isi ************************************************)

(*** uni_inv_isid uni_isi *)
lemma pr_uni_isi (f): đŽâ¨đâŠ â f â đâ¨fâŠ.
/2 width=1 by pr_eq_id_isi/ qed.

(* Inversions with pr_isi ***************************************************)

(*** uni_isid isi_inv_uni *)
lemma pr_isi_inv_uni (f): đâ¨fâŠ â đŽâ¨đâŠ â f.
/2 width=1 by pr_isi_inv_eq_id/ qed-.
