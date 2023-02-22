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

include "ground/relocation/pr_tl.ma".
include "ground/relocation/pr_isi.ma".

(* IDENTITY CONDITION FOR PARTIAL RELOCATION MAPS ***************************)

(* Constructions with pr_tl *************************************************)

(*** isid_tl *)
lemma pr_isi_tl (f): 𝐈❨f❩ → 𝐈❨⫰f❩.
#f cases (pr_map_split_tl f) * #H
[ /2 width=3 by pr_isi_inv_push/
| elim (pr_isi_inv_next … H) -H //
]
qed.
