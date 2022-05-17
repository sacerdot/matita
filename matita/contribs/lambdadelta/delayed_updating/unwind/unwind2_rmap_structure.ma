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

include "delayed_updating/unwind/unwind2_rmap.ma".
include "delayed_updating/syntax/path_structure.ma".
include "delayed_updating/syntax/path_depth.ma".
include "ground/relocation/tr_pushs.ma".

(* UNWIND MAP FOR PATH ******************************************************)

(* Constructions with structure and depth ***********************************)

lemma unwind2_rmap_structure (p) (f):
      (⫯*[♭p]f) = ▶[f]⊗p.
#p elim p -p //
* [ #n ] #p #IH #f //
[ <unwind2_rmap_A_sn //
| <unwind2_rmap_S_sn //
]
qed.
