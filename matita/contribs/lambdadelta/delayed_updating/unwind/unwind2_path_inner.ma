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

include "delayed_updating/unwind/unwind2_path_structure.ma".
include "delayed_updating/syntax/path_inner.ma".

(* UNWIND FOR PATH **********************************************************)

(* Destructions with inner condition for path *******************************)

lemma unwind2_path_des_inner (f) (p):
      ▼[f]p ϵ 𝐈 → p ϵ 𝐈.
#f #p @(list_ind_rcons … p) -p //
#p * [ #n ] #_ //
<unwind2_path_d_dx #H0
elim (pic_inv_d_dx … H0)
qed-.
