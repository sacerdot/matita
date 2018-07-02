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

include "static_2/syntax/bind_weight.ma".
include "static_2/relocation/lifts_weight.ma".
include "static_2/relocation/lifts_bind.ma".

(* GENERIC RELOCATION FOR BINDERS *******************************************)

(* Forward lemmas with weight for binders ***********************************)

lemma liftsb_fwd_bw: ∀f,I1,I2. ⬆*[f] I1 ≘ I2 → ♯{I1} = ♯{I2}.
#f #I1 #I2 * -I1 -I2 /2 width=2 by lifts_fwd_tw/
qed-.
