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

include "ground/relocation/gr_tl_eq.ma".
include "ground/relocation/gr_id.ma".

(* IDENTITY ELEMENT FOR GENERIC RELOCATION MAPS *****************************)

(* Constructions with gr_eq *************************************************)

corec lemma gr_id_eq (f): ⫯f ≡ f → 𝐢 ≡ f.
cases gr_id_unfold #Hf
cases (gr_eq_inv_push_sn … Hf) [|*: // ] #_ #H
cases H in Hf; -H #Hf
@gr_eq_push [3:|*: // ]
/3 width=5 by gr_eq_inv_push_bi/
qed.

(* Inversions with gr_eq ****************************************************)

(* Note: this has the same proof of the previous *)
corec lemma gr_id_inv_eq (f): 𝐢 ≡ f → ⫯f ≡ f.
cases gr_id_unfold #Hf
cases (gr_eq_inv_push_sn … Hf) [|*: // ] #_ #H
cases H in Hf; -H #Hf
@gr_eq_push [3:|*: // ]
/3 width=5 by gr_eq_inv_push_bi/
qed-.
