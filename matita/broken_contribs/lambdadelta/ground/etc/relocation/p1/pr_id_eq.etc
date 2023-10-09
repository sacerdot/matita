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

include "ground/relocation/p1/pr_tl_eq.ma".
include "ground/relocation/p1/pr_id.ma".

(* IDENTITY ELEMENT FOR PARTIAL RELOCATION MAPS *****************************)

(* Constructions with pr_eq *************************************************)

corec lemma pr_id_eq (f): ⫯f ≐ f → 𝐢 ≐ f.
cases pr_id_unfold #Hf
cases (pr_eq_inv_push_sn … Hf) [|*: // ] #_ #H
cases H in Hf; -H #Hf
@pr_eq_push [3:|*: // ]
/3 width=5 by pr_eq_inv_push_bi/
qed.

(* Inversions with pr_eq ****************************************************)

(* Note: this has the same proof of the previous *)
corec lemma pr_id_inv_eq (f): 𝐢 ≐ f → ⫯f ≐ f.
cases pr_id_unfold #Hf
cases (pr_eq_inv_push_sn … Hf) [|*: // ] #_ #H
cases H in Hf; -H #Hf
@pr_eq_push [3:|*: // ]
/3 width=5 by pr_eq_inv_push_bi/
qed-.
