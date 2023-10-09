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

include "ground/relocation/fb/fbr_rconss.ma".
include "ground/relocation/fb/fbr_eq.ma".

(* ITERATED RCONS FOR FINITE RELOCATION MAPS WITH BOOLEANS ******************)

(* Constructions with fbr_eq ************************************************)

lemma fbr_rconss_eq_repl (b) (n):
      compatible_2_fwd … fbr_eq fbr_eq (λf.f◖*[n]b).
#b #n @(nat_ind_succ … n) -n
/3 width=1 by fbr_eq_rcons_bi/
qed.

lemma fbr_pushs_id (n):
      (𝐢) ≐ ⫯*[n]𝐢.
#n @(nat_ind_succ … n) -n
/2 width=1 by fbr_eq_id_push/
qed.
