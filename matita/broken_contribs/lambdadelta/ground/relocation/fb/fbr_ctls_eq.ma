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

include "ground/relocation/fb/fbr_ctls.ma".
include "ground/relocation/fb/fbr_ctl_eq.ma".

(* ITERATED COARSE TAIL FOR FINITE RELOCATION MAPS WITH BOOLEANS ************)

(* Constructions with fbr_eq ************************************************)

lemma fbr_ctl_eq_repl (n):
      compatible_2_fwd … fbr_eq fbr_eq (λf.⫰*[n]f).
#n @(nat_ind_succ … n) -n //
#n #IH #f1 #f2 #Hf
/3 width=1 by fbr_ctl_eq_repl/
qed.
