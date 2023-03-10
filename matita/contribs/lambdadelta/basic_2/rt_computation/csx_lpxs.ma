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

include "basic_2/rt_computation/csx_lpx.ma".
include "basic_2/rt_computation/lpxs_lpx.ma".

(* STRONGLY NORMALIZING TERMS FOR EXTENDED PARALLEL RT-TRANSITION ***********)

(* Properties with extended parallel rt-computation on all entries **********)

lemma csx_lpxs_conf (G) (L1):
      ∀L2,T. ❨G,L1❩ ⊢ ⬈* L2 → ❨G,L1❩ ⊢ ⬈*𝐒 T → ❨G,L2❩ ⊢ ⬈*𝐒 T.
#G #L1 #L2 #T #H @(lpxs_ind_dx … H) -L2
/3 by lpxs_step_dx, csx_lpx_conf/
qed-.
