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

include "delayed_updating/reduction/ifr.ma".
include "delayed_updating/reduction/dfr.ma".

(* DELAYED FOCUSED REDUCTION ************************************************)

lemma dfr_lift_bi (f) (p) (q) (t1) (t2):
      t1 ➡𝐝𝐟[p,q] t2 → ↑[f]t1 ➡𝐟[⊗p,⊗q] ↑[f]t2.
#f #p #q #t1 #t2
* #b #n #Hr #Hb
