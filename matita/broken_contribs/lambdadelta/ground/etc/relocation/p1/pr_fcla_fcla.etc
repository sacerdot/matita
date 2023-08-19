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

include "ground/relocation/p1/pr_fcla.ma".

(* FINITE COLENGTH ASSIGNMENT FOR PARTIAL RELOCATION MAPS *******************)

(* Main destructions ********************************************************)

(*** fcla_mono *)
theorem pr_fcla_mono (f):
        ∀n1. 𝐂❨f❩ ≘ n1 → ∀n2. 𝐂❨f❩ ≘ n2 → n1 = n2.
#f #n #H elim H -f -n
[ /2 width=3 by pr_fcla_inv_isi/
| /3 width=3 by pr_fcla_inv_push/
| #f #n1 #_ #IH #n2 #H elim (pr_fcla_inv_next … H) -H [2,3 : // ]
  #g #Hf #H destruct >IH //
]
qed-.
