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

include "ground/relocation/gr_tls.ma".
include "ground/relocation/gr_sor.ma".

(* RELATIONAL UNION FOR GENERIC RELOCATION MAPS ***********************************************************)

(* Properties with iterated tail ********************************************)

(*** sor_tls *)
lemma gr_sor_tls:
      ∀f1,f2,f. f1 ⋓ f2 ≘ f →
      ∀n. ⫱*[n]f1 ⋓ ⫱*[n]f2 ≘ ⫱*[n]f.
#f1 #f2 #f #Hf #n @(nat_ind_succ … n) -n
/2 width=1 by gr_sor_tl/
qed.
