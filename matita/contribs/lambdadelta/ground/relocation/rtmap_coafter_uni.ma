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

include "ground/relocation/rtmap_uni.ma".
include "ground/relocation/rtmap_coafter.ma".

(* RELOCATION MAP ***********************************************************)

(* Properties with test for uniform relocations *****************************)

lemma coafter_isuni_isid: ∀f2. 𝐈❪f2❫ → ∀f1. 𝐔❪f1❫ → f1 ~⊚ f2 ≘ f2.
#f #Hf #g #H elim H -g
/3 width=5 by coafter_isid_sn, coafter_eq_repl_back0, coafter_next, eq_push_inv_isid/
qed.

(* Properties with uniform relocations **************************************)

lemma coafter_uni_sn: ∀n,f. 𝐔❨n❩ ~⊚ f ≘ ⫯*[n] f.
#n @(nat_ind_succ … n) -n
/2 width=5 by coafter_isid_sn, coafter_next/
qed.
