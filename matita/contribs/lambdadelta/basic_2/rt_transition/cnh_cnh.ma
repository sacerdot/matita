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

include "basic_2/rt_transition/cpm.ma".
include "basic_2/rt_transition/cnh.ma".

(* NORMAL TERMS FOR HEAD T-UNUNBOUND RT-TRANSITION **************************)

(* Advanced properties ******************************************************)

axiom cnh_cpm_trans (h) (n) (G) (L):
      ∀T1,T2. ⦃G,L⦄ ⊢ T1 ➡[n,h] T2 → ⦃G,L⦄ ⊢ ⥲[h] 𝐍⦃T1⦄ → ⦃G,L⦄ ⊢ ⥲[h] 𝐍⦃T2⦄.
(*
#h #n #G #L #T1 #T2 #HT1 #n #T2 #HT12 #k #X #HX 
*)
