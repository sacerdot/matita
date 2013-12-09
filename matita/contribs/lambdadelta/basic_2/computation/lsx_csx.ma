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

include "basic_2/computation/lpxs_lleq.ma".
include "basic_2/computation/csx_alt.ma".
include "basic_2/computation/lsx.ma".

(* SN EXTENDED STRONGLY NORMALIZING LOCAL ENVIRONMENTS **********************)

(* Main properties **********************************************************)

axiom csx_lsx: ∀h,g,G,L,T. ⦃G, L⦄ ⊢ ⬊*[h, g] T → G ⊢ ⋕⬊*[h, g, T] L.

axiom lsx_inv_csx: ∀h,g,G,L,T. G ⊢ ⋕⬊*[h, g, T] L → ⦃G, L⦄ ⊢ ⬊*[h, g] T.

(*
#h #g #G #L1 #T1 #H @(csx_ind_alt … H) -T1
#T1 #_ #IHT1 @lsx_intro
#L2 #HL12 #HnT1 elim (lpxs_inv_cpxs_nlleq … HL12 HnT1) -HL12 -HnT1
#T2 #H1T12 #HnT12 #H2T12 lapply (IHT1 … H1T12 HnT12) -IHT1 -H1T12 -HnT12
#HT2  
*)
