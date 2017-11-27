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

include "basic_2/static/frees_drops.ma".
include "basic_2/static/fle.ma".

(* FREE VARIABLES INCLUSION FOR RESTRICTED CLOSURES *************************)

(* Advanced properties ******************************************************)

lemma fle_bind_dx: ∀T,U. ⬆*[1] T ≡ U →
                   ∀p,I,L,V. ⦃L, T⦄ ⊆ ⦃L, ⓑ{p,I}V.U⦄.
#T #U #HTU #p #I #L #V
elim (frees_total L V) #f1 #Hf1
elim (frees_total L T) #f2 #Hf2
elim (sor_isfin_ex f1 f2) /3 width=3 by frees_fwd_isfin, isfin_tl/ #f #H #_
lapply (sor_inv_sle_dx … H) #Hf0
>(tl_push_rew f) in H; #Hf
/6 width=6 by frees_lifts_SO, frees_bind, drops_refl, drops_drop, ex3_2_intro/
qed.
