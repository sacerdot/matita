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

include "basic_2/static/frees_fqup.ma".
include "basic_2/static/fle.ma".

(* FREE VARIABLES INCLUSION FOR RESTRICTED CLOSURES *************************)

(* Advanced properties ******************************************************)

lemma fle_refl: bi_reflexive … fle.
#L #T elim (frees_total L T) /2 width=5 by sle_refl, ex3_2_intro/
qed.

lemma fle_bind_sn: ∀p,I,L,V,T. ⦃L, V⦄ ⊆ ⦃L, ⓑ{p,I}V.T⦄.
#p #I #L #V #T
elim (frees_total L V) #f1 #Hf1
elim (frees_total (L.ⓑ{I}V) T) #f2 #Hf2
elim (sor_isfin_ex f1 (⫱f2)) /3 width=3 by frees_fwd_isfin, isfin_tl/ #f #Hf #_
/3 width=6 by frees_bind, sor_inv_sle_sn, ex3_2_intro/
qed.

lemma fle_flat_sn: ∀I,L,V,T. ⦃L, V⦄ ⊆ ⦃L, ⓕ{I}V.T⦄.
#I #L #V #T
elim (frees_total L V) #f1 #Hf1
elim (frees_total L T) #f2 #Hf2
elim (sor_isfin_ex f1 f2) /2 width=3 by frees_fwd_isfin/ #f #Hf #_
/3 width=6 by frees_flat, sor_inv_sle_sn, ex3_2_intro/
qed.

lemma fle_flat_dx: ∀I,L,V,T. ⦃L, T⦄ ⊆ ⦃L, ⓕ{I}V.T⦄.
#I #L #V #T
elim (frees_total L V) #f1 #Hf1
elim (frees_total L T) #f2 #Hf2
elim (sor_isfin_ex f1 f2) /2 width=3 by frees_fwd_isfin/ #f #Hf #_
/3 width=6 by frees_flat, sor_inv_sle_dx, ex3_2_intro/
qed.
