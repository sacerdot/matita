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

include "basic_2/dynamic/nta.ma".
include "basic_2/i_dynamic/ntas.ma".

(* ITERATED NATIVE TYPE ASSIGNMENT FOR TERMS ********************************)

(*

definition ntas: sh → lenv → relation term ≝
                 λh,L. star … (nta h L).

(* Basic eliminators ********************************************************)

axiom ntas_ind_dx: ∀h,L,T2. ∀R:predicate term. R T2 →
                   (∀T1,T. ⦃h, L⦄ ⊢ T1 : T → ⦃h, L⦄ ⊢ T :* T2 → R T → R T1) →
                   ∀T1. ⦃h, L⦄ ⊢ T1 :* T2 → R T1.
(*
#h #L #T2 #R #HT2 #IHT2 #T1 #HT12
@(star_ind_dx … HT2 IHT2 … HT12) //
qed-.
*)
(* Basic properties *********************************************************)

lemma ntas_strap1: ∀h,L,T1,T,T2.
                   ⦃h, L⦄ ⊢ T1 :* T → ⦃h, L⦄  ⊢ T : T2 → ⦃h, L⦄  ⊢ T1 :* T2.
/2 width=3/ qed.

lemma ntas_strap2: ∀h,L,T1,T,T2.
                   ⦃h, L⦄  ⊢ T1 : T → ⦃h, L⦄ ⊢ T :* T2 → ⦃h, L⦄ ⊢ T1 :* T2.
/2 width=3/ qed.
*)
