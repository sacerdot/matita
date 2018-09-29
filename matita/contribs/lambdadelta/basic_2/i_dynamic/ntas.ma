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

include "basic_2/notation/relations/colon_7.ma".
include "basic_2/notation/relations/colon_6.ma".
include "basic_2/notation/relations/colonstar_6.ma".
include "basic_2/dynamic/cnv.ma".

(* ITERATED NATIVE TYPE ASSIGNMENT FOR TERMS ********************************)

definition ntas (a) (h) (n) (G) (L): relation term ≝ λT,U.
           ∃∃U0. ⦃G,L⦄ ⊢ U ![a,h] & ⦃G,L⦄ ⊢ T ![a,h] & ⦃G,L⦄ ⊢ U ➡*[h] U0 & ⦃G, L⦄ ⊢ T ➡*[n,h] U0.

interpretation "iterated native type assignment (term)"
   'Colon a h n G L T U = (ntas a h n G L T U).

interpretation "restricted iterated native type assignment (term)"
   'Colon h n G L T U = (ntas true h n G L T U).

interpretation "extended iterated native type assignment (term)"
   'ColonStar h n G L T U = (ntas false h n G L T U).

(* Basic properties *********************************************************)

lemma ntas_refl (a) (h) (G) (L):
      ∀T. ⦃G,L⦄ ⊢ T ![a,h] → ⦃G,L⦄ ⊢ T :[a,h,0] T.
/2 width=3 by ex4_intro/ qed.
