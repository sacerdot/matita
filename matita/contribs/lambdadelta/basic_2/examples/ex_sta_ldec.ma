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

include "basic_2/unfold/lstas.ma".

(* EXAMPLES *****************************************************************)

(* Static type assignment (iterated vs primitive): the declared variable ****)

(* basic_1: we have "L.ⓛⓝ⋆k1.⋆k2⦄ ⊢ #0 • ⓝ⋆k1.⋆k2". *)
theorem sta_ldec: ∀h,G,L,s1,s2. ⦃G, L.ⓛⓝ⋆s1.⋆s2⦄ ⊢ #0 •*[h, 1] ⋆s2.
/3 width=6 by lstas_sort, lstas_succ, lstas_cast, drop_pair/ qed-.
