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

include "u0_class.ma".

(* CLASSES FROM DATA TYPES ********************************************)

definition u0_data: Type[0] → u0_class ≝
                    λT. mk_u0_class T (u0_full T) (eq T).

(* Basic properties ***************************************************)

lemma u0_class_data: ∀T. is_u0_class (u0_data T).
/2 width=1 by mk_is_u0_class/ qed.
