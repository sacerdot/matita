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

include "preamble.ma".

(* APPLICATIONS *******************************************************)

definition u0_i: ∀T:Type[0]. T → T ≝
                 λT,a. a.

definition u0_k: ∀T,U:Type[0]. T → U → T ≝
                 λT,U,a,b. a.

definition u0_s: ∀T,U1,U2:Type[0]. (T → U1 → U2) → (T → U1) → (T → U2) ≝
                 λT,U1,U2,f,g,a. f a (g a).
