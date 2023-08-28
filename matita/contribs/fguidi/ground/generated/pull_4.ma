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

include "basics/pts.ma".
include "basics/core_notation/imply_2.ma".

(* GENERATED LIBRARY ********************************************************)

lemma pull_4 (A1:Type[0])
             (A2:A1→Type[0])
             (A3:∀x1.A2 x1→Type[0])
             (A4:Type[0])
             (A:∀x1:A1.∀x2:A2 x1.A3 x1 x2 → A4 → Type[0]):
             (∀x4,x1,x2,x3. A x1 x2 x3 x4) →
             (∀x1,x2,x3,x4. A x1 x2 x3 x4).
/2 width=1 by/ qed-.
