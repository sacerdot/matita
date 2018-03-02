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

include "basic_2/static/fsle.ma".
include "basic_2/static/lfxs.ma".

(* GENERIC EXTENSION ON REFERRED ENTRIES OF A CONTEXT-SENSITIVE REALTION ****)

definition R_fsle_compatible: predicate (relation3 …) ≝ λRN.
                              ∀L,T1,T2. RN L T1 T2 → ⦃L, T2⦄ ⊆ ⦃L, T1⦄.

definition lfxs_fsle_compatible: predicate (relation3 …) ≝ λRN.
                                 ∀L1,L2,T. L1 ⪤*[RN, T] L2 → ⦃L2, T⦄ ⊆ ⦃L1, T⦄.
