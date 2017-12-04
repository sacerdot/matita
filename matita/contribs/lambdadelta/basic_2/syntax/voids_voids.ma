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

include "basic_2/syntax/voids.ma".

(* EQUIVALENCE FOR LOCAL ENVIRONMENTS UP TO EXCLUSION BINDERS ***************)

(* Main inversion lemmas ****************************************************)

theorem voids_inj: ∀L1,L2,n1,n2. ⓧ*[n1]L1 ≋ ⓧ*[n2]L2 →
                   ∀m1,m2. ⓧ*[m1]L1 ≋ ⓧ*[m2]L2 →
                   ∧∧ n1 = m1 & n2 = m2.
