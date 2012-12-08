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

include "labelled_hap_computation.ma".

(* KASHIMA'S "ST" COMPUTATION ***********************************************)

(* Note: this is the "standard" computation of:
         R. Kashima: "A proof of the Standization Theorem in λ-Calculus". Typescript note, (2000).
*)
inductive st: relation term ≝
| st_vref: ∀s,M,i. lhap s M (#i) → st M (#i)
| st_abst: ∀s,M,A1,A2. lhap s M (𝛌.A1) → st A1 A2 → st M (𝛌.A2)
| st_appl: ∀s,M,B1,B2,A1,A2. lhap s M (@B1.A1) → st B1 B2 → st A1 A2 → st M (@B2.A2)
.

