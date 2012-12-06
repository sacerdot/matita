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
| st_abst: ∀s,M,A,C. lhap s M (𝛌.A) → st A C → st M (𝛌.C)
| st_appl: ∀s,M,B,D,A,C. lhap s M (@B.A) → st B D → st A C → st M (@D.C) 
.

