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



(* PROOFS
   - Naming policy:
     - proofs: p q r s
*)

include "preamble0.ma".

inductive Proof: Type \def
   | lref: Nat \to Proof                       (* projection         *)
   | prin: Nat \to Proof                       (* pos rel inhabitant *)
   | impw: Proof \to Proof                     (* weakening          *)
   | impr: Proof \to Proof                     (* right introduction *)
   | impi: Proof \to Proof \to Proof \to Proof (* left introduction  *)
   | scut: Proof \to Proof \to Proof           (* symmetric cut      *)
.
