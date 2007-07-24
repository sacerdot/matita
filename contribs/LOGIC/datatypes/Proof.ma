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

set "baseuri" "cic:/matita/LOGIC/datatypes/Proof".

(* PROOFS
   - Naming policy:
     - proofs: p q r s
*)

include "preamble.ma".

inductive Proof: Type \def
   | lref: Nat \to Proof
   | parx: Nat \to Proof
   | impw: Proof \to Proof
   | impi: Proof \to Proof
   | impe: Proof \to Proof
(*   
   | impe: Proof \to Proof \to Proof \to Proof
*)
.
