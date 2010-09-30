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



(* SEQUENTS
   - Naming policy:
     - left hand sides  (lhs): A C
     - right hand sides (rhs): B D
     - sequents              : R S
*)

include "datatypes_defs/Formula.ma".

inductive LHS: Type \def
   | lleaf: LHS
   | labst: LHS \to Formula \to LHS
.

inductive RHS: Type \def
   | rleaf: RHS
   | rabst: Formula \to RHS \to RHS
.

inductive Sequent: Type \def
   | pair: LHS \to RHS \to Sequent
.

definition linj: Formula \to LHS \def labst lleaf.

definition rinj: Formula \to RHS \def \lambda b. rabst b rleaf.

coercion cic:/matita/LOGIC/datatypes_defs/Sequent/linj.con.

coercion cic:/matita/LOGIC/datatypes_defs/Sequent/rinj.con.
