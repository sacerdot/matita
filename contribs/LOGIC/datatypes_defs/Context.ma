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



(* FLAT CONTEXTS
   - Naming policy:
     - contexts: P Q
*)

include "datatypes_defs/Proof.ma".
include "datatypes_defs/Sequent.ma".

inductive Context: Type \def
   | leaf: Context
   | abst: Context \to Proof \to Proof \to Sequent \to Context
.
(*
definition inj: Sequent \to Context \def abst leaf.

coercion cic:/matita/LOGIC/datatypes_defs/Context/inj.con.
*)
