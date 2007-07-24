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

set "baseuri" "cic:/matita/LOGIC/datatypes/Context".

(* FLAT CONTEXTS
   - Naming policy:
     - contexts: P Q
*)

include "datatypes/Sequent.ma".

inductive Context: Type \def
   | leaf: Context
   | abst: Context \to Sequent \to Context
.

definition inj: Sequent \to Context \def abst leaf.

coercion cic:/matita/LOGIC/datatypes/Context/inj.con.
