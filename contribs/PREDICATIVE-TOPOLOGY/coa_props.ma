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

set "baseuri" "cic:/matita/PREDICATIVE-TOPOLOGY/coa_props".

include "coa_defs.ma".

inductive True:Prop \def T:True.

theorem zero_le: 
  \forall (P:COA). \forall (p:P). (le ? (zero P) p) \to True.
  intros.
  exact T.
qed.

  
  
  
