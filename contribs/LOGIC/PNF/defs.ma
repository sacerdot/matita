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

set "baseuri" "cic:/matita/LOGIC/PNF/defs".

(* NORMAL FORM PREDICATE FOR PARALLEL REDUCTION
*)

include "PRed/defs.ma".

inductive PNF: Proof \to Prop \def
   | pnf: \forall p. (\forall q. p => q \to p = q) \to PNF p
.
