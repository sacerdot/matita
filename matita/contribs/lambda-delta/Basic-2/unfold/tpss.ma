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

include "Basic-2/substitution/tps.ma".

(* PARTIAL UNFOLD ON TERMS **************************************************)

definition tpss: nat → nat → lenv → relation term ≝
                 λd,e,L. TC … (tps d e L).

interpretation "partial unfold (term)"
   'PSubstStar L T1 d e T2 = (tpss d e L T1 T2).

(* Basic properties *********************************************************)

