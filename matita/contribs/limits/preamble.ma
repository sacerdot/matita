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

(* Project started Wed Oct 12, 2005 ***************************************)
(* Project taken over by "formal_topology" and restarted Mon Apr 6, 2009 **)
(* Project taken over by "lambdadelta" and restarted Sun Sept 20, 2015 ****)

include "basics/logic.ma".
include "../lambdadelta/ground/notation/xoa/false_0.ma".
include "../lambdadelta/ground/notation/xoa/true_0.ma".

interpretation "logical false" 'false = False.

interpretation "logical true" 'true = True.
