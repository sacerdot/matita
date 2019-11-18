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

include "basic_2/notation/relations/predeval_5.ma".
include "basic_2/rt_computation/cpmre.ma".
include "basic_2/rt_computation/cprs.ma".

(* EVALUATION FOR CONTEXT-SENSITIVE PARALLEL R-TRANSITION ON TERMS ***********)

(* Basic_2A1: was: cpre *)
interpretation "evaluation for context-sensitive parallel r-transition (term)"
   'PRedEval h G L T1 T2 = (cpmre h O G L T1 T2).
