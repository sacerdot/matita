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

include "Basic_2/computation/acp_cr.ma".
include "Basic_2/computation/csn.ma".

(* CONTEXT-SENSITIVE STRONGLY NORMALIZING TERMS *****************************)

(* the candidate of reducibility associated to an atomic arity *)
definition snc: aarity → lenv → predicate term ≝ acr csn.

interpretation
   "candidate of reducibility (contex-sensitive strong normalization)"
   'InEInt L T A = (snc A L T).
