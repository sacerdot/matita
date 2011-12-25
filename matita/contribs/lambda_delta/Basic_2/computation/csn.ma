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

include "Basic_2/reducibility/cpr.ma".
include "Basic_2/computation/acp.ma".

(* CONTEXT-SENSITIVE STRONGLY NORMALIZING TERMS *****************************)

definition csn: lenv → predicate term ≝ λL. SN … (cpr L) (eq …).

interpretation
   "context-sensitive strong normalization (term)"
   'SN L T = (csn L T). 

(* Basic properties *********************************************************)

axiom csn_acp: acp cpr (eq …) (csn …).
