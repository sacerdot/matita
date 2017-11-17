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

include "basic_2/notation/relations/relation_3.ma".
include "basic_2/relocation/lexs.ma".

(* GENERIC EXTENSION OF A CONTEXT-SENSITIVE REALTION ON TERMS ***************)

(* Basic_2A1: includes: lpx_sn_atom lpx_sn_pair *)
definition lex: (lenv → relation bind) → relation lenv ≝
                λR,L1,L2. ∃∃f. 𝐈⦃f⦄ & L1 ⪤*[cfull, R, f] L2.

interpretation "generic extension (local environment)"
   'Relation R L1 L2 = (lex R L1 L2).
