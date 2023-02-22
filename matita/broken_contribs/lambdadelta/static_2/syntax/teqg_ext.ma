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

include "static_2/notation/relations/stareq_4.ma".
include "static_2/syntax/cext2.ma".
include "static_2/syntax/teqg.ma".

(* GENERIC EQUIVALENCE ******************************************************)

definition teqg_ext (S): relation bind ≝
           ext2 (teqg S).

definition ceqg (S): relation3 lenv term term ≝
           λL. (teqg S).

definition ceqg_ext (S): relation3 lenv bind bind ≝
           cext2 (ceqg S).

interpretation
  "context-free generic equivalence (binder)"
  'StarEq S I1 I2 = (teqg_ext S I1 I2).

interpretation
  "context-dependent generic equivalence (term)"
  'StarEq S L T1 T2 = (ceqg S L T1 T2).

interpretation
  "context-dependent generic equivalence (binder)"
  'StarEq S L I1 I2 = (ceqg_ext S L I1 I2).
