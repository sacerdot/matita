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

include "basic_2/reduction/cpr_cif.ma".
include "basic_2/reduction/cnf_crf.ma".

(* CONTEXT-SENSITIVE NORMAL TERMS *******************************************)

(* Main properties on context-sensitive irreducible terms *******************)

theorem cif_cnf: ∀L,T. L ⊢ 𝐈⦃T⦄ → L ⊢ 𝐍⦃T⦄.
/2 width=3 by cpr_fwd_cif/ qed.

(* Main inversion lemmas on context-sensitive irreducible terms *************)

theorem cnf_inv_cif: ∀L,T. L ⊢ 𝐍⦃T⦄ → L ⊢ 𝐈⦃T⦄.
/2 width=4 by cnf_inv_crf/ qed-.
