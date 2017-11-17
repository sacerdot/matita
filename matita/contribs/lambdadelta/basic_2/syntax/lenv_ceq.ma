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

include "basic_2/syntax/lenv_ext2.ma".

(* EXTENSION TO BINDERS OF A CONTEXT-SENSITIVE RELATION FOR TERMS ***********)

definition ceq_ext: lenv → relation bind ≝
                    cext2 ceq.

(* Basic properties *********************************************************)

lemma ceq_ext_refl (L): reflexive … (ceq_ext L).
/2 width=1 by ext2_refl/ qed.

(* Basic inversion lemmas ***************************************************)

lemma ceq_ext_inv_eq: ∀L,I1,I2. ceq_ext L I1 I2 → I1 = I2.
#L #I1 #I2 * -I1 -I2 //
qed-.   
