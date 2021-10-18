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

include "static_2/notation/relations/ideq_3.ma".
include "static_2/syntax/teqg_ext.ma".
include "static_2/syntax/teq.ma".

(* SYNTACTIC EQUIVALENCE ****************************************************)

definition ceq: relation3 lenv term term ≝
           ceqg (eq …).

definition ceq_ext: lenv → relation bind ≝
           ceqg_ext (eq …).

interpretation
  "context-dependent syntactic equivalence (term)"
  'IdEq L T1 T2 = (ceq L T1 T2).

interpretation
  "context-dependent syntactic equivalence (binder)"
  'IdEq L I1 I2 = (ceq_ext L I1 I2).

(* Basic properties *********************************************************)

lemma ceq_ext_refl (L):
     reflexive … (ceq_ext L).
/2 width=1 by ext2_refl/ qed.

lemma ceq_ext_sym (L):
      symmetric … (ceq_ext L).
#L @ext2_sym (**) (* full auto does not work *)
/2 width=1 by teq_sym/
qed-.

(* Basic inversion lemmas ***************************************************)

lemma ceq_ext_inv_eq (L):
      ∀I1,I2. L ⊢ I1 ≡ I2 → I1 = I2.
#L #I1 #I2 * -I1 -I2
/3 width=4 by teq_inv_eq, eq_f3/
qed-.
