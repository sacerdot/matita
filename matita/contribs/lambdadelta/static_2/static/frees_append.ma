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

include "static_2/syntax/append.ma".
include "static_2/static/frees.ma".

(* CONTEXT-SENSITIVE FREE VARIABLES *****************************************)

(* Properties with append for local environments ****************************)

lemma frees_append_void: ∀f,K,T. K ⊢ 𝐅+⦃T⦄ ≘ f → ⓧ.K ⊢ 𝐅+⦃T⦄ ≘ f.
#f #K #T #H elim H -f -K -T
[ /2 width=1 by frees_sort/
| #f * /3 width=1 by frees_atom, frees_unit, frees_lref/
| /2 width=1 by frees_pair/
| /2 width=1 by frees_unit/
| /2 width=1 by frees_lref/
| /2 width=1 by frees_gref/
| /3 width=5 by frees_bind/
| /3 width=5 by frees_flat/
]
qed.

(* Inversion lemmas with append for local environments **********************)

fact frees_inv_append_void_aux:
     ∀f,L,T. L ⊢ 𝐅+⦃T⦄ ≘ f →
     ∀K. L = ⓧ.K → K ⊢ 𝐅+⦃T⦄ ≘ f.
#f #L #T #H elim H -f -L -T
[ /2 width=1 by frees_sort/
| #f #i #_ #K #H
  elim (append_inv_atom3_sn … H) -H #H1 #H2 destruct
| #f #I #L #V #_ #IH #K #H
  elim (append_inv_bind3_sn … H) -H * [ | #Y ] #H1 #H2 destruct
  /3 width=1 by frees_pair/
| #f #I #L #Hf #K #H
  elim (append_inv_bind3_sn … H) -H * [ | #Y ] #H1 #H2 destruct
  /2 width=1 by frees_atom, frees_unit/
| #f #I #L #i #Hf #IH #K #H
  elim (append_inv_bind3_sn … H) -H * [ | #Y ] #H1 #H2 destruct
  /3 width=1 by frees_lref, frees_lref_push/
| /2 width=1 by frees_gref/
| /3 width=5 by frees_bind/
| /3 width=5 by frees_flat/
]
qed-.

lemma frees_inv_append_void: ∀f,K,T. ⓧ.K  ⊢ 𝐅+⦃T⦄ ≘ f → K ⊢ 𝐅+⦃T⦄ ≘ f.
/2 width=3 by frees_inv_append_void_aux/ qed-.
