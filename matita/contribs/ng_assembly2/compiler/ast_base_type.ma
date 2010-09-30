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

(* ********************************************************************** *)
(*                          Progetto FreeScale                            *)
(*                                                                        *)
(*   Sviluppato da: Ing. Cosimo Oliboni, oliboni@cs.unibo.it              *)
(*   Sviluppo: 2008-2010                                                  *)
(*                                                                        *)
(* ********************************************************************** *)

include "compiler/ast_base_type_base.ma".
include "common/comp.ma".
include "num/bool_lemmas.ma".

(* ************************* *)
(* dimensioni degli elementi *)
(* ************************* *)

ndefinition astbasetype_destruct_aux ≝
Πb1,b2:ast_base_type.ΠP:Prop.b1 = b2 →
 match eq_astbasetype b1 b2 with [ true ⇒ P → P | false ⇒ P ].

ndefinition astbasetype_destruct : astbasetype_destruct_aux.
 #b1; #b2; #P; #H;
 nrewrite < H;
 nelim b1;
 nnormalize;
 napply (λx.x).
nqed.

nlemma eq_to_eqastbasetype : ∀n1,n2.n1 = n2 → eq_astbasetype n1 n2 = true.
 #n1; #n2; #H;
 nrewrite > H;
 nelim n2;
 nnormalize;
 napply refl_eq.
nqed.

nlemma neqastbasetype_to_neq : ∀n1,n2.eq_astbasetype n1 n2 = false → n1 ≠ n2.
 #n1; #n2; #H;
 napply (not_to_not (n1 = n2) (eq_astbasetype n1 n2 = true) …);
 ##[ ##1: napply (eq_to_eqastbasetype n1 n2)
 ##| ##2: napply (eqfalse_to_neqtrue … H)
 ##]
nqed.

nlemma eqastbasetype_to_eq : ∀b1,b2.eq_astbasetype b1 b2 = true → b1 = b2.
 #b1; #b2; ncases b1; ncases b2; nnormalize;
 ##[ ##1,5,9: #H; napply refl_eq
 ##| ##*: #H; ndestruct (*napply (bool_destruct … H)*)
 ##]
nqed.

nlemma neq_to_neqastbasetype : ∀n1,n2.n1 ≠ n2 → eq_astbasetype n1 n2 = false.
 #n1; #n2; #H;
 napply (neqtrue_to_eqfalse (eq_astbasetype n1 n2));
 napply (not_to_not (eq_astbasetype n1 n2 = true) (n1 = n2) ? H);
 napply (eqastbasetype_to_eq n1 n2).
nqed.

nlemma decidable_astbasetype : ∀x,y:ast_base_type.decidable (x = y).
 #x; #y; nnormalize;
 napply (or2_elim (eq_astbasetype x y = true) (eq_astbasetype x y = false) ? (decidable_bexpr ?));
 ##[ ##1: #H; napply (or2_intro1 (x = y) (x ≠ y) (eqastbasetype_to_eq … H))
 ##| ##2: #H; napply (or2_intro2 (x = y) (x ≠ y) (neqastbasetype_to_neq … H))
 ##]
nqed.

nlemma symmetric_eqastbasetype : symmetricT ast_base_type bool eq_astbasetype.
 #n1; #n2;
 napply (or2_elim (n1 = n2) (n1 ≠ n2) ? (decidable_astbasetype n1 n2));
 ##[ ##1: #H; nrewrite > H; napply refl_eq
 ##| ##2: #H; nrewrite > (neq_to_neqastbasetype n1 n2 H);
          napply (symmetric_eq ? (eq_astbasetype n2 n1) false);
          napply (neq_to_neqastbasetype n2 n1 (symmetric_neq ? n1 n2 H))
 ##]
nqed.

nlemma astbasetype_is_comparable : comparable.
 @ ast_base_type
  ##[ napply AST_BASE_TYPE_BYTE8
  ##| napply forall_astbasetype
  ##| napply eq_astbasetype
  ##| napply eqastbasetype_to_eq
  ##| napply eq_to_eqastbasetype
  ##| napply neqastbasetype_to_neq
  ##| napply neq_to_neqastbasetype
  ##| napply decidable_astbasetype
  ##| napply symmetric_eqastbasetype
  ##]
nqed.

unification hint 0 ≔ ⊢ carr astbasetype_is_comparable ≡ ast_base_type.

