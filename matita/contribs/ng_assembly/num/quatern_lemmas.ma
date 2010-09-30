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

include "num/quatern.ma".
include "num/bool_lemmas.ma".

(* ********** *)
(* QUATERNARI *)
(* ********** *)

(*
ndefinition quatern_destruct_aux ≝
Πn1,n2:quatern.ΠP:Prop.n1 = n2 →
 match eq_qu n1 n2 with [ true ⇒ P → P | false ⇒ P ].

ndefinition quatern_destruct : quatern_destruct_aux.
 #n1; #n2; #P; #H;
 nrewrite < H;
 nelim n1;
 nnormalize;
 napply (λx.x).
nqed.
*)

nlemma eq_to_eqqu : ∀n1,n2.n1 = n2 → eq_qu n1 n2 = true.
 #n1; #n2; #H;
 nrewrite > H;
 nelim n2;
 nnormalize;
 napply refl_eq.
nqed.

nlemma neqqu_to_neq : ∀n1,n2.eq_qu n1 n2 = false → n1 ≠ n2.
 #n1; #n2; #H;
 napply (not_to_not (n1 = n2) (eq_qu n1 n2 = true) …);
 ##[ ##1: napply (eq_to_eqqu n1 n2)
 ##| ##2: napply (eqfalse_to_neqtrue … H)
 ##]
nqed.

nlemma eqqu_to_eq : ∀n1,n2.eq_qu n1 n2 = true → n1 = n2.
 #n1; #n2;
 ncases n1;
 ncases n2;
 nnormalize;
 ##[ ##1,6,11,16: #H; napply refl_eq
 ##| ##*: #H; ndestruct (*napply (bool_destruct … H)*)
 ##]
nqed.

nlemma neq_to_neqqu : ∀n1,n2.n1 ≠ n2 → eq_qu n1 n2 = false.
 #n1; #n2; #H;
 napply (neqtrue_to_eqfalse (eq_qu n1 n2));
 napply (not_to_not (eq_qu n1 n2 = true) (n1 = n2) ? H);
 napply (eqqu_to_eq n1 n2).
nqed.

nlemma decidable_qu : ∀x,y:quatern.decidable (x = y).
 #x; #y; nnormalize;
 napply (or2_elim (eq_qu x y = true) (eq_qu x y = false) ? (decidable_bexpr ?));
 ##[ ##1: #H; napply (or2_intro1 (x = y) (x ≠ y) (eqqu_to_eq … H))
 ##| ##2: #H; napply (or2_intro2 (x = y) (x ≠ y) (neqqu_to_neq … H))
 ##]
nqed.

nlemma symmetric_eqqu : symmetricT quatern bool eq_qu.
 #n1; #n2;
 napply (or2_elim (n1 = n2) (n1 ≠ n2) ? (decidable_qu n1 n2));
 ##[ ##1: #H; nrewrite > H; napply refl_eq
 ##| ##2: #H; nrewrite > (neq_to_neqqu n1 n2 H);
          napply (symmetric_eq ? (eq_qu n2 n1) false);
          napply (neq_to_neqqu n2 n1 (symmetric_neq ? n1 n2 H))
 ##]
nqed.
