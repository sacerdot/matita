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

include "num/exadecim.ma".
include "num/bool_lemmas.ma".

(* *********** *)
(* ESADECIMALI *)
(* *********** *)

(*
ndefinition exadecim_destruct_aux ≝
Πe1,e2.ΠP:Prop.ΠH:e1 = e2.
 match eq_ex e1 e2 with [ true ⇒ P → P | false ⇒ P ].

ndefinition exadecim_destruct : exadecim_destruct_aux.
 #e1; #e2; #P; #H;
 nrewrite < H;
 nelim e1;
 nnormalize;
 napply (λx.x).
nqed.
*)

nlemma eq_to_eqex : ∀n1,n2.n1 = n2 → eq_ex n1 n2 = true.
 #n1; #n2; #H;
 nrewrite > H;
 nelim n2;
 nnormalize;
 napply refl_eq.
nqed.

nlemma neqex_to_neq : ∀n1,n2.eq_ex n1 n2 = false → n1 ≠ n2.
 #n1; #n2; #H;
 napply (not_to_not (n1 = n2) (eq_ex n1 n2 = true) …);
 ##[ ##1: napply (eq_to_eqex n1 n2)
 ##| ##2: napply (eqfalse_to_neqtrue … H)
 ##]
nqed.

nlemma eqex_to_eq : ∀n1,n2.eq_ex n1 n2 = true → n1 = n2.
 #n1; #n2;
 ncases n1;
 ncases n2;
 nnormalize;
 ##[ ##1,18,35,52,69,86,103,120,137,154,171,188,205,222,239,256: #H; napply refl_eq
 ##| ##*: #H; ndestruct (*napply (bool_destruct … H)*)
 ##]
nqed.

nlemma neq_to_neqex : ∀n1,n2.n1 ≠ n2 → eq_ex n1 n2 = false.
 #n1; #n2; #H;
 napply (neqtrue_to_eqfalse (eq_ex n1 n2));
 napply (not_to_not (eq_ex n1 n2 = true) (n1 = n2) ? H);
 napply (eqex_to_eq n1 n2).
nqed.

nlemma decidable_ex : ∀x,y:exadecim.decidable (x = y).
 #x; #y; nnormalize;
 napply (or2_elim (eq_ex x y = true) (eq_ex x y = false) ? (decidable_bexpr ?));
 ##[ ##1: #H; napply (or2_intro1 (x = y) (x ≠ y) (eqex_to_eq … H))
 ##| ##2: #H; napply (or2_intro2 (x = y) (x ≠ y) (neqex_to_neq … H))
 ##]
nqed.

nlemma symmetric_eqex : symmetricT exadecim bool eq_ex.
 #n1; #n2;
 napply (or2_elim (n1 = n2) (n1 ≠ n2) ? (decidable_ex n1 n2));
 ##[ ##1: #H; nrewrite > H; napply refl_eq
 ##| ##2: #H; nrewrite > (neq_to_neqex n1 n2 H);
          napply (symmetric_eq ? (eq_ex n2 n1) false);
          napply (neq_to_neqex n2 n1 (symmetric_neq ? n1 n2 H))
 ##]
nqed.
