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

include "common/ascii.ma".
include "num/bool_lemmas.ma".

(* ************************** *)
(* DEFINIZIONE ASCII MINIMALE *)
(* ************************** *)

(*
ndefinition ascii_destruct_aux ≝
Πc1,c2.ΠP:Prop.c1 = c2 →
 match eq_ascii c1 c2 with [ true ⇒ P → P | false ⇒ P ].

nlemma ascii_destruct : ascii_destruct_aux.
 #c1; #c2; #P; #H;
 nrewrite < H;
 nelim c1;
 nnormalize;
 napply (λx.x).
nqed.
*)

nlemma eq_to_eqascii : ∀n1,n2.n1 = n2 → eq_ascii n1 n2 = true.
 #n1; #n2; #H;
 nrewrite > H;
 nelim n2;
 nnormalize;
 napply refl_eq.
nqed.

nlemma neqascii_to_neq : ∀n1,n2.eq_ascii n1 n2 = false → n1 ≠ n2.
 #n1; #n2; #H;
 napply (not_to_not (n1 = n2) (eq_ascii n1 n2 = true) …);
 ##[ ##1: napply (eq_to_eqascii n1 n2)
 ##| ##2: napply (eqfalse_to_neqtrue … H)
 ##]
nqed.

(* !!! per brevita... *)
naxiom eqascii_to_eq : ∀c1,c2.eq_ascii c1 c2 = true → c1 = c2.

nlemma neq_to_neqascii : ∀n1,n2.n1 ≠ n2 → eq_ascii n1 n2 = false.
 #n1; #n2; #H;
 napply (neqtrue_to_eqfalse (eq_ascii n1 n2));
 napply (not_to_not (eq_ascii n1 n2 = true) (n1 = n2) ? H);
 napply (eqascii_to_eq n1 n2).
nqed.

nlemma decidable_ascii : ∀x,y:ascii.decidable (x = y).
 #x; #y; nnormalize;
 napply (or2_elim (eq_ascii x y = true) (eq_ascii x y = false) ? (decidable_bexpr ?));
 ##[ ##1: #H; napply (or2_intro1 (x = y) (x ≠ y) (eqascii_to_eq … H))
 ##| ##2: #H; napply (or2_intro2 (x = y) (x ≠ y) (neqascii_to_neq … H))
 ##]
nqed.

nlemma symmetric_eqascii : symmetricT ascii bool eq_ascii.
 #n1; #n2;
 napply (or2_elim (n1 = n2) (n1 ≠ n2) ? (decidable_ascii n1 n2));
 ##[ ##1: #H; nrewrite > H; napply refl_eq
 ##| ##2: #H; nrewrite > (neq_to_neqascii n1 n2 H);
          napply (symmetric_eq ? (eq_ascii n2 n1) false);
          napply (neq_to_neqascii n2 n1 (symmetric_neq ? n1 n2 H))
 ##]
nqed.
