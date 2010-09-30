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

include "num/bitrigesim.ma".
include "num/bool_lemmas.ma".

(* ************* *)
(* BITRIGESIMALI *)
(* ************* *)

(*
ndefinition bitrigesim_destruct_aux ≝
Πt1,t2:bitrigesim.ΠP:Prop.t1 = t2 →
 match eq_bit t1 t2 with [ true ⇒ P → P | false ⇒ P ].

ndefinition bitrigesim_destruct : bitrigesim_destruct_aux.
 #t1; #t2; #P; #H;
 nrewrite < H;
 nelim t1;
 nnormalize;
 napply (λx.x).
nqed.
*)

nlemma eq_to_eqbit : ∀n1,n2.n1 = n2 → eq_bit n1 n2 = true.
 #n1; #n2; #H;
 nrewrite > H;
 nelim n2;
 nnormalize;
 napply refl_eq.
nqed.

nlemma neqbit_to_neq : ∀n1,n2.eq_bit n1 n2 = false → n1 ≠ n2.
 #n1; #n2; #H;
 napply (not_to_not (n1 = n2) (eq_bit n1 n2 = true) …);
 ##[ ##1: napply (eq_to_eqbit n1 n2)
 ##| ##2: napply (eqfalse_to_neqtrue … H)
 ##]
nqed.

(* !!! per brevita... *)
naxiom eqbit_to_eq : ∀t1,t2.eq_bit t1 t2 = true → t1 = t2.

nlemma neq_to_neqbit : ∀n1,n2.n1 ≠ n2 → eq_bit n1 n2 = false.
 #n1; #n2; #H;
 napply (neqtrue_to_eqfalse (eq_bit n1 n2));
 napply (not_to_not (eq_bit n1 n2 = true) (n1 = n2) ? H);
 napply (eqbit_to_eq n1 n2).
nqed.

nlemma decidable_bit : ∀x,y:bitrigesim.decidable (x = y).
 #x; #y; nnormalize;
 napply (or2_elim (eq_bit x y = true) (eq_bit x y = false) ? (decidable_bexpr ?));
 ##[ ##1: #H; napply (or2_intro1 (x = y) (x ≠ y) (eqbit_to_eq … H))
 ##| ##2: #H; napply (or2_intro2 (x = y) (x ≠ y) (neqbit_to_neq … H))
 ##]
nqed.

nlemma symmetric_eqbit : symmetricT bitrigesim bool eq_bit.
 #n1; #n2;
 napply (or2_elim (n1 = n2) (n1 ≠ n2) ? (decidable_bit n1 n2));
 ##[ ##1: #H; nrewrite > H; napply refl_eq
 ##| ##2: #H; nrewrite > (neq_to_neqbit n1 n2 H);
          napply (symmetric_eq ? (eq_bit n2 n1) false);
          napply (neq_to_neqbit n2 n1 (symmetric_neq ? n1 n2 H))
 ##]
nqed.
