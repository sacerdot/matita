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

include "emulator/opcodes/IP2022_pseudo_base.ma".
include "common/comp.ma".
include "num/bool_lemmas.ma".

nlemma eq_to_eqIP2022pseudo : ∀n1,n2.n1 = n2 → eq_IP2022_pseudo n1 n2 = true.
 #n1; #n2; #H;
 nrewrite > H;
 nelim n2;
 nnormalize;
 napply refl_eq.
nqed.

nlemma neqIP2022pseudo_to_neq : ∀n1,n2.eq_IP2022_pseudo n1 n2 = false → n1 ≠ n2.
 #n1; #n2; #H;
 napply (not_to_not (n1 = n2) (eq_IP2022_pseudo n1 n2 = true) …);
 ##[ ##1: napply (eq_to_eqIP2022pseudo n1 n2)
 ##| ##2: napply (eqfalse_to_neqtrue … H)
 ##]
nqed.

(* !!! per brevita... *)
naxiom eqIP2022pseudo_to_eq : ∀c1,c2.eq_IP2022_pseudo c1 c2 = true → c1 = c2.

nlemma neq_to_neqIP2022pseudo : ∀n1,n2.n1 ≠ n2 → eq_IP2022_pseudo n1 n2 = false.
 #n1; #n2; #H;
 napply (neqtrue_to_eqfalse (eq_IP2022_pseudo n1 n2));
 napply (not_to_not (eq_IP2022_pseudo n1 n2 = true) (n1 = n2) ? H);
 napply (eqIP2022pseudo_to_eq n1 n2).
nqed.

nlemma decidable_IP2022pseudo : ∀x,y:IP2022_pseudo.decidable (x = y).
 #x; #y; nnormalize;
 napply (or2_elim (eq_IP2022_pseudo x y = true) (eq_IP2022_pseudo x y = false) ? (decidable_bexpr ?));
 ##[ ##1: #H; napply (or2_intro1 (x = y) (x ≠ y) (eqIP2022pseudo_to_eq … H))
 ##| ##2: #H; napply (or2_intro2 (x = y) (x ≠ y) (neqIP2022pseudo_to_neq … H))
 ##]
nqed.

nlemma symmetric_eqIP2022pseudo : symmetricT IP2022_pseudo bool eq_IP2022_pseudo.
 #n1; #n2;
 napply (or2_elim (n1 = n2) (n1 ≠ n2) ? (decidable_IP2022pseudo n1 n2));
 ##[ ##1: #H; nrewrite > H; napply refl_eq
 ##| ##2: #H; nrewrite > (neq_to_neqIP2022pseudo n1 n2 H);
          napply (symmetric_eq ? (eq_IP2022_pseudo n2 n1) false);
          napply (neq_to_neqIP2022pseudo n2 n1 (symmetric_neq ? n1 n2 H))
 ##]
nqed.

nlemma IP2022pseudo_is_comparable : comparable.
 @ IP2022_pseudo
  ##[ napply ADD
  ##| napply forall_IP2022_pseudo
  ##| napply eq_IP2022_pseudo
  ##| napply eqIP2022pseudo_to_eq
  ##| napply eq_to_eqIP2022pseudo
  ##| napply neqIP2022pseudo_to_neq
  ##| napply neq_to_neqIP2022pseudo
  ##| napply decidable_IP2022pseudo
  ##| napply symmetric_eqIP2022pseudo
  ##]
nqed.

unification hint 0 ≔ ⊢ carr IP2022pseudo_is_comparable ≡ IP2022_pseudo.
