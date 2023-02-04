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

include "emulator/opcodes/Freescale_pseudo_base.ma".
include "common/comp.ma".
include "num/bool_lemmas.ma".

nlemma eq_to_eqFreescalepseudo : ∀n1,n2.n1 = n2 → eq_Freescale_pseudo n1 n2 = true.
 #n1; #n2; #H;
 nrewrite > H;
 nelim n2;
 nnormalize;
 napply refl_eq.
nqed.

nlemma neqFreescalepseudo_to_neq : ∀n1,n2.eq_Freescale_pseudo n1 n2 = false → n1 ≠ n2.
 #n1; #n2; #H;
 napply (not_to_not (n1 = n2) (eq_Freescale_pseudo n1 n2 = true) …);
 ##[ ##1: napply (eq_to_eqFreescalepseudo n1 n2)
 ##| ##2: napply (eqfalse_to_neqtrue … H)
 ##]
nqed.

(* !!! per brevita... *)
naxiom eqFreescalepseudo_to_eq : ∀c1,c2.eq_Freescale_pseudo c1 c2 = true → c1 = c2.

nlemma neq_to_neqFreescalepseudo : ∀n1,n2.n1 ≠ n2 → eq_Freescale_pseudo n1 n2 = false.
 #n1; #n2; #H;
 napply (neqtrue_to_eqfalse (eq_Freescale_pseudo n1 n2));
 napply (not_to_not (eq_Freescale_pseudo n1 n2 = true) (n1 = n2) ? H);
 napply (eqFreescalepseudo_to_eq n1 n2).
nqed.

nlemma decidable_Freescalepseudo : ∀x,y:Freescale_pseudo.decidable (x = y).
 #x; #y; nnormalize;
 napply (or2_elim (eq_Freescale_pseudo x y = true) (eq_Freescale_pseudo x y = false) ? (decidable_bexpr ?));
 ##[ ##1: #H; napply (or2_intro1 (x = y) (x ≠ y) (eqFreescalepseudo_to_eq … H))
 ##| ##2: #H; napply (or2_intro2 (x = y) (x ≠ y) (neqFreescalepseudo_to_neq … H))
 ##]
nqed.

nlemma symmetric_eqFreescalepseudo : symmetricT Freescale_pseudo bool eq_Freescale_pseudo.
 #n1; #n2;
 napply (or2_elim (n1 = n2) (n1 ≠ n2) ? (decidable_Freescalepseudo n1 n2));
 ##[ ##1: #H; nrewrite > H; napply refl_eq
 ##| ##2: #H; nrewrite > (neq_to_neqFreescalepseudo n1 n2 H);
          napply (symmetric_eq ? (eq_Freescale_pseudo n2 n1) false);
          napply (neq_to_neqFreescalepseudo n2 n1 (symmetric_neq ? n1 n2 H))
 ##]
nqed.

nlemma Freescalepseudo_is_comparable : comparable.
 @ Freescale_pseudo
  ##[ napply ADC
  ##| napply forall_Freescale_pseudo
  ##| napply eq_Freescale_pseudo
  ##| napply eqFreescalepseudo_to_eq
  ##| napply eq_to_eqFreescalepseudo
  ##| napply neqFreescalepseudo_to_neq
  ##| napply neq_to_neqFreescalepseudo
  ##| napply decidable_Freescalepseudo
  ##| napply symmetric_eqFreescalepseudo
  ##]
nqed.

unification hint 0 ≔ ⊢ carr Freescalepseudo_is_comparable ≡ Freescale_pseudo.
