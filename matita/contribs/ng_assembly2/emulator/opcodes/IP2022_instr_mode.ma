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

include "emulator/opcodes/IP2022_instr_mode_base.ma".

nlemma eq_to_eqIP2022im : ∀n1,n2.n1 = n2 → eq_IP2022_im n1 n2 = true.
 #n1; #n2; #H;
 nrewrite > H;
 nelim n2;
 ##[ ##4,11,12: #o; nrewrite > (eq_to_eqoct … (refl_eq …))
 ##| ##6: #t; nrewrite > (eq_to_eqbit … (refl_eq …)) ##]
 nnormalize;
 napply refl_eq.
nqed.

nlemma neqIP2022im_to_neq : ∀n1,n2.eq_IP2022_im n1 n2 = false → n1 ≠ n2.
 #n1; #n2; #H;
 napply (not_to_not (n1 = n2) (eq_IP2022_im n1 n2 = true) …);
 ##[ ##1: napply (eq_to_eqIP2022im n1 n2)
 ##| ##2: napply (eqfalse_to_neqtrue … H)
 ##]
nqed.

(* !!! per brevita... *)
naxiom eqIP2022im_to_eq : ∀c1,c2.eq_IP2022_im c1 c2 = true → c1 = c2.

nlemma neq_to_neqIP2022im : ∀n1,n2.n1 ≠ n2 → eq_IP2022_im n1 n2 = false.
 #n1; #n2; #H;
 napply (neqtrue_to_eqfalse (eq_IP2022_im n1 n2));
 napply (not_to_not (eq_IP2022_im n1 n2 = true) (n1 = n2) ? H);
 napply (eqIP2022im_to_eq n1 n2).
nqed.

nlemma decidable_IP2022im : ∀x,y:IP2022_instr_mode.decidable (x = y).
 #x; #y; nnormalize;
 napply (or2_elim (eq_IP2022_im x y = true) (eq_IP2022_im x y = false) ? (decidable_bexpr ?));
 ##[ ##1: #H; napply (or2_intro1 (x = y) (x ≠ y) (eqIP2022im_to_eq … H))
 ##| ##2: #H; napply (or2_intro2 (x = y) (x ≠ y) (neqIP2022im_to_neq … H))
 ##]
nqed.

nlemma symmetric_eqIP2022im : symmetricT IP2022_instr_mode bool eq_IP2022_im.
 #n1; #n2;
 napply (or2_elim (n1 = n2) (n1 ≠ n2) ? (decidable_IP2022im n1 n2));
 ##[ ##1: #H; nrewrite > H; napply refl_eq
 ##| ##2: #H; nrewrite > (neq_to_neqIP2022im n1 n2 H);
          napply (symmetric_eq ? (eq_IP2022_im n2 n1) false);
          napply (neq_to_neqIP2022im n2 n1 (symmetric_neq ? n1 n2 H))
 ##]
nqed.

nlemma IP2022im_is_comparable : comparable.
 @ IP2022_instr_mode
  ##[ napply MODE_INH
  ##| napply forall_IP2022_im
  ##| napply eq_IP2022_im
  ##| napply eqIP2022im_to_eq
  ##| napply eq_to_eqIP2022im
  ##| napply neqIP2022im_to_neq
  ##| napply neq_to_neqIP2022im
  ##| napply decidable_IP2022im
  ##| napply symmetric_eqIP2022im
  ##]
nqed.

unification hint 0 ≔ ⊢ carr IP2022im_is_comparable ≡ IP2022_instr_mode.
