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

include "num/bool_lemmas.ma".
include "emulator/opcodes/Freescale_instr_mode.ma".
include "num/oct_lemmas.ma".
include "num/bitrigesim_lemmas.ma".
include "num/exadecim_lemmas.ma".

nlemma eq_to_eqFreescaleim : ∀n1,n2.n1 = n2 → eq_Freescale_im n1 n2 = true.
 #n1; #n2; #H;
 nrewrite > H;
 nelim n2;
 ##[ ##31,32: #o; nrewrite > (eq_to_eqoct … (refl_eq …))
 ##| ##33: #e; nrewrite > (eq_to_eqex … (refl_eq …))
 ##| ##34: #t; nrewrite > (eq_to_eqbit … (refl_eq …)) ##]
 napply refl_eq.
nqed.

nlemma neqFreescaleim_to_neq : ∀n1,n2.eq_Freescale_im n1 n2 = false → n1 ≠ n2.
 #n1; #n2; #H;
 napply (not_to_not (n1 = n2) (eq_Freescale_im n1 n2 = true) …);
 ##[ ##1: napply (eq_to_eqFreescaleim n1 n2)
 ##| ##2: napply (eqfalse_to_neqtrue … H)
 ##]
nqed.

(* !!! per brevita... *)
naxiom eqFreescaleim_to_eq : ∀c1,c2.eq_Freescale_im c1 c2 = true → c1 = c2.

nlemma neq_to_neqFreescaleim : ∀n1,n2.n1 ≠ n2 → eq_Freescale_im n1 n2 = false.
 #n1; #n2; #H;
 napply (neqtrue_to_eqfalse (eq_Freescale_im n1 n2));
 napply (not_to_not (eq_Freescale_im n1 n2 = true) (n1 = n2) ? H);
 napply (eqFreescaleim_to_eq n1 n2).
nqed.

nlemma decidable_Freescaleim : ∀x,y:Freescale_instr_mode.decidable (x = y).
 #x; #y; nnormalize;
 napply (or2_elim (eq_Freescale_im x y = true) (eq_Freescale_im x y = false) ? (decidable_bexpr ?));
 ##[ ##1: #H; napply (or2_intro1 (x = y) (x ≠ y) (eqFreescaleim_to_eq … H))
 ##| ##2: #H; napply (or2_intro2 (x = y) (x ≠ y) (neqFreescaleim_to_neq … H))
 ##]
nqed.

nlemma symmetric_eqFreescaleim : symmetricT Freescale_instr_mode bool eq_Freescale_im.
 #n1; #n2;
 napply (or2_elim (n1 = n2) (n1 ≠ n2) ? (decidable_Freescaleim n1 n2));
 ##[ ##1: #H; nrewrite > H; napply refl_eq
 ##| ##2: #H; nrewrite > (neq_to_neqFreescaleim n1 n2 H);
          napply (symmetric_eq ? (eq_Freescale_im n2 n1) false);
          napply (neq_to_neqFreescaleim n2 n1 (symmetric_neq ? n1 n2 H))
 ##]
nqed.
