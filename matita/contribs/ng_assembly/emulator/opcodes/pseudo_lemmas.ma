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

include "emulator/opcodes/Freescale_pseudo_lemmas.ma".
include "emulator/opcodes/Freescale_instr_mode_lemmas.ma".
include "emulator/opcodes/IP2022_pseudo_lemmas.ma".
include "emulator/opcodes/IP2022_instr_mode_lemmas.ma".
include "emulator/opcodes/pseudo.ma".

nlemma eq_to_eqpseudo : ∀m.∀n1,n2.(n1 = n2) → (eq_pseudo m n1 n2 = true).
 #m; nelim m;
 ##[ ##1,2,3,4: napply eq_to_eqFreescalepseudo
 ##| ##5: napply eq_to_eqIP2022pseudo
 ##]
nqed.

nlemma neqpseudo_to_neq : ∀m.∀n1,n2.(eq_pseudo m n1 n2 = false) → (n1 ≠ n2).
 #m; nelim m;
 ##[ ##1,2,3,4: napply neqFreescalepseudo_to_neq
 ##| ##5: napply neqIP2022pseudo_to_neq
 ##]
nqed.

nlemma eqpseudo_to_eq : ∀m.∀n1,n2.(eq_pseudo m n1 n2 = true) → (n1 = n2).
 #m; nelim m;
 ##[ ##1,2,3,4: napply eqFreescalepseudo_to_eq
 ##| ##5: napply eqIP2022pseudo_to_eq
 ##]
nqed.

nlemma neq_to_neqpseudo : ∀m.∀n1,n2.(n1 ≠ n2) → (eq_pseudo m n1 n2 = false).
 #m; nelim m;
 ##[ ##1,2,3,4: napply neq_to_neqFreescalepseudo
 ##| ##5: napply neq_to_neqIP2022pseudo
 ##]
nqed.

nlemma decidable_pseudo : ∀m.∀x,y:aux_pseudo_type m.decidable (x = y).
 #m; nelim m;
 ##[ ##1,2,3,4: napply decidable_Freescalepseudo
 ##| ##5: napply decidable_IP2022pseudo
 ##]
nqed.

nlemma symmetric_eqpseudo : ∀m.symmetricT (aux_pseudo_type m) bool (eq_pseudo m).
 #m; nelim m;
 ##[ ##1,2,3,4: napply symmetric_eqFreescalepseudo
 ##| ##5: napply symmetric_eqIP2022pseudo
 ##]
nqed.

nlemma eq_to_eqim : ∀m.∀n1,n2.(n1 = n2) → (eq_im m n1 n2 = true).
 #m; nelim m;
 ##[ ##1,2,3,4: napply eq_to_eqFreescaleim
 ##| ##5: napply eq_to_eqIP2022im
 ##]
nqed.

nlemma neqim_to_neq : ∀m.∀n1,n2.(eq_im m n1 n2 = false) → (n1 ≠ n2).
 #m; nelim m;
 ##[ ##1,2,3,4: napply neqFreescaleim_to_neq
 ##| ##5: napply neqIP2022im_to_neq
 ##]
nqed.

nlemma eqim_to_eq : ∀m.∀n1,n2.(eq_im m n1 n2 = true) → (n1 = n2).
 #m; nelim m;
 ##[ ##1,2,3,4: napply eqFreescaleim_to_eq
 ##| ##5: napply eqIP2022im_to_eq
 ##]
nqed.

nlemma neq_to_neqim : ∀m.∀n1,n2.(n1 ≠ n2) → (eq_im m n1 n2 = false).
 #m; nelim m;
 ##[ ##1,2,3,4: napply neq_to_neqFreescaleim
 ##| ##5: napply neq_to_neqIP2022im
 ##]
nqed.

nlemma decidable_im : ∀m.∀x,y:aux_im_type m.decidable (x = y).
 #m; nelim m;
 ##[ ##1,2,3,4: napply decidable_Freescaleim
 ##| ##5: napply decidable_IP2022im
 ##]
nqed.

nlemma symmetric_eqim : ∀m.symmetricT (aux_im_type m) bool (eq_im m).
 #m; nelim m;
 ##[ ##1,2,3,4: napply symmetric_eqFreescaleim
 ##| ##5: napply symmetric_eqIP2022im
 ##]
nqed.
