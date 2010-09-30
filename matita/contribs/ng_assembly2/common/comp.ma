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

include "common/hints_declaration.ma".
include "num/bool.ma".

alias symbol "hint_decl" (instance 1) = "hint_decl_Type1".

nrecord comparable : Type[1] ≝
 {
 carr          :> Type[0];
 zeroc         : carr;
 forallc       : (carr → bool) → bool;
 eqc           : carr → carr → bool;
 eqc_to_eq     : ∀x,y.(eqc x y = true) → (x = y);
 eq_to_eqc     : ∀x,y.(x = y) → (eqc x y = true);
 neqc_to_neq   : ∀x,y.(eqc x y = false) → (x ≠ y);
 neq_to_neqc   : ∀x,y.(x ≠ y) → (eqc x y = false);
 decidable_c   : ∀x,y:carr.decidable (x = y);
 symmetric_eqc : symmetricT carr bool eqc
 }.
