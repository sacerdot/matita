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

include "common/string.ma".
include "compiler/ast_type.ma".

(* ***************** *)
(* GESTIONE AMBIENTE *)
(* ***************** *)

(* elemento: name + const + type *)
nrecord envDsc : Type ≝
 {
 nameDsc: aux_str_type;
 constDsc: bool;
 typeDsc: ast_type
 }.

(* ambiente globale: (ambiente base + ambienti annidati) *)
ninductive env_list : nat → Type ≝
  env_nil: list envDsc → env_list O
| env_cons: ∀n.list envDsc → env_list n → env_list (S n).

ndefinition defined_envList ≝
λd.λl:env_list d.match l with [ env_nil _ ⇒ False | env_cons _ _ _ ⇒ True ].

(* bisogna bypassare la carenza di inversion *)
nlemma defined_envList_S : ∀d.∀l:env_list (S d).defined_envList (S d) l.
 #d; #l;
 ngeneralize in match (refl_eq ? (S d));
 ncases l in ⊢ (? ? % ? → %);
 ##[ ##1: #dsc; #H; ndestruct (*nelim (nat_destruct_0_S … H)*)
 ##| ##2: #n; #dsc; #sub; #H;
          nnormalize;
          napply I
 ##]
nqed.

ndefinition cut_first_envList_aux : Πd.env_list (S d) → env_list d ≝
λd.λl:env_list (S d).
  match l
   return λX.λY:env_list X.defined_envList X Y → env_list (pred X)
  with
   [ env_nil h ⇒ λp:defined_envList O (env_nil h).False_rect_Type0 ? p
   | env_cons n h t ⇒ λp:defined_envList (S n) (env_cons n h t).t
   ] (defined_envList_S d l).
