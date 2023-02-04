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
(*                                                                        *)
(* Sviluppato da:                                                         *)
(*   Cosimo Oliboni, oliboni@cs.unibo.it                                  *)
(*                                                                        *)
(* ********************************************************************** *)

include "compiler/env_to_flatenv.ma".
include "compiler/astfe_tree.ma".

(* ************************************************ *)
(* SUCCESSIONE APPIATITA DI ASSEGNAMENTI SU FLATENV *)
(* ************************************************ *)

inductive jumpNLabel : Type ≝
  N_LABEL: nat → jumpNLabel.

inductive jumpLabel : Type ≝
  LABEL_N: jumpNLabel → jumpLabel
| LABEL_END: jumpLabel.

(* 
   L1 := goto L1
   EXPR L1 L2 := if(EXPR) then { goto L1; } else { goto L2; }
*)
inductive jumpBlock (e:aux_flatEnv_type) : Type ≝
  JUMPBLOCK_ABS: jumpLabel → jumpBlock e
| JUMPBLOCK_COND: astfe_base_expr e → jumpLabel → jumpLabel → jumpBlock e.

inductive linearfe_stm (e:aux_flatEnv_type) : Type ≝
  LINEARFE_STM_ASG: ∀t:ast_type.
                    astfe_var e false t → astfe_expr e t → linearfe_stm e
| LINEARFE_STM_INIT: ∀b:bool.∀t:ast_type.
                     astfe_id e b t → astfe_init e t → linearfe_stm e.

(* LABEL + [ init/assegnamenti ] + if(EXPR) then { goto LABEL; } else { goto LABEL; } *)
inductive linearfe_elem (e:aux_flatEnv_type) : Type ≝
 LINEARFE_ELEM: jumpNLabel → list (linearfe_stm e) → jumpBlock e → linearfe_elem e.

(* -------------------------- *)

definition linearfe_prog ≝ λe.list (linearfe_elem e).

(* -------------------------- *)

(* programma vuoto *)
definition empty_linearfe_prog ≝ nil (linearfe_elem empty_flatEnv).
