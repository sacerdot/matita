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

include "emulator/model/HC05_model.ma".
include "emulator/model/HC08_model.ma".
include "emulator/model/HCS08_model.ma".
include "emulator/model/RS08_model.ma".
include "emulator/model/IP2022_model.ma".

(* *********************************** *)
(* IMPOSTAZIONI SPECIFICHE DEI MODELLI *)
(* *********************************** *)

(* raggruppamento dei modelli *)
ndefinition aux_model_type ≝
λm:mcu_type.match m with
 [ HC05   ⇒ HC05_model
 | HC08   ⇒ HC08_model
 | HCS08  ⇒ HCS08_model
 | RS08   ⇒ RS08_model
 | IP2022 ⇒ IP2022_model
 ].

(* ∀modello.descrizione della memoria installata *)
ndefinition memory_type_of_model ≝
λm:mcu_type.
 match m
  return λm.aux_model_type m → ?
 with
 [ HC05   ⇒ memory_type_of_FamilyHC05
 | HC08   ⇒ memory_type_of_FamilyHC08
 | HCS08  ⇒ memory_type_of_FamilyHCS08
 | RS08   ⇒ memory_type_of_FamilyRS08
 | IP2022 ⇒ memory_type_of_FamilyIP2022
 ].

(* dato un modello costruisce un descrittore a partire dalla lista precedente *)
nlet rec build_memory_type_of_model_aux t param (result:aux_chk_type t) on param ≝
 match param with
  [ nil ⇒ result
  | cons hd tl ⇒ 
   build_memory_type_of_model_aux t tl
    (check_update_ranged t result (fst3T ??? hd) (snd3T ??? hd) (thd3T ??? hd)) ].

ndefinition build_memory_type_of_model ≝
λm:mcu_type.λmcu:aux_model_type m.λt:memory_impl.
 build_memory_type_of_model_aux t (memory_type_of_model m mcu) (out_of_bound_memory t).

ndefinition start_of_model ≝
λm:mcu_type.
 match m
  return λm.aux_model_type m → ?
 with
 [ HC05   ⇒ start_of_model_HC05
 | HC08   ⇒ start_of_model_HC08
 | HCS08  ⇒ start_of_model_HCS08
 | RS08   ⇒ start_of_model_RS08
 | IP2022 ⇒ start_of_model_IP2022
 ].

ndefinition reset_of_model ≝
λm:mcu_type.
 match m return λm.Πt.(any_status m t) → ? with
  [ HC05   ⇒ reset_of_model_HC05
  | HC08   ⇒ reset_of_model_HC08
  | HCS08  ⇒ reset_of_model_HCS08
  | RS08   ⇒ reset_of_model_RS08
  | IP2022 ⇒ reset_of_model_IP2022
  ].
