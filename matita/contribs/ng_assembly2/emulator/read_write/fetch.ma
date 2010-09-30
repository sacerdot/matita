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

include "emulator/read_write/Freescale_fetch.ma".
include "emulator/read_write/IP2022_fetch.ma".
include "emulator/status/status_getter.ma".

ndefinition fetch ≝
λm,t.λs:any_status m t.
 match m with
  [ HC05 ⇒ fetch_byte
  | HC08 ⇒ Freescale_fetch_byte_or_word
  | HCS08 ⇒ Freescale_fetch_byte_or_word
  | RS08 ⇒ fetch_byte
  | IP2022 ⇒ IP2022_fetch_byte_or_word
  ] m t s (get_pc_reg … s).
