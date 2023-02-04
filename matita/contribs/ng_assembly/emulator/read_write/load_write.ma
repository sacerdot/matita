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

include "emulator/read_write/Freescale_load_write.ma".
include "emulator/read_write/IP2022_load_write.ma".

(* ************************************** *)
(* raccordo di tutte le possibili letture *)
(* ************************************** *)

ndefinition multi_mode_loadb ≝
λm.match m
    return λm.Πt.any_status m t → word16 → aux_im_type m →
              option (Prod3T (any_status m t) byte8 word16)
   with
    [ HC05 ⇒ Freescale_multi_mode_load_auxb HC05
    | HC08 ⇒ Freescale_multi_mode_load_auxb HC08
    | HCS08 ⇒ Freescale_multi_mode_load_auxb HCS08
    | RS08 ⇒ Freescale_multi_mode_load_auxb RS08
    | IP2022 ⇒ IP2022_multi_mode_load_auxb
  ].

ndefinition multi_mode_loadw ≝
λm.match m
    return λm.Πt.any_status m t → word16 → aux_im_type m →
                 option (Prod3T (any_status m t) word16 word16)
   with
    [ HC05 ⇒ Freescale_multi_mode_load_auxw HC05
    | HC08 ⇒ Freescale_multi_mode_load_auxw HC08
    | HCS08 ⇒ Freescale_multi_mode_load_auxw HCS08
    | RS08 ⇒ Freescale_multi_mode_load_auxw RS08
    | IP2022 ⇒ IP2022_multi_mode_load_auxw
  ].

(* **************************************** *)
(* raccordo di tutte le possibili scritture *)
(* **************************************** *)

ndefinition multi_mode_writeb ≝
λm.match m
    return λm.Πt.any_status m t → word16 → aux_mod_type → aux_im_type m → byte8 →
              option (ProdT (any_status m t) word16)
   with
    [ HC05 ⇒ Freescale_multi_mode_write_auxb HC05
    | HC08 ⇒ Freescale_multi_mode_write_auxb HC08
    | HCS08 ⇒ Freescale_multi_mode_write_auxb HCS08
    | RS08 ⇒ Freescale_multi_mode_write_auxb RS08
    | IP2022 ⇒ IP2022_multi_mode_write_auxb
  ].

ndefinition multi_mode_writew ≝
λm.match m
    return λm.Πt.any_status m t → word16 → aux_im_type m → word16 →
              option (ProdT (any_status m t) word16)
   with
    [ HC05 ⇒ Freescale_multi_mode_write_auxw HC05
    | HC08 ⇒ Freescale_multi_mode_write_auxw HC08
    | HCS08 ⇒ Freescale_multi_mode_write_auxw HCS08
    | RS08 ⇒ Freescale_multi_mode_write_auxw RS08
    | IP2022 ⇒ IP2022_multi_mode_write_auxw
  ].
