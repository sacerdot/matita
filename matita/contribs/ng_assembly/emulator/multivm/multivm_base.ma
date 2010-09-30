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

include "common/theory.ma".
include "emulator/status/status_setter.ma".

ndefinition set_zflb ≝
λm,t.λs:any_status m t.λb.set_z_flag … s (eq_b8 b 〈x0,x0〉).
ndefinition set_zflw ≝
λm,t.λs:any_status m t.λw.set_z_flag … s (eq_w16 w 〈〈x0,x0〉:〈x0,x0〉〉).

ndefinition set_nflb ≝
λm,t.λs:any_status m t.λb.setweak_n_flag … s (getMSB_b8 b).
ndefinition set_nflw ≝
λm,t.λs:any_status m t.λw.setweak_n_flag … s (getMSB_w16 w).

(* enumerazione delle possibili modalita' di sospensione *)
ninductive susp_type : Type ≝
  BGND_MODE: susp_type
| STOP_MODE: susp_type
| WAIT_MODE: susp_type.
