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

include "common/comp.ma".
include "common/prod.ma".

alias symbol "hint_decl" (instance 1) = "hint_decl_Type1".

nrecord comparable_ext : Type[1] ≝
 {
 comp_base     : comparable;
 ltc           : (carr comp_base) → (carr comp_base) → bool;
 lec           : (carr comp_base) → (carr comp_base) → bool;
 gtc           : (carr comp_base) → (carr comp_base) → bool;
 gec           : (carr comp_base) → (carr comp_base) → bool;
 andc          : (carr comp_base) → (carr comp_base) → (carr comp_base);
 orc           : (carr comp_base) → (carr comp_base) → (carr comp_base);
 xorc          : (carr comp_base) → (carr comp_base) → (carr comp_base);
 getMSBc       : (carr comp_base) → bool;
 setMSBc       : (carr comp_base) → (carr comp_base);
 clrMSBc       : (carr comp_base) → (carr comp_base);
 getLSBc       : (carr comp_base) → bool;
 setLSBc       : (carr comp_base) → (carr comp_base);
 clrLSBc       : (carr comp_base) → (carr comp_base);
 rcrc          : bool → (carr comp_base) → ProdT bool (carr comp_base);
 shrc          : (carr comp_base) → ProdT bool (carr comp_base);
 rorc          : (carr comp_base) → (carr comp_base);
 rclc          : bool → (carr comp_base) → ProdT bool (carr comp_base);
 shlc          : (carr comp_base) → ProdT bool (carr comp_base);
 rolc          : (carr comp_base) → (carr comp_base); 
 notc          : (carr comp_base) → (carr comp_base);
 plusc_dc_dc   : bool → (carr comp_base) → (carr comp_base) → ProdT bool (carr comp_base);
 plusc_d_dc    : (carr comp_base) → (carr comp_base) → ProdT bool (carr comp_base);
 plusc_dc_d    : bool → (carr comp_base) → (carr comp_base) → (carr comp_base);
 plusc_d_d     : (carr comp_base) → (carr comp_base) → (carr comp_base);
 plusc_dc_c    : bool → (carr comp_base) → (carr comp_base) → bool;
 plusc_d_c     : (carr comp_base) → (carr comp_base) → bool;
 predc         : (carr comp_base) → (carr comp_base);
 succc         : (carr comp_base) → (carr comp_base);
 complc        : (carr comp_base) → (carr comp_base);
 absc          : (carr comp_base) → (carr comp_base);
 inrangec      : (carr comp_base) → (carr comp_base) → (carr comp_base) → bool
 }.
