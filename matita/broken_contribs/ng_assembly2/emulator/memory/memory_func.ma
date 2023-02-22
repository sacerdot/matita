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

include "emulator/memory/memory_base.ma".
include "num/word16.ma".
include "common/list.ma".

(* ************************** *)
(* 8 segmenti da 64Kb → 512Kb *)
(* ************************** *)

(* ********************* *)
(* MEMORIA E DESCRITTORE *)
(* ********************* *)

(* (mf_check_update_ranged chk inf sup mode) = setta tipo memoria *)
ndefinition mf_check_update_ranged ≝
λf:oct → word16 → memory_type.λsel:oct.λaddr:word16.λrange:word16.λv.
 λx,y.
 match (eqc ? sel x)⊗(inrangec ? y addr (plusc_d_d ? addr range)) with
  [ true ⇒ v
  | false ⇒ f x y ].

(* tutta la memoria non installata *)
ndefinition mf_out_of_bound_memory ≝ λ_:oct.λ_:word16.MEM_OUT_OF_BOUND.

(* (mf_mem_update mem checked addr val) = scrivi controllando il tipo di memoria *)
ndefinition mf_mem_update ≝
λf:oct → word16 → byte8.λc:oct → word16 → memory_type.λsel:oct.λa:word16.λv:byte8.
 match c sel a with
  (* ROM? ok, ma il valore viene perso *)
  [ MEM_READ_ONLY ⇒ Some ? f
  (* RAM? ok *)
  | MEM_READ_WRITE ⇒ Some ? (λx,y.match (eqc ? sel x)⊗(eqc ? a y) with [ true ⇒ v | false ⇒ f x y ])
  (* NON INSTALLATA? no *)
  | MEM_OUT_OF_BOUND ⇒ None ? ].  

(* tutta la memoria a 0 *)
ndefinition mf_zero_memory ≝ λ_:oct.λ_:word16.〈x0,x0〉.

(* (mf_mem_read mem check addr) = leggi controllando il tipo di memoria *)
ndefinition mf_mem_read ≝
λf:oct → word16 → byte8.λc:oct → word16 → memory_type.λsel:oct.λa:word16.
 match c sel a with
  [ MEM_READ_ONLY ⇒ Some ? (f sel a)
  | MEM_READ_WRITE ⇒ Some ? (f sel a)
  | MEM_OUT_OF_BOUND ⇒ None ? ].

(* ************************** *)
(* CARICAMENTO PROGRAMMA/DATI *)
(* ************************** *)

(* carica a paratire da addr, overflow se si supera 0xFFFF... *)
nlet rec mf_load_from_source_at (old_mem:oct → word16 → byte8) (src:list byte8) (sel:oct) (addr:word16) on src ≝
 match src with
  (* fine di source: carica da old_mem *)
  [ nil ⇒ old_mem
  | cons hd tl ⇒ λx,y.match (eqc ? sel x)⊗(eqc ? addr y) with
   (* la locazione corrisponde al punto corrente di source *)
   [ true ⇒ hd
   (* la locazione e' piu' avanti? ricorsione *)
   | false ⇒ (mf_load_from_source_at old_mem tl sel (succc ? addr)) x y
   ]
  ].
