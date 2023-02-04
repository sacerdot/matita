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

include "emulator/memory/memory_struct.ma".
include "num/word32.ma".
include "common/option.ma".
include "common/list.ma".

(* ********************* *)
(* MEMORIA E DESCRITTORE *)
(* ********************* *)

(* (mf_check_update_ranged chk inf sup mode) = setta tipo memoria *)
ndefinition mf_check_update_ranged ≝
λf:word32 → memory_type.λaddr:word32.λrange:word16.λv.
 λx.match inrange_w32 x addr (plus_w32_d_d addr (ext_word32 range)) with
  [ true ⇒ v
  | false ⇒ f x ].

(* tutta la memoria non installata *)
ndefinition mf_out_of_bound_memory ≝ λ_:word32.MEM_OUT_OF_BOUND.

(* (mf_mem_update mem checked addr val) = scrivi controllando il tipo di memoria *)
ndefinition mf_mem_update ≝
λf:word32 → byte8.λc:word32 → memory_type.λa:word32.λv:byte8.
 match c a with
  (* ROM? ok, ma il valore viene perso *)
  [ MEM_READ_ONLY ⇒ Some ? f
  (* RAM? ok *)
  | MEM_READ_WRITE ⇒ Some ? (λx.match eq_w32 x a with [ true ⇒ v | false ⇒ f x ])
  (* NON INSTALLATA? no *)
  | MEM_OUT_OF_BOUND ⇒ None ? ].  

(* tutta la memoria a 0 *)
ndefinition mf_zero_memory ≝ λ_:word32.〈x0,x0〉.

(* (mf_mem_read mem check addr) = leggi controllando il tipo di memoria *)
ndefinition mf_mem_read ≝
λf:word32 → byte8.λc:word32 → memory_type.λa.
 match c a with
  [ MEM_READ_ONLY ⇒ Some ? (f a)
  | MEM_READ_WRITE ⇒ Some ? (f a)
  | MEM_OUT_OF_BOUND ⇒ None ? ].

(* ************************** *)
(* CARICAMENTO PROGRAMMA/DATI *)
(* ************************** *)

(* carica a paratire da addr, overflow se si supera 0xFFFF... *)
nlet rec mf_load_from_source_at (old_mem:word32 → byte8) (src:list byte8) (addr:word32) on src ≝
 match src with
  (* fine di source: carica da old_mem *)
  [ nil ⇒ old_mem
  | cons hd tl ⇒ λx:word32.match eq_w32 addr x with
   (* la locazione corrisponde al punto corrente di source *)
   [ true ⇒ hd
   (* la locazione e' piu' avanti? ricorsione *)
   | false ⇒ (mf_load_from_source_at old_mem tl (succ_w32 addr)) x
   ]
  ].
