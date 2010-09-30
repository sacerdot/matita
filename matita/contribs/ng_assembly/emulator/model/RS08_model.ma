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

include "emulator/status/status.ma".

(* *********************************** *)
(* IMPOSTAZIONI SPECIFICHE DEI MODELLI *)
(* *********************************** *)

(* modelli di RS08 *)
ninductive RS08_model : Type ≝
  MC9RS08KA1 : RS08_model
| MC9RS08KA2 : RS08_model.

(* memoria dei RS08 *)
ndefinition memory_type_of_FamilyRS08 ≝
λm:RS08_model.match m with
 [ MC9RS08KA1 ⇒
  [
(* 0x0000-0x000E *)   triple … 〈〈〈x0,x0〉:〈x0,x0〉〉.〈〈x0,x0〉:〈x0,x0〉〉〉 〈〈x0,x0〉:〈x0,xF〉〉 MEM_READ_WRITE (* 15B RAM *)
(* 0x0010-0x001E *) ; triple … 〈〈〈x0,x0〉:〈x0,x0〉〉.〈〈x0,x0〉:〈x1,x0〉〉〉 〈〈x0,x0〉:〈x0,xF〉〉 MEM_READ_WRITE (* 15B MEMORY MAPPED IO *)
(* 0x0020-0x004F *) ; triple … 〈〈〈x0,x0〉:〈x0,x0〉〉.〈〈x0,x0〉:〈x2,x0〉〉〉 〈〈x0,x0〉:〈x3,x0〉〉 MEM_READ_WRITE (* 48B RAM *)
(* 0x00C0-0x00FF *) ; triple … 〈〈〈x0,x0〉:〈x0,x0〉〉.〈〈x0,x0〉:〈xC,x0〉〉〉 〈〈x0,x0〉:〈x4,x0〉〉 MEM_READ_WRITE (* 64B RAM PAGING *)
(* 0x0200-0x023F *) ; triple … 〈〈〈x0,x0〉:〈x0,x0〉〉.〈〈x0,x2〉:〈x0,x0〉〉〉 〈〈x0,x0〉:〈x4,x0〉〉 MEM_READ_WRITE (* 64B MEMORY MAPPED IO *)
(* 0x3C00-0x3FFF *) ; triple … 〈〈〈x0,x0〉:〈x0,x0〉〉.〈〈x3,xC〉:〈x0,x0〉〉〉 〈〈x0,x4〉:〈x0,x0〉〉 MEM_READ_ONLY  (* 1024B FLASH *) ]
  | MC9RS08KA2 ⇒
   [ 
(* 0x0000-0x000E *)   triple … 〈〈〈x0,x0〉:〈x0,x0〉〉.〈〈x0,x0〉:〈x0,x0〉〉〉 〈〈x0,x0〉:〈x0,xF〉〉 MEM_READ_WRITE (* 15B RAM *)
(* 0x0010-0x001E *) ; triple … 〈〈〈x0,x0〉:〈x0,x0〉〉.〈〈x0,x0〉:〈x1,x0〉〉〉 〈〈x0,x0〉:〈x0,xF〉〉 MEM_READ_WRITE (* 15B MEMORY MAPPED IO *)
(* 0x0020-0x004F *) ; triple … 〈〈〈x0,x0〉:〈x0,x0〉〉.〈〈x0,x0〉:〈x2,x0〉〉〉 〈〈x0,x0〉:〈x3,x0〉〉 MEM_READ_WRITE (* 48B RAM *)
(* 0x00C0-0x00FF *) ; triple … 〈〈〈x0,x0〉:〈x0,x0〉〉.〈〈x0,x0〉:〈xC,x0〉〉〉 〈〈x0,x0〉:〈x4,x0〉〉 MEM_READ_WRITE (* 64B RAM PAGING *)
(* 0x0200-0x023F *) ; triple … 〈〈〈x0,x0〉:〈x0,x0〉〉.〈〈x0,x2〉:〈x0,x0〉〉〉 〈〈x0,x0〉:〈x4,x0〉〉 MEM_READ_WRITE (* 64B MEMORY MAPPED IO *)
(* 0x3800-0x3FFF *) ; triple … 〈〈〈x0,x0〉:〈x0,x0〉〉.〈〈x3,x8〉:〈x0,x0〉〉〉 〈〈x0,x8〉:〈x0,x0〉〉 MEM_READ_ONLY  (* 2048B FLASH *) ]
  ].

(* parametrizzati i non deterministici rispetto a tutti i valori casuali
   che verranno dati dall'esterno di tipo byte8 (ndby1-2) e bool (ndbo1-5).
   l'ACCENSIONE e' totalmente equivalente ad un reset causato da calo di tensione
   (reset V-low), la memoria ed il check possono essere passati *)
ndefinition start_of_model_RS08 ≝
λmcu:RS08_model.λt:memory_impl.
λmem:aux_mem_type t.λchk:aux_chk_type t.
λndby1,ndby2:byte8.λirqfl,ndbo1,ndbo2,ndbo3,ndbo4,ndbo5:bool.
 (mk_any_status RS08 t
  (mk_alu_RS08
   (* acc_low: reset *)  〈x0,x0〉
   (* pc: reset *) 〈〈x3,xF〉:〈xF,xD〉〉
   (* pcm *) 〈〈x3,xF〉:〈xF,xF〉〉
   (* spc: reset *) 〈〈x3,xF〉:〈xF,xD〉〉
   (* xm: reset *) 〈x0,x0〉
   (* psm: *) 〈x8,x0〉
   (* Z: reset *) false
   (* C: reset *) false)
   (* mem *) mem
   (* chk *) chk
   (* clk: reset *) (None ?)).

(* cio' che non viene resettato mantiene il valore precedente: nella documentazione
   viene riportato come "unaffected"/"indeterminate"/"unpredictable"
   il soft RESET e' diverso da un calo di tensione e la ram non variera' *)
ndefinition reset_of_model_RS08 ≝
λt:memory_impl.λs:any_status RS08 t.
 (mk_any_status RS08 t
  (mk_alu_RS08
   (* acc_low: reset *) 〈x0,x0〉
   (* pc: reset *) 〈〈x3,xF〉:〈xF,xD〉〉
   (* pcm *) (pc_mask_RS08 (alu ? t s))
   (* spc: reset *) 〈〈x3,xF〉:〈xF,xD〉〉
   (* xm: reset *) 〈x0,x0〉
   (* psm: reset *) 〈x8,x0〉
   (* Z: reset *) false
   (* C: reset *) false)
   (* mem: inv. *) (mem_desc ? t s)
   (* chk: inv. *) (chk_desc ? t s)
   (* clk: reset *) (None ?)).
