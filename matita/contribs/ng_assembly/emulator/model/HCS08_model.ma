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

(* modelli di HCS08 *)
ninductive HCS08_model : Type ≝
  MC9S08AW60 : HCS08_model
| MC9S08GB60 : HCS08_model
  (*..*).

(* memoria degli HCS08 *)
ndefinition memory_type_of_FamilyHCS08 ≝
λm:HCS08_model.match m with
 [ MC9S08AW60 ⇒
  [  (* astraggo molto *)
(* 0x0000-0x006F,0x1800-0x185F: sarebbe memory mapped IO *)
(* 0x0070-0x086F *)   triple … 〈〈〈x0,x0〉:〈x0,x0〉〉.〈〈x0,x0〉:〈x7,x0〉〉〉 〈〈x0,x8〉:〈x0,x0〉〉 MEM_READ_WRITE (* 2048B RAM *)
(* 0x0870-0x17FF *) ; triple … 〈〈〈x0,x0〉:〈x0,x0〉〉.〈〈x0,x8〉:〈x7,x0〉〉〉 〈〈x0,xF〉:〈x9,x0〉〉 MEM_READ_ONLY  (* 3984B FLASH *)
(* 0x1860-0xFFFF *) ; triple … 〈〈〈x0,x0〉:〈x0,x0〉〉.〈〈x1,x8〉:〈x6,x0〉〉〉 〈〈xE,x7〉:〈xA,x0〉〉 MEM_READ_ONLY  (* 59296B FLASH *) ]
 | MC9S08GB60 ⇒
  [  (* astraggo molto *)
(* 0x0000-0x006F,0x1800-0x185F: sarebbe memory mapped IO *)
(* 0x0080-0x107F *)   triple … 〈〈〈x0,x0〉:〈x0,x0〉〉.〈〈x0,x0〉:〈x8,x0〉〉〉 〈〈x1,x0〉:〈x0,x0〉〉 MEM_READ_WRITE (* 4096B RAM *)
(* 0x1080-0x17FF *) ; triple … 〈〈〈x0,x0〉:〈x0,x0〉〉.〈〈x1,x0〉:〈x8,x0〉〉〉 〈〈x0,x7〉:〈x8,x0〉〉 MEM_READ_ONLY  (* 1920B FLASH *)
(* 0x182C-0xFFFF *) ; triple … 〈〈〈x0,x0〉:〈x0,x0〉〉.〈〈x1,x8〉:〈x2,xC〉〉〉 〈〈xE,x7〉:〈xD,x4〉〉 MEM_READ_ONLY  (* 59348B FLASH *) ]
 (* etc... *)
 ].

(* parametrizzati i non deterministici rispetto a tutti i valori casuali
   che verranno dati dall'esterno di tipo byte8 (ndby1-2) e bool (ndbo1-5).
   l'ACCENSIONE e' totalmente equivalente ad un reset causato da calo di tensione
   (reset V-low), la memoria ed il check possono essere passati *)
ndefinition start_of_model_HCS08 ≝
λmcu:HCS08_model.λt:memory_impl.
λmem:aux_mem_type t.λchk:aux_chk_type t.
λndby1,ndby2:byte8.λirqfl,ndbo1,ndbo2,ndbo3,ndbo4,ndbo5:bool.
 mk_any_status HCS08 t
  (mk_alu_HC08
   (* acc_low: ? *) ndby1
   (* indw_low: ? *) ndby2
   (* indx_high: reset *)  〈x0,x0〉
   (* sp: reset *) 〈〈x0,x0〉:〈xF,xF〉〉
   (* pc: reset+fetch *) (mk_word16 (mem_read_abs t mem 〈〈〈x0,x0〉:〈x0,x0〉〉.〈〈xF,xF〉:〈xF,xE〉〉〉) 
                                    (mem_read_abs t mem 〈〈〈x0,x0〉:〈x0,x0〉〉.〈〈xF,xF〉:〈xF,xF〉〉〉))
   (* V: ? *) ndbo1
   (* H: ? *) ndbo2
   (* I: reset *) true
   (* N: ? *) ndbo3
   (* Z: ? *) ndbo4
   (* C: ? *) ndbo5
   (* IRQ: ? *) irqfl)
   (* mem *) mem
   (* chk *) chk
   (* clk: reset *) (None ?).

(* cio' che non viene resettato mantiene il valore precedente: nella documentazione
   viene riportato come "unaffected"/"indeterminate"/"unpredictable"
   il soft RESET e' diverso da un calo di tensione e la ram non variera' *)
ndefinition reset_of_model_HCS08 ≝
λt:memory_impl.λs:any_status HCS08 t.
 (mk_any_status HCS08 t
  (mk_alu_HC08
   (* acc_low: inv. *) (acc_low_reg_HC08 (alu ? t s))
   (* indx_low: inv. *) (indX_low_reg_HC08 (alu ? t s))
   (* indx_high: reset *) 〈x0,x0〉
   (* sp: reset *) 〈〈x0,x0〉:〈xF,xF〉〉
   (* pc: reset+fetch *) (mk_word16 (mem_read_abs t (mem_desc ? t s) 〈〈〈x0,x0〉:〈x0,x0〉〉.〈〈xF,xF〉:〈xF,xE〉〉〉)
                                    (mem_read_abs t (mem_desc ? t s) 〈〈〈x0,x0〉:〈x0,x0〉〉.〈〈xF,xF〉:〈xF,xE〉〉〉))
   (* V: inv. *) (v_flag_HC08 (alu ? t s))
   (* H: inv. *) (h_flag_HC08 (alu ? t s))
   (* I: reset *) true
   (* N: inv. *) (n_flag_HC08 (alu ? t s))
   (* Z: inv. *) (z_flag_HC08 (alu ? t s))
   (* C: inv. *) (c_flag_HC08 (alu ? t s))
   (* IRQ: inv *) (irq_flag_HC08 (alu ? t s)))
   (* mem: inv. *) (mem_desc ? t s)
   (* chk: inv. *) (chk_desc ? t s)
   (* clk: reset *) (None ?)).
