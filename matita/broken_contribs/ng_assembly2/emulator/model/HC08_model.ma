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

(* modelli di HC08 *)
ninductive HC08_model : Type ≝
  MC68HC08AB16A: HC08_model
  (*..*). 

(* memoria degli HC08 *)
ndefinition memory_type_of_FamilyHC08 ≝
λm:HC08_model.match m with
 [ MC68HC08AB16A ⇒
  [
(* tutto mappato nel segmento 0 *)
(* 0x0050-0x024F *)   quadruple … o0 〈〈x0,x0〉:〈x5,x0〉〉 〈〈x0,x2〉:〈x0,x0〉〉 MEM_READ_WRITE (* 512B RAM *)
(* 0x0800-0x09FF *) ; quadruple … o0 〈〈x0,x8〉:〈x0,x0〉〉 〈〈x0,x2〉:〈x0,x0〉〉 MEM_READ_ONLY  (* 512B EEPROM *)
(* 0xBE00-0xFDFF *) ; quadruple … o0 〈〈xB,xE〉:〈x0,x0〉〉 〈〈x4,x0〉:〈x0,x0〉〉 MEM_READ_ONLY  (* 16384B ROM *)
(* 0xFE20-0xFF52 *) ; quadruple … o0 〈〈xF,xE〉:〈x2,x0〉〉 〈〈x0,x1〉:〈x3,x3〉〉 MEM_READ_ONLY  (* 307B ROM *)
(* 0xFFD0-0xFFFF *) ; quadruple … o0 〈〈xF,xF〉:〈xD,x0〉〉 〈〈x0,x0〉:〈x3,x0〉〉 MEM_READ_ONLY  (* 48B ROM *) ]
  (* etc... *)
  ].

(* parametrizzati i non deterministici rispetto a tutti i valori casuali
   che verranno dati dall'esterno di tipo byte8 (ndby1-2) e bool (ndbo1-5).
   l'ACCENSIONE e' totalmente equivalente ad un reset causato da calo di tensione
   (reset V-low), la memoria ed il check possono essere passati *)
ndefinition start_of_model_HC08 ≝
λmcu:HC08_model.λt:memory_impl.
λmem:aux_mem_type t.λchk:aux_chk_type t.
λndby1,ndby2:byte8.λirqfl,ndbo1,ndbo2,ndbo3,ndbo4,ndbo5:bool.
 mk_any_status HC08 t
  (mk_alu_HC08
   (* acc_low: ? *) ndby1
   (* indw_low: ? *) ndby2
   (* indx_high: reset *)  〈x0,x0〉
   (* sp: reset *) 〈〈x0,x0〉:〈xF,xF〉〉
   (* pc: reset+fetch *) (mk_word16 (mem_read_abs t mem o0 〈〈xF,xF〉:〈xF,xE〉〉) 
                                    (mem_read_abs t mem o0 〈〈xF,xF〉:〈xF,xF〉〉))
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
ndefinition reset_of_model_HC08 ≝
λt:memory_impl.λs:any_status HC08 t.
 (mk_any_status HC08 t
  (mk_alu_HC08
   (* acc_low: inv. *) (acc_low_reg_HC08 (alu ? t s))
   (* indx_low: inv. *) (indX_low_reg_HC08 (alu ? t s))
   (* indx_high: reset *) 〈x0,x0〉
   (* sp: reset *) 〈〈x0,x0〉:〈xF,xF〉〉
   (* pc: reset+fetch *) (mk_word16 (mem_read_abs t (mem_desc ? t s) o0 〈〈xF,xF〉:〈xF,xE〉〉)
                                    (mem_read_abs t (mem_desc ? t s) o0 〈〈xF,xF〉:〈xF,xE〉〉))
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
