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

(* modelli di HC05 *)
ninductive HC05_model : Type ≝
  MC68HC05J5A: HC05_model
  (*..*).

(* memoria degli HC05 *)
ndefinition memory_type_of_FamilyHC05 ≝
λm:HC05_model.match m with
 [ MC68HC05J5A ⇒
  [ (* astraggo molto *)
(* 0x0000-0x001F,0x0FF0: sarebbe memory mapped IO *)
(* 0x0080-0x00FF *)   triple … 〈〈〈x0,x0〉:〈x0,x0〉〉.〈〈x0,x0〉:〈x8,x0〉〉〉 〈〈x0,x0〉:〈x8,x0〉〉 MEM_READ_WRITE (* 128B RAM+STACK *)
(* 0x0300-0x0CFF *) ; triple … 〈〈〈x0,x0〉:〈x0,x0〉〉.〈〈x0,x3〉:〈x0,x0〉〉〉 〈〈x0,xA〉:〈x0,x0〉〉 MEM_READ_ONLY  (* 2560B USER ROM *)
(* 0x0E00-0x0FFF *) ; triple … 〈〈〈x0,x0〉:〈x0,x0〉〉.〈〈x0,xE〉:〈x0,x0〉〉〉 〈〈x0,x2〉:〈x0,x0〉〉 MEM_READ_ONLY  (* 512B INTERNAL ROM *) ]
 (* etc.. *)
 ].

(* parametrizzati i non deterministici rispetto a tutti i valori casuali
   che verranno dati dall'esterno di tipo byte8 (ndby1-2) e bool (ndbo1-5).
   l'ACCENSIONE e' totalmente equivalente ad un reset causato da calo di tensione
   (reset V-low), la memoria ed il check possono essere passati *)
ndefinition start_of_model_HC05 ≝
λmcu:HC05_model.λt:memory_impl.
λmem:aux_mem_type t.λchk:aux_chk_type t.
λndby1,ndby2:byte8.λirqfl,ndbo1,ndbo2,ndbo3,ndbo4,ndbo5:bool.
 let build ≝ λspm,spf,pcm:word16.
  mk_any_status HC05 t
   (mk_alu_HC05
    (* acc_low: ? *) ndby1
    (* indx_low: ? *) ndby2 
    (* sp: reset *) (or_w16 (and_w16 〈〈x0,x0〉:〈xF,xF〉〉 spm) spf)
    (* spm *) spm
    (* spf *) spf
    (* pc: reset+fetch *) (and_w16 (mk_word16 (mem_read_abs t mem 〈〈〈x0,x0〉:〈x0,x0〉〉.(and_w16 〈〈xF,xF〉:〈xF,xE〉〉 pcm)〉) 
                                              (mem_read_abs t mem 〈〈〈x0,x0〉:〈x0,x0〉〉.(and_w16 〈〈xF,xF〉:〈xF,xF〉〉 pcm)〉)) pcm)
    (* pcm *) pcm
    (* H: ? *) ndbo1
    (* I: reset *) true
    (* N: ? *) ndbo2
    (* Z: ? *) ndbo3
    (* C: ? *) ndbo4
    (* IRQ: ? *) irqfl)
    (* mem *) mem
    (* chk *) chk
    (* clk: reset *) (None ?) in
 match mcu with
  [ MC68HC05J5A ⇒ build 〈〈x0,x0〉:〈x3,xF〉〉 〈〈x0,x0〉:〈xC,x0〉〉 〈〈x0,xF〉:〈xF,xF〉〉
    (*..*)
  ].

(* cio' che non viene resettato mantiene il valore precedente: nella documentazione
   viene riportato come "unaffected"/"indeterminate"/"unpredictable"
   il soft RESET e' diverso da un calo di tensione e la ram non variera' *)
ndefinition reset_of_model_HC05 ≝
λt:memory_impl.λs:any_status HC05 t.
 (mk_any_status HC05 t
  (mk_alu_HC05
   (* acc_low: inv. *) (acc_low_reg_HC05 (alu ? t s))
   (* indx_low: inv. *) (indX_low_reg_HC05 (alu ? t s))
   (* sp: reset *) (or_w16 (and_w16 〈〈x0,x0〉:〈xF,xF〉〉 (sp_mask_HC05 (alu ? t s)))
                           (sp_fix_HC05 (alu ? t s)))
   (* spm: inv. *) (sp_mask_HC05 (alu ? t s))
   (* spf: inv. *) (sp_fix_HC05 (alu ? t s))
   (* pc: reset+fetch *) (and_w16 (mk_word16 (mem_read_abs t (mem_desc ? t s) 〈〈〈x0,x0〉:〈x0,x0〉〉.(and_w16 〈〈xF,xF〉:〈xF,xE〉〉 (pc_mask_HC05 (alu ? t s)))〉)
                                             (mem_read_abs t (mem_desc ? t s) 〈〈〈x0,x0〉:〈x0,x0〉〉.(and_w16 〈〈xF,xF〉:〈xF,xF〉〉 (pc_mask_HC05 (alu ? t s)))〉))
                                  (pc_mask_HC05 (alu ? t s)))
   (* pcm: inv. *) (pc_mask_HC05 (alu ? t s))
   (* H: inv. *) (h_flag_HC05 (alu ? t s))
   (* I: reset *) true
   (* N: inv. *) (n_flag_HC05 (alu ? t s))
   (* Z: inv. *) (z_flag_HC05 (alu ? t s))
   (* C: inv. *) (c_flag_HC05 (alu ? t s))
   (* IRQ: inv *) (irq_flag_HC05 (alu ? t s)))
   (* mem: inv. *) (mem_desc ? t s)
   (* chk: inv. *) (chk_desc ? t s)
   (* clk: reset *) (None ?)).
