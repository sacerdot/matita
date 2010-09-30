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

(* modelli di IP2022 *)
ninductive IP2022_model : Type ≝
  IP2K: IP2022_model.

(* memoria degli IP2022 *)
ndefinition memory_type_of_FamilyIP2022 ≝
λm:IP2022_model.match m with
  [ IP2K ⇒
   [
(* 0x02-0x13, 0x7E-0x7F registri memory mapped *)
(* 0x00000002-0x0000007F *)   triple … 〈〈〈x0,x0〉:〈x0,x0〉〉.〈〈x0,x0〉:〈x0,x2〉〉〉 〈〈x0,x0〉:〈x7,xE〉〉 MEM_READ_ONLY  (* 126B SystemMemoryReg *)
(* 0x00000080-0x00000FFF *) ; triple … 〈〈〈x0,x0〉:〈x0,x0〉〉.〈〈x0,x0〉:〈x8,x0〉〉〉 〈〈x0,xF〉:〈x8,x0〉〉 MEM_READ_WRITE (* 3968 UserMemoryReg+RAM+STACK *)
(* 0x02000000-0x02003FFF *) ; triple … 〈〈〈x0,x2〉:〈x0,x0〉〉.〈〈x0,x0〉:〈x0,x0〉〉〉 〈〈x4,x0〉:〈x0,x0〉〉 MEM_READ_WRITE (* 16384B PROGRAM RAM *)
(* 0x02010000-0x02013FFF *) ; triple … 〈〈〈x0,x2〉:〈x0,x1〉〉.〈〈x0,x0〉:〈x0,x0〉〉〉 〈〈x4,x0〉:〈x0,x0〉〉 MEM_READ_ONLY  (* 16384B PROGRAM FLASH *)
(* 0x02014000-0x02017FFF *) ; triple … 〈〈〈x0,x2〉:〈x0,x1〉〉.〈〈x4,x0〉:〈x0,x0〉〉〉 〈〈x4,x0〉:〈x0,x0〉〉 MEM_READ_ONLY  (* 16384B PROGRAM FLASH *)
(* 0x02018000-0x0201BFFF *) ; triple … 〈〈〈x0,x2〉:〈x0,x1〉〉.〈〈x8,x0〉:〈x0,x0〉〉〉 〈〈x4,x0〉:〈x0,x0〉〉 MEM_READ_ONLY  (* 16384B PROGRAM FLASH *)
(* 0x0201C000-0x0201FFFF *) ; triple … 〈〈〈x0,x2〉:〈x0,x1〉〉.〈〈xC,x0〉:〈x0,x0〉〉〉 〈〈x4,x0〉:〈x0,x0〉〉 MEM_READ_ONLY  (* 16384B PROGRAM FLASH *) ]
   (*..*)
  ].

(* punto di riferimento per accessi $FR, ($IP) ($DP) ($SP) *)
ndefinition IP2022_gpr_base ≝ 〈〈〈x0,x0〉:〈x0,x0〉〉.〈〈x0,x0〉:〈x0,x0〉〉〉.
(* punto di riferimento per accessi ($PC) ($ADDR) *)
ndefinition IP2022_ram_base ≝ 〈〈〈x0,x2〉:〈x0,x0〉〉.〈〈x0,x0〉:〈x0,x0〉〉〉.

(* parametrizzati i non deterministici rispetto a tutti i valori casuali
   che verranno dati dall'esterno di tipo byte8 (ndby1-2) e bool (ndbo1-5).
   l'ACCENSIONE e' totalmente equivalente ad un reset causato da calo di tensione
   (reset V-low), la memoria ed il check possono essere passati *)
ndefinition start_of_model_IP2022 ≝
λmcu:IP2022_model.λt:memory_impl.
λmem:aux_mem_type t.λchk:aux_chk_type t.
λndby1,ndby2:byte8.λirqfl,ndbo1,ndbo2,ndbo3,ndbo4,ndbo5:bool.
 (mk_any_status IP2022 t
  (mk_alu_IP2022
   (* acc_low: reset *) 〈x0,x0〉
   (* mulh: reset *) 〈x0,x0〉
   (* addrsel: reset *) 〈x0,x0〉
   (* addr: reset *) new_addrarray
   (* call: reset *) new_callstack
   (* ip: reset *) 〈〈x0,x0〉:〈x0,x0〉〉
   (* dp: reset *) 〈〈x0,x0〉:〈x0,x0〉〉
   (* data: reset *) 〈〈x0,x0〉:〈x0,x0〉〉
   (* sp: reset *) 〈〈x0,x0〉:〈x0,x0〉〉
   (* pc: reset *) 〈〈xF,xF〉:〈xF,x0〉〉
   (* speed: reset *) x3
   (* page: reset *) o7
   (* H: reset *) false
   (* Z: reset *) false
   (* C: reset *) false
   (* skip mode: reset *) false)
   (* mem *) mem
   (* chk *) chk
   (* clk: reset *) (None ?)).

(* cio' che non viene resettato mantiene il valore precedente: nella documentazione
   viene riportato come "unaffected"/"indeterminate"/"unpredictable"
   il soft RESET e' diverso da un calo di tensione e la ram non variera' *)
ndefinition reset_of_model_IP2022 ≝
λt:memory_impl.λs:any_status IP2022 t.
 (mk_any_status IP2022 t
  (mk_alu_IP2022
   (* acc_low: reset *) 〈x0,x0〉
   (* mulh: reset *) 〈x0,x0〉
   (* addrsel: reset *) 〈x0,x0〉
   (* addr: reset *) new_addrarray
   (* call: reset *) new_callstack
   (* ip: reset *) 〈〈x0,x0〉:〈x0,x0〉〉
   (* dp: reset *) 〈〈x0,x0〉:〈x0,x0〉〉
   (* data: reset *) 〈〈x0,x0〉:〈x0,x0〉〉
   (* sp: reset *) 〈〈x0,x0〉:〈x0,x0〉〉
   (* pc: reset *) 〈〈xF,xF〉:〈xF,x0〉〉
   (* speed: reset *) x3
   (* page: reset *) o7
   (* H: reset *) false
   (* Z: reset *) false
   (* C: reset *) false
   (* skip mode: reset *) false)
   (* mem: inv. *) (mem_desc ? t s)
   (* chk: inv. *) (chk_desc ? t s)
   (* clk: reset *) (None ?)).
