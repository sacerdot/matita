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
(*                           Progetto FreeScale                           *)
(*                                                                        *)
(* Sviluppato da:                                                         *)
(*   Cosimo Oliboni, oliboni@cs.unibo.it                                  *)
(*                                                                        *)
(* Questo materiale fa parte della tesi:                                  *)
(*   "Formalizzazione Interattiva dei Microcontroller a 8bit FreeScale"   *)
(*                                                                        *)
(*                    data ultima modifica 15/11/2007                     *)
(* ********************************************************************** *)

include "freescale/memory_abs.ma".

(* *********************************** *)
(* STATUS INTERNO DEL PROCESSORE (ALU) *)
(* *********************************** *)

(* ALU dell'HC05 *)
record alu_HC05: Type ≝
 {
 (* A: registo accumulatore *)
 acc_low_reg_HC05 : byte8;
 (* X: registro indice *)
 indX_low_reg_HC05 : byte8;
 (* SP: registo stack pointer *)
 sp_reg_HC05 : word16;
 (* modificatori di SP: per esempio e' definito come 0000000011xxxxxxb *)
 (* la logica della sua costruzione e' quindi (SP∧mask)∨fix *)
 (* totalmente racchiusa nella ALU, bastera' fare get(set(SP)) *)
 sp_mask_HC05 : word16;
 sp_fix_HC05 : word16;
 (* PC: registro program counter *)
 pc_reg_HC05 : word16;
 (* modificatore di PC: per esempio e' definito come 00xxxxxxxxxxxxxxb *)
 (* la logica della sua costruzione e' quindi (PC∧mask) *)
 (* totalmente racchiusa nella ALU, bastera' fare get(set(PC)) *)
 pc_mask_HC05 : word16;
 
 (* H: flag semi-carry (somma nibble basso) *)
 h_flag_HC05 : bool;
 (* I: flag mascheramento degli interrupt mascherabili: 1=mascherati *)
 i_flag_HC05 : bool;
 (* N: flag segno/negativita' *)
 n_flag_HC05 : bool;
 (* Z: flag zero *)
 z_flag_HC05 : bool;
 (* C: flag carry *)
 c_flag_HC05 : bool;
 
 (* IRQ: flag che simula il pin esterno IRQ *)
 irq_flag_HC05 : bool
 }.

notation "{hvbox('A_Reg' ≝ acclow ; break 'X_Reg' ≝ indxlow ; break 'Sp_Reg' ≝ sp ; break 'Sp_Mask' ≝ spm ; break 'Sp_Fix' ≝ spf ; break 'Pc_Reg' ≝ pc ; break 'Pc_Mask' ≝ pcm ; break 'H_Flag' ≝ hfl ; break 'I_Flag' ≝ ifl ; break 'N_Flag' ≝ nfl ; break 'Z_Flag' ≝ zfl ; break 'C_Flag' ≝ cfl ; break 'IRQ_Flag' ≝ irqfl)}"
 non associative with precedence 80 for
 @{ 'mk_alu_HC05 $acclow $indxlow $sp $spm $spf $pc $pcm $hfl $ifl $nfl $zfl $cfl $irqfl }.
interpretation "mk_alu_HC05" 'mk_alu_HC05 acclow indxlow sp spm spf pc pcm hfl ifl nfl zfl cfl irqfl =
 (mk_alu_HC05 acclow indxlow sp spm spf pc pcm hfl ifl nfl zfl cfl irqfl).
 
(* ALU dell'HC08/HCS08 *) 
record alu_HC08: Type ≝
 {
 (* A: registo accumulatore *)
 acc_low_reg_HC08 : byte8;
 (* X: registro indice parte bassa *)
 indX_low_reg_HC08 : byte8;
 (* H: registro indice parte alta *)
 indX_high_reg_HC08 : byte8;
 (* SP: registo stack pointer *)
 sp_reg_HC08 : word16;
 (* PC: registro program counter *)
 pc_reg_HC08 : word16;
 
 (* V: flag overflow *)
 v_flag_HC08 : bool;
 (* H: flag semi-carry (somma nibble basso) *)
 h_flag_HC08 : bool;
 (* I: flag mascheramento degli interrupt mascherabili: 1=mascherati *)
 i_flag_HC08 : bool;
 (* N: flag segno/negativita' *)
 n_flag_HC08 : bool;
 (* Z: flag zero *)
 z_flag_HC08 : bool;
 (* C: flag carry *)
 c_flag_HC08 : bool;
 
 (* IRQ: flag che simula il pin esterno IRQ *)
 irq_flag_HC08 : bool
 }.

notation "{hvbox('A_Reg' ≝ acclow ; break 'X_Reg' ≝ indxlow ; break 'H_Reg' ≝ indxhigh ; break 'Sp_Reg' ≝ sp ; break 'Pc_Reg' ≝ pc ; break 'V_Flag' ≝ vfl ; break 'H_Flag' ≝ hfl ; break 'I_Flag' ≝ ifl ; break 'N_Flag' ≝ nfl ; break 'Z_Flag' ≝ zfl ; break 'C_Flag' ≝ cfl ; break 'IRQ_Flag' ≝ irqfl)}"
 non associative with precedence 80 for
 @{ 'mk_alu_HC08 $acclow $indxlow $indxhigh $sp $pc $vfl $hfl $ifl $nfl $zfl $cfl $irqfl }.
interpretation "mk_alu_HC08" 'mk_alu_HC08 acclow indxlow indxhigh sp pc vfl hfl ifl nfl zfl cfl irqfl =
 (mk_alu_HC08 acclow indxlow indxhigh sp pc vfl hfl ifl nfl zfl cfl irqfl).

(* ALU dell'RS08 *)
record alu_RS08: Type ≝
 {
 (* A: registo accumulatore *)
 acc_low_reg_RS08 : byte8;
 (* PC: registro program counter *)
 pc_reg_RS08 : word16;
 (* modificatore di PC: per esempio e' definito come 00xxxxxxxxxxxxxxb *)
 (* la logica della sua costruzione e' quindi (PC∧mask) *)
 (* totalmente racchiusa nella ALU, bastera' fare get(set(PC)) *)
 pc_mask_RS08 : word16;
 (* SPC: registro shadow program counter *)
 (* NB: il suo modificatore e' lo stesso di PC *)
 spc_reg_RS08 : word16;

 (* X: registro indice parte bassa *)
 (* NB: in realta' e' mappato in memoria e non risiede nella ALU *)
 (* la lettura/scrittura avviene tramite la locazione [0x000F] *)
 (* la funzione memory_filter_read/write si occupera' di intercettare *)
 (* e deviare sul registro le letture/scritture (modulo load_write) *)
 x_map_RS08 : byte8;
 (* PS: registro selezione di pagina *)
 (* serve a indirizzare la finestra RAM di 64b [0x00C0-0x00FF] *)
 (* su tutta la memoria installata [0x0000-0x3FFF]: [00pp pppp ppxx xxxx] *)
 (* NB: in realta' e' mappato in memoria e non risiede nella ALU *)
 (* la lettura/scrittura avviene tramite la locazione [0x001F] *)
 (* la funzione memory_filter_read/write si occupera' di intercettare *)
 (* e deviare sul registro le letture/scritture (modulo load_write) *)
 ps_map_RS08 : byte8;
 
 (* Z: flag zero *)
 z_flag_RS08 : bool;
 (* C: flag carry *)
 c_flag_RS08 : bool
 }.

notation "{hvbox('A_Reg' ≝ acclow ; break 'Pc_Reg' ≝ pc ; break 'Pc_Mask' ≝ pcm ; break 'Spc_Reg' ≝ spc ; break 'X_Map' ≝ xm ; break 'Ps_Map' ≝ psm ; break 'Z_Flag' ≝ zfl ; break 'C_Flag' ≝ cfl)}"
 non associative with precedence 80 for
 @{ 'mk_alu_RS08 $acclow $pc $pcm $spc $xm $psm $zfl $cfl }.
interpretation "mk_alu_RS08" 'mk_alu_RS08 acclow pc pcm spc xm psm zfl cfl =
 (mk_alu_RS08 acclow pc pcm spc xm psm zfl cfl).

(* tipo processore dipendente dalla mcu, varia solo la ALU *)
record any_status (mcu:mcu_type) (t:memory_impl): Type ≝
 {
 alu : match mcu with
  [ HC05 ⇒ alu_HC05 | HC08 ⇒ alu_HC08 | HCS08 ⇒ alu_HC08 | RS08 ⇒ alu_RS08 ];

 (* descritore della memoria *)
 mem_desc : aux_mem_type t;
 (* descrittore del tipo di memoria installata *)
 chk_desc : aux_chk_type t;
 (* descrittore del click = stato di avanzamento dell'esecuzione+cur_pc conseguente a fetch *)
 (* 1) None = istruzione eseguita, attesa del fetch *)
 (* 2) Some cur_clk,pseudo,mode,clks,cur_pc = fetch eseguito, countup a esecuzione *) 
 clk_desc : option (Prod5T byte8 (any_opcode mcu) (instr_mode) byte8 word16)
 }.

(* evitare di mostrare la memoria/descrittore che impalla il visualizzatore *)
notation > "{hvbox('Alu' ≝ alu ; break 'Clk' ≝ clk)}" non associative with precedence 80 
 for @{ 'mk_any_status $alu $mem $chk $clk }.
interpretation "mk_any_status" 'mk_any_status alu mem chk clk =
 (mk_any_status alu mem chk clk).

(* **************** *)
(* GETTER SPECIFICI *)
(* **************** *)

(* funzione ausiliaria per il tipaggio dei getter *)
definition aux_get_typing ≝ λx:Type.λm:mcu_type.match m with
 [ HC05 ⇒ alu_HC05 | HC08 ⇒ alu_HC08 | HCS08 ⇒ alu_HC08 | RS08 ⇒ alu_RS08 ] → x.

(* REGISTRI *)

(* getter di A, esiste sempre *)
definition get_acc_8_low_reg ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.
 match m
  return aux_get_typing byte8 with
 [ HC05 ⇒ acc_low_reg_HC05
 | HC08 ⇒ acc_low_reg_HC08
 | HCS08 ⇒ acc_low_reg_HC08
 | RS08 ⇒ acc_low_reg_RS08 ]
 (alu m t s).

(* getter di X, non esiste sempre *)
definition get_indX_8_low_reg ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.
 match m
  return aux_get_typing (option byte8) with 
 [ HC05 ⇒ λalu.Some ? (indX_low_reg_HC05 alu)
 | HC08 ⇒ λalu.Some ? (indX_low_reg_HC08 alu)
 | HCS08 ⇒ λalu.Some ? (indX_low_reg_HC08 alu)
 | RS08 ⇒ λalu.None ? ]
 (alu m t s).

(* getter di H, non esiste sempre *)
definition get_indX_8_high_reg ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.
 match m
  return aux_get_typing (option byte8) with 
 [ HC05 ⇒ λalu.None ?
 | HC08 ⇒ λalu.Some ? (indX_high_reg_HC08 alu)
 | HCS08 ⇒ λalu.Some ? (indX_high_reg_HC08 alu)
 | RS08 ⇒ λalu.None ? ]
 (alu m t s).

(* getter di H:X, non esiste sempre *)
definition get_indX_16_reg ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.
 match m
  return aux_get_typing (option word16) with 
 [ HC05 ⇒ λalu.None ?
 | HC08 ⇒ λalu.Some ? (mk_word16 (indX_high_reg_HC08 alu) (indX_low_reg_HC08 alu))
 | HCS08 ⇒ λalu.Some ? (mk_word16 (indX_high_reg_HC08 alu) (indX_low_reg_HC08 alu))
 | RS08 ⇒ λalu.None ? ]
 (alu m t s).

(* getter di SP, non esiste sempre *)
definition get_sp_reg ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.
 match m
  return aux_get_typing (option word16) with 
 [ HC05 ⇒ λalu.Some ? (sp_reg_HC05 alu)
 | HC08 ⇒ λalu.Some ? (sp_reg_HC08 alu)
 | HCS08 ⇒ λalu.Some ? (sp_reg_HC08 alu)
 | RS08 ⇒ λalu.None ? ]
 (alu m t s).

(* getter di PC, esiste sempre *)
definition get_pc_reg ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.
 match m
  return aux_get_typing word16 with 
 [ HC05 ⇒ pc_reg_HC05
 | HC08 ⇒ pc_reg_HC08
 | HCS08 ⇒ pc_reg_HC08
 | RS08 ⇒ pc_reg_RS08 ]
 (alu m t s).

(* getter di SPC, non esiste sempre *)
definition get_spc_reg ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.
 match m
  return aux_get_typing (option word16) with 
 [ HC05 ⇒ λalu.None ?
 | HC08 ⇒ λalu.None ?
 | HCS08 ⇒ λalu.None ?
 | RS08 ⇒ λalu.Some ? (spc_reg_RS08 alu) ]
 (alu m t s).

(* REGISTRI MEMORY MAPPED *)

(* getter di memory mapped X, non esiste sempre *)
definition get_x_map ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.
 match m
  return aux_get_typing (option byte8) with 
 [ HC05 ⇒ λalu.None ?
 | HC08 ⇒ λalu.None ?
 | HCS08 ⇒ λalu.None ?
 | RS08 ⇒ λalu.Some ? (x_map_RS08 alu) ]
 (alu m t s).

(* getter di memory mapped PS, non esiste sempre *)
definition get_ps_map ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.
 match m
  return aux_get_typing (option byte8) with 
 [ HC05 ⇒ λalu.None ?
 | HC08 ⇒ λalu.None ?
 | HCS08 ⇒ λalu.None ?
 | RS08 ⇒ λalu.Some ? (ps_map_RS08 alu) ]
 (alu m t s).

(* FLAG *)

(* getter di V, non esiste sempre *)
definition get_v_flag ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.
 match m
  return aux_get_typing (option bool) with 
 [ HC05 ⇒ λalu.None ?
 | HC08 ⇒ λalu.Some ? (v_flag_HC08 alu)
 | HCS08 ⇒ λalu.Some ? (v_flag_HC08 alu)
 | RS08 ⇒ λalu.None ? ]
 (alu m t s).

(* getter di H, non esiste sempre *)
definition get_h_flag ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.
 match m
  return aux_get_typing (option bool) with 
 [ HC05 ⇒ λalu.Some ? (h_flag_HC05 alu)
 | HC08 ⇒ λalu.Some ? (h_flag_HC08 alu)
 | HCS08 ⇒ λalu.Some ? (h_flag_HC08 alu)
 | RS08 ⇒ λalu.None ? ]
 (alu m t s).

(* getter di I, non esiste sempre *)
definition get_i_flag ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.
 match m
  return aux_get_typing (option bool) with 
 [ HC05 ⇒ λalu.Some ? (i_flag_HC05 alu)
 | HC08 ⇒ λalu.Some ? (i_flag_HC08 alu)
 | HCS08 ⇒ λalu.Some ? (i_flag_HC08 alu)
 | RS08 ⇒ λalu.None ? ]
 (alu m t s).

(* getter di N, non esiste sempre *)
definition get_n_flag ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.
 match m
  return aux_get_typing (option bool) with 
 [ HC05 ⇒ λalu.Some ? (n_flag_HC05 alu)
 | HC08 ⇒ λalu.Some ? (n_flag_HC08 alu)
 | HCS08 ⇒ λalu.Some ? (n_flag_HC08 alu)
 | RS08 ⇒ λalu.None ? ]
 (alu m t s).

(* getter di Z, esiste sempre *)
definition get_z_flag ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.
 match m
  return aux_get_typing bool with 
 [ HC05 ⇒ z_flag_HC05
 | HC08 ⇒ z_flag_HC08
 | HCS08 ⇒ z_flag_HC08
 | RS08 ⇒ z_flag_RS08 ]
 (alu m t s).

(* getter di C, esiste sempre *)
definition get_c_flag ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.
 match m
  return aux_get_typing bool with 
 [ HC05 ⇒ c_flag_HC05
 | HC08 ⇒ c_flag_HC08
 | HCS08 ⇒ c_flag_HC08
 | RS08 ⇒ c_flag_RS08 ]
 (alu m t s).

(* getter di IRQ, non esiste sempre *)
definition get_irq_flag ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.
 match m
  return aux_get_typing (option bool) with 
 [ HC05 ⇒ λalu.Some ? (irq_flag_HC05 alu)
 | HC08 ⇒ λalu.Some ? (irq_flag_HC08 alu)
 | HCS08 ⇒ λalu.Some ? (irq_flag_HC08 alu)
 | RS08 ⇒ λalu.None ? ]
 (alu m t s).

(* DESCRITTORI ESTERNI ALLA ALU *)

(* getter della ALU, esiste sempre *)
definition get_alu ≝ λm:mcu_type.λt:memory_impl.λs:any_status m t.alu m t s.

(* getter della memoria, esiste sempre *)
definition get_mem_desc ≝ λm:mcu_type.λt:memory_impl.λs:any_status m t.mem_desc m t s.

(* getter del descrittore, esiste sempre *)
definition get_chk_desc ≝ λm:mcu_type.λt:memory_impl.λs:any_status m t.chk_desc m t s.

(* getter del clik, esiste sempre *)
definition get_clk_desc ≝ λm:mcu_type.λt:memory_impl.λs:any_status m t.clk_desc m t s.

(* ***************************** *)
(* SETTER SPECIFICI FORTI/DEBOLI *)
(* ***************************** *)

(* funzione ausiliaria per il tipaggio dei setter forti *)
definition aux_set_typing ≝ λx:Type.λm:mcu_type.
  match m with [ HC05 ⇒ alu_HC05 | HC08 ⇒ alu_HC08 | HCS08 ⇒ alu_HC08 | RS08 ⇒ alu_RS08 ]
  → x →
  match m with [ HC05 ⇒ alu_HC05 | HC08 ⇒ alu_HC08 | HCS08 ⇒ alu_HC08 | RS08 ⇒ alu_RS08 ].

(* funzione ausiliaria per il tipaggio dei setter deboli *)
definition aux_set_typing_opt ≝ λx:Type.λm:mcu_type.option
 (match m with [ HC05 ⇒ alu_HC05 | HC08 ⇒ alu_HC08 | HCS08 ⇒ alu_HC08 | RS08 ⇒ alu_RS08 ]
  → x →
  match m with [ HC05 ⇒ alu_HC05 | HC08 ⇒ alu_HC08 | HCS08 ⇒ alu_HC08 | RS08 ⇒ alu_RS08 ]).

(* DESCRITTORI ESTERNI ALLA ALU *)

(* setter forte della ALU *)
definition set_alu ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λalu'.
 mk_any_status m t alu' (get_mem_desc m t s) (get_chk_desc m t s) (get_clk_desc m t s).

(* setter forte della memoria *)
definition set_mem_desc ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λmem':aux_mem_type t.
 mk_any_status m t (get_alu m t s) mem' (get_chk_desc m t s) (get_clk_desc m t s).

(* setter forte del descrittore *)
definition set_chk_desc ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λchk':aux_chk_type t.
 mk_any_status m t (get_alu m t s) (get_mem_desc m t s) chk' (get_clk_desc m t s).

(* setter forte del clik *)
definition set_clk_desc ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.
λclk':option (Prod5T byte8 (any_opcode m) (instr_mode) byte8 word16).
 mk_any_status m t (get_alu m t s) (get_mem_desc m t s) (get_chk_desc m t s) clk'.

(* REGISTRO A *)

(* setter specifico HC05 di A *)
definition set_acc_8_low_reg_HC05 ≝
λalu.λacclow':byte8.
 mk_alu_HC05
  acclow'
  (indX_low_reg_HC05 alu)
  (sp_reg_HC05 alu)
  (sp_mask_HC05 alu)
  (sp_fix_HC05 alu)
  (pc_reg_HC05 alu)
  (pc_mask_HC05 alu)
  (h_flag_HC05 alu)
  (i_flag_HC05 alu)
  (n_flag_HC05 alu)
  (z_flag_HC05 alu)
  (c_flag_HC05 alu)
  (irq_flag_HC05 alu).

(* setter specifico HC08/HCS08 di A *)
definition set_acc_8_low_reg_HC08 ≝
λalu.λacclow':byte8.
 mk_alu_HC08
  acclow'
  (indX_low_reg_HC08 alu)
  (indX_high_reg_HC08 alu)
  (sp_reg_HC08 alu)
  (pc_reg_HC08 alu)
  (v_flag_HC08 alu)
  (h_flag_HC08 alu)
  (i_flag_HC08 alu)
  (n_flag_HC08 alu)
  (z_flag_HC08 alu)
  (c_flag_HC08 alu)
  (irq_flag_HC08 alu).

(* setter specifico RS08 di A *)
definition set_acc_8_low_reg_RS08 ≝ 
λalu.λacclow':byte8.
 mk_alu_RS08
  acclow'
  (pc_reg_RS08 alu)
  (pc_mask_RS08 alu)
  (spc_reg_RS08 alu)
  (x_map_RS08 alu)
  (ps_map_RS08 alu)
  (z_flag_RS08 alu)
  (c_flag_RS08 alu).

(* setter forte di A *)
definition set_acc_8_low_reg ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λacclow':byte8.
 set_alu m t s 
 (match m return aux_set_typing byte8 with
  [ HC05 ⇒ set_acc_8_low_reg_HC05
  | HC08 ⇒ set_acc_8_low_reg_HC08
  | HCS08 ⇒ set_acc_8_low_reg_HC08
  | RS08 ⇒ set_acc_8_low_reg_RS08
  ] (alu m t s) acclow').

(* REGISTRO X *)

(* setter specifico HC05 di X *)
definition set_indX_8_low_reg_HC05 ≝
λalu.λindxlow':byte8.
 mk_alu_HC05
  (acc_low_reg_HC05 alu)
  indxlow'
  (sp_reg_HC05 alu)
  (sp_mask_HC05 alu)
  (sp_fix_HC05 alu)
  (pc_reg_HC05 alu)
  (pc_mask_HC05 alu)
  (h_flag_HC05 alu)
  (i_flag_HC05 alu)
  (n_flag_HC05 alu)
  (z_flag_HC05 alu)
  (c_flag_HC05 alu)
  (irq_flag_HC05 alu).

(* setter specifico HC08/HCS08 di X *)
definition set_indX_8_low_reg_HC08 ≝
λalu.λindxlow':byte8.
 mk_alu_HC08
  (acc_low_reg_HC08 alu)
  indxlow'
  (indX_high_reg_HC08 alu)
  (sp_reg_HC08 alu)
  (pc_reg_HC08 alu)
  (v_flag_HC08 alu)
  (h_flag_HC08 alu)
  (i_flag_HC08 alu)
  (n_flag_HC08 alu)
  (z_flag_HC08 alu)
  (c_flag_HC08 alu)
  (irq_flag_HC08 alu).

(* setter forte di X *)
definition set_indX_8_low_reg ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λindxlow':byte8.
 opt_map ?? (match m return aux_set_typing_opt byte8 with
             [ HC05 ⇒ Some ? set_indX_8_low_reg_HC05
             | HC08 ⇒ Some ? set_indX_8_low_reg_HC08
             | HCS08 ⇒ Some ? set_indX_8_low_reg_HC08
             | RS08 ⇒ None ? ])
 (λf.Some ? (set_alu m t s (f (alu m t s) indxlow'))).

(* setter debole di X *)
definition setweak_indX_8_low_reg ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λindxlow':byte8.
 match set_indX_8_low_reg m t s indxlow' with
  [ None ⇒ s | Some s' ⇒ s' ].

(* REGISTRO H *)

(* setter specifico HC08/HCS08 di H *)
definition set_indX_8_high_reg_HC08 ≝
λalu.λindxhigh':byte8.
 mk_alu_HC08
  (acc_low_reg_HC08 alu)
  (indX_low_reg_HC08 alu)
  indxhigh'
  (sp_reg_HC08 alu)
  (pc_reg_HC08 alu)
  (v_flag_HC08 alu)
  (h_flag_HC08 alu)
  (i_flag_HC08 alu)
  (n_flag_HC08 alu)
  (z_flag_HC08 alu)
  (c_flag_HC08 alu)
  (irq_flag_HC08 alu).

(* setter forte di H *)
definition set_indX_8_high_reg ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λindxhigh':byte8.
 opt_map ?? (match m return aux_set_typing_opt byte8 with
             [ HC05 ⇒ None ?
             | HC08 ⇒ Some ? set_indX_8_high_reg_HC08
             | HCS08 ⇒ Some ? set_indX_8_high_reg_HC08
             | RS08 ⇒ None ? ])
 (λf.Some ? (set_alu m t s (f (alu m t s) indxhigh'))).

(* setter debole di H *)
definition setweak_indX_8_high_reg ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λindxhigh':byte8.
 match set_indX_8_high_reg m t s indxhigh' with
  [ None ⇒ s | Some s' ⇒ s' ].

(* REGISTRO H:X *)

(* setter specifico HC08/HCS08 di H:X *)
definition set_indX_16_reg_HC08 ≝
λalu.λindx16:word16.
 mk_alu_HC08
  (acc_low_reg_HC08 alu)
  (w16l indx16)
  (w16h indx16)
  (sp_reg_HC08 alu)
  (pc_reg_HC08 alu)
  (v_flag_HC08 alu)
  (h_flag_HC08 alu)
  (i_flag_HC08 alu)
  (n_flag_HC08 alu)
  (z_flag_HC08 alu)
  (c_flag_HC08 alu)
  (irq_flag_HC08 alu).

(* setter forte di H:X *)
definition set_indX_16_reg ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λindx16:word16.
 opt_map ?? (match m return aux_set_typing_opt word16 with
             [ HC05 ⇒ None ?
             | HC08 ⇒ Some ? set_indX_16_reg_HC08
             | HCS08 ⇒ Some ? set_indX_16_reg_HC08
             | RS08 ⇒ None ? ])
 (λf.Some ? (set_alu m t s (f (alu m t s) indx16))).

(* setter debole di H:X *)
definition setweak_indX_16_reg ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λindx16:word16.
 match set_indX_16_reg m t s indx16 with
  [ None ⇒ s | Some s' ⇒ s' ].

(* REGISTRO SP *)

(* setter specifico HC05 di SP, effettua (SP∧mask)∨fix *)
definition set_sp_reg_HC05 ≝
λalu.λsp':word16.
 mk_alu_HC05
  (acc_low_reg_HC05 alu)
  (indX_low_reg_HC05 alu)
  (or_w16 (and_w16 sp' (sp_mask_HC05 alu)) (sp_fix_HC05 alu))
  (sp_mask_HC05 alu)
  (sp_fix_HC05 alu)
  (pc_reg_HC05 alu)
  (pc_mask_HC05 alu)
  (h_flag_HC05 alu)
  (i_flag_HC05 alu)
  (n_flag_HC05 alu)
  (z_flag_HC05 alu)
  (c_flag_HC05 alu)
  (irq_flag_HC05 alu).

(* setter specifico HC08/HCS08 di SP *)
definition set_sp_reg_HC08 ≝
λalu.λsp':word16.
 mk_alu_HC08
  (acc_low_reg_HC08 alu)
  (indX_low_reg_HC08 alu)
  (indX_high_reg_HC08 alu)
  sp'
  (pc_reg_HC08 alu)
  (v_flag_HC08 alu)
  (h_flag_HC08 alu)
  (i_flag_HC08 alu)
  (n_flag_HC08 alu)
  (z_flag_HC08 alu)
  (c_flag_HC08 alu)
  (irq_flag_HC08 alu).

(* setter forte di SP *)
definition set_sp_reg ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λsp':word16.
 opt_map ?? (match m return aux_set_typing_opt word16 with
             [ HC05 ⇒ Some ? set_sp_reg_HC05
             | HC08 ⇒ Some ? set_sp_reg_HC08
             | HCS08 ⇒ Some ? set_sp_reg_HC08
             | RS08 ⇒ None ? ])
 (λf.Some ? (set_alu m t s (f (alu m t s) sp'))).

(* setter debole di SP *)
definition setweak_sp_reg ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λsp':word16.
 match set_sp_reg m t s sp' with
  [ None ⇒ s | Some s' ⇒ s' ].

(* REGISTRO PC *)

(* setter specifico HC05 di PC, effettua PC∧mask *)
definition set_pc_reg_HC05 ≝
λalu.λpc':word16.
 mk_alu_HC05
  (acc_low_reg_HC05 alu)
  (indX_low_reg_HC05 alu)
  (sp_reg_HC05 alu)
  (sp_mask_HC05 alu)
  (sp_fix_HC05 alu)
  (and_w16 pc' (pc_mask_HC05 alu))
  (pc_mask_HC05 alu)
  (h_flag_HC05 alu)
  (i_flag_HC05 alu)
  (n_flag_HC05 alu)
  (z_flag_HC05 alu)
  (c_flag_HC05 alu)
  (irq_flag_HC05 alu).

(* setter specifico HC08/HCS08 di PC *)
definition set_pc_reg_HC08 ≝
λalu.λpc':word16.
 mk_alu_HC08
  (acc_low_reg_HC08 alu)
  (indX_low_reg_HC08 alu)
  (indX_high_reg_HC08 alu)
  (sp_reg_HC08 alu)
  pc'
  (v_flag_HC08 alu)
  (h_flag_HC08 alu)
  (i_flag_HC08 alu)
  (n_flag_HC08 alu)
  (z_flag_HC08 alu)
  (c_flag_HC08 alu)
  (irq_flag_HC08 alu).

(* setter specifico RS08 di PC, effettua PC∧mask *)
definition set_pc_reg_RS08 ≝ 
λalu.λpc':word16.
 mk_alu_RS08
  (acc_low_reg_RS08 alu)
  (and_w16 pc' (pc_mask_RS08 alu))
  (pc_mask_RS08 alu)
  (spc_reg_RS08 alu)
  (x_map_RS08 alu)
  (ps_map_RS08 alu)
  (z_flag_RS08 alu)
  (c_flag_RS08 alu).

(* setter forte di PC *)
definition set_pc_reg ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λpc':word16.
 set_alu m t s 
 (match m return aux_set_typing word16 with
  [ HC05 ⇒ set_pc_reg_HC05
  | HC08 ⇒ set_pc_reg_HC08
  | HCS08 ⇒ set_pc_reg_HC08
  | RS08 ⇒ set_pc_reg_RS08
  ] (alu m t s) pc').

(* REGISTRO SPC *)

(* setter specifico RS08 di SPC, effettua SPC∧mask *)
definition set_spc_reg_RS08 ≝ 
λalu.λspc':word16.
 mk_alu_RS08
  (acc_low_reg_RS08 alu)
  (pc_reg_RS08 alu)
  (pc_mask_RS08 alu)
  (and_w16 spc' (pc_mask_RS08 alu))
  (x_map_RS08 alu)
  (ps_map_RS08 alu)
  (z_flag_RS08 alu)
  (c_flag_RS08 alu).

(* setter forte di SPC *)
definition set_spc_reg ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λspc':word16.
 opt_map ?? (match m return aux_set_typing_opt word16 with
             [ HC05 ⇒ None ?
             | HC08 ⇒ None ?
             | HCS08 ⇒ None ?
             | RS08 ⇒ Some ? set_spc_reg_RS08 ])
 (λf.Some ? (set_alu m t s (f (alu m t s) spc'))).

(* setter debole di SPC *)
definition setweak_spc_reg ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λspc':word16.
 match set_spc_reg m t s spc' with
  [ None ⇒ s | Some s' ⇒ s' ].

(* REGISTRO MEMORY MAPPED X *)

(* setter specifico RS08 di memory mapped X *)
definition set_x_map_RS08 ≝ 
λalu.λxm':byte8.
 mk_alu_RS08
  (acc_low_reg_RS08 alu)
  (pc_reg_RS08 alu)
  (pc_mask_RS08 alu)
  (spc_reg_RS08 alu)
  xm'
  (ps_map_RS08 alu)
  (z_flag_RS08 alu)
  (c_flag_RS08 alu).

(* setter forte di memory mapped X *)
definition set_x_map ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λxm':byte8.
 opt_map ?? (match m return aux_set_typing_opt byte8 with
             [ HC05 ⇒ None ?
             | HC08 ⇒ None ?
             | HCS08 ⇒ None ?
             | RS08 ⇒ Some ? set_x_map_RS08 ])
 (λf.Some ? (set_alu m t s (f (alu m t s) xm'))).

(* setter debole di memory mapped X *)
definition setweak_x_map ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λxm':byte8.
 match set_x_map m t s xm' with
  [ None ⇒ s | Some s' ⇒ s' ].

(* REGISTRO MEMORY MAPPED PS *)

(* setter specifico RS08 di memory mapped PS *)
definition set_ps_map_RS08 ≝ 
λalu.λpsm':byte8.
 mk_alu_RS08
  (acc_low_reg_RS08 alu)
  (pc_reg_RS08 alu)
  (pc_mask_RS08 alu)
  (spc_reg_RS08 alu)
  (x_map_RS08 alu)
  psm'
  (z_flag_RS08 alu)
  (c_flag_RS08 alu).

(* setter forte di memory mapped PS *)
definition set_ps_map ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λpsm':byte8.
 opt_map ?? (match m return aux_set_typing_opt byte8 with
             [ HC05 ⇒ None ?
             | HC08 ⇒ None ?
             | HCS08 ⇒ None ?
             | RS08 ⇒ Some ? set_ps_map_RS08 ])
 (λf.Some ? (set_alu m t s (f (alu m t s) psm'))).

(* setter debole di memory mapped PS *)
definition setweak_ps_map ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λpsm':byte8.
 match set_ps_map m t s psm' with
  [ None ⇒ s | Some s' ⇒ s' ].

(* FLAG V *)

(* setter specifico HC08/HCS08 di V *)
definition set_v_flag_HC08 ≝
λalu.λvfl':bool.
 mk_alu_HC08
  (acc_low_reg_HC08 alu)
  (indX_low_reg_HC08 alu)
  (indX_high_reg_HC08 alu)
  (sp_reg_HC08 alu)
  (pc_reg_HC08 alu)
  vfl'
  (h_flag_HC08 alu)
  (i_flag_HC08 alu)
  (n_flag_HC08 alu)
  (z_flag_HC08 alu)
  (c_flag_HC08 alu)
  (irq_flag_HC08 alu).

(* setter forte di V *)
definition set_v_flag ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λvfl':bool.
 opt_map ?? (match m return aux_set_typing_opt bool with
             [ HC05 ⇒ None ?
             | HC08 ⇒ Some ? set_v_flag_HC08
             | HCS08 ⇒ Some ? set_v_flag_HC08
             | RS08 ⇒ None ? ])
 (λf.Some ? (set_alu m t s (f (alu m t s) vfl'))).

(* setter debole  di V *)
definition setweak_v_flag ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λvfl':bool.
 match set_v_flag m t s vfl' with
  [ None ⇒ s | Some s' ⇒ s' ].

(* FLAG H *)

(* setter specifico HC05 di H *)
definition set_h_flag_HC05 ≝
λalu.λhfl':bool.
 mk_alu_HC05
  (acc_low_reg_HC05 alu)
  (indX_low_reg_HC05 alu)
  (sp_reg_HC05 alu)
  (sp_mask_HC05 alu)
  (sp_fix_HC05 alu)
  (pc_reg_HC05 alu)
  (pc_mask_HC05 alu)
  hfl'
  (i_flag_HC05 alu)
  (n_flag_HC05 alu)
  (z_flag_HC05 alu)
  (c_flag_HC05 alu)
  (irq_flag_HC05 alu).

(* setter specifico HC08/HCS08 di H *)
definition set_h_flag_HC08 ≝
λalu.λhfl':bool.
 mk_alu_HC08
  (acc_low_reg_HC08 alu)
  (indX_low_reg_HC08 alu)
  (indX_high_reg_HC08 alu)
  (sp_reg_HC08 alu)
  (pc_reg_HC08 alu)
  (v_flag_HC08 alu)
  hfl'
  (i_flag_HC08 alu)
  (n_flag_HC08 alu)
  (z_flag_HC08 alu)
  (c_flag_HC08 alu)
  (irq_flag_HC08 alu).

(* setter forte di H *)
definition set_h_flag ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λhfl':bool.
 opt_map ?? (match m return aux_set_typing_opt bool with
             [ HC05 ⇒ Some ? set_h_flag_HC05
             | HC08 ⇒ Some ? set_h_flag_HC08
             | HCS08 ⇒ Some ? set_h_flag_HC08
             | RS08 ⇒ None ? ])
 (λf.Some ? (set_alu m t s (f (alu m t s) hfl'))).

(* setter debole di H *)
definition setweak_h_flag ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λhfl':bool.
 match set_h_flag m t s hfl' with
  [ None ⇒ s | Some s' ⇒ s' ].

(* FLAG I *)

(* setter specifico HC05 di I *)
definition set_i_flag_HC05 ≝
λalu.λifl':bool.
 mk_alu_HC05
  (acc_low_reg_HC05 alu)
  (indX_low_reg_HC05 alu)
  (sp_reg_HC05 alu)
  (sp_mask_HC05 alu)
  (sp_fix_HC05 alu)
  (pc_reg_HC05 alu)
  (pc_mask_HC05 alu)
  (h_flag_HC05 alu)
  ifl'
  (n_flag_HC05 alu)
  (z_flag_HC05 alu)
  (c_flag_HC05 alu)
  (irq_flag_HC05 alu).

(* setter specifico HC08/HCS08 di I *)
definition set_i_flag_HC08 ≝
λalu.λifl':bool.
 mk_alu_HC08
  (acc_low_reg_HC08 alu)
  (indX_low_reg_HC08 alu)
  (indX_high_reg_HC08 alu)
  (sp_reg_HC08 alu)
  (pc_reg_HC08 alu)
  (v_flag_HC08 alu)
  (h_flag_HC08 alu)
  ifl'
  (n_flag_HC08 alu)
  (z_flag_HC08 alu)
  (c_flag_HC08 alu)
  (irq_flag_HC08 alu).

(* setter forte di I *)
definition set_i_flag ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λifl':bool.
 opt_map ?? (match m return aux_set_typing_opt bool with
             [ HC05 ⇒ Some ? set_i_flag_HC05
             | HC08 ⇒ Some ? set_i_flag_HC08
             | HCS08 ⇒ Some ? set_i_flag_HC08
             | RS08 ⇒ None ? ])
 (λf.Some ? (set_alu m t s (f (alu m t s) ifl'))).

(* setter debole di I *)
definition setweak_i_flag ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λifl':bool.
 match set_i_flag m t s ifl' with
  [ None ⇒ s | Some s' ⇒ s' ].

(* FLAG N *)

(* setter specifico HC05 di N *)
definition set_n_flag_HC05 ≝
λalu.λnfl':bool.
 mk_alu_HC05
  (acc_low_reg_HC05 alu)
  (indX_low_reg_HC05 alu)
  (sp_reg_HC05 alu)
  (sp_mask_HC05 alu)
  (sp_fix_HC05 alu)
  (pc_reg_HC05 alu)
  (pc_mask_HC05 alu)
  (h_flag_HC05 alu)
  (i_flag_HC05 alu)
  nfl'
  (z_flag_HC05 alu)
  (c_flag_HC05 alu)
  (irq_flag_HC05 alu).

(* setter specifico HC08/HCS08 di N *)
definition set_n_flag_HC08 ≝
λalu.λnfl':bool.
 mk_alu_HC08
  (acc_low_reg_HC08 alu)
  (indX_low_reg_HC08 alu)
  (indX_high_reg_HC08 alu)
  (sp_reg_HC08 alu)
  (pc_reg_HC08 alu)
  (v_flag_HC08 alu)
  (h_flag_HC08 alu)
  (i_flag_HC08 alu)
  nfl'
  (z_flag_HC08 alu)
  (c_flag_HC08 alu)
  (irq_flag_HC08 alu).

(* setter forte di N *)
definition set_n_flag ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λnfl':bool.
 opt_map ?? (match m return aux_set_typing_opt bool with
             [ HC05 ⇒ Some ? set_n_flag_HC05
             | HC08 ⇒ Some ? set_n_flag_HC08
             | HCS08 ⇒ Some ? set_n_flag_HC08
             | RS08 ⇒ None ? ])
 (λf.Some ? (set_alu m t s (f (alu m t s) nfl'))).

(* setter debole di N *)
definition setweak_n_flag ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λnfl':bool.
 match set_n_flag m t s nfl' with
  [ None ⇒ s | Some s' ⇒ s' ].

(* FLAG Z *)

(* setter specifico HC05 di Z *)
definition set_z_flag_HC05 ≝
λalu.λzfl':bool.
 mk_alu_HC05
  (acc_low_reg_HC05 alu)
  (indX_low_reg_HC05 alu)
  (sp_reg_HC05 alu)
  (sp_mask_HC05 alu)
  (sp_fix_HC05 alu)
  (pc_reg_HC05 alu)
  (pc_mask_HC05 alu)
  (h_flag_HC05 alu)
  (i_flag_HC05 alu)
  (n_flag_HC05 alu)
  zfl'
  (c_flag_HC05 alu)
  (irq_flag_HC05 alu).

(* setter specifico HC08/HCS08 di Z *)
definition set_z_flag_HC08 ≝
λalu.λzfl':bool.
 mk_alu_HC08
  (acc_low_reg_HC08 alu)
  (indX_low_reg_HC08 alu)
  (indX_high_reg_HC08 alu)
  (sp_reg_HC08 alu)
  (pc_reg_HC08 alu)
  (v_flag_HC08 alu)
  (h_flag_HC08 alu)
  (i_flag_HC08 alu)
  (n_flag_HC08 alu)
  zfl'
  (c_flag_HC08 alu)
  (irq_flag_HC08 alu).

(* setter sprcifico RS08 di Z *)
definition set_z_flag_RS08 ≝ 
λalu.λzfl':bool.
 mk_alu_RS08
  (acc_low_reg_RS08 alu)
  (pc_reg_RS08 alu)
  (pc_mask_RS08 alu)
  (spc_reg_RS08 alu)
  (x_map_RS08 alu)
  (ps_map_RS08 alu)
  zfl'
  (c_flag_RS08 alu).

(* setter forte di Z *)
definition set_z_flag ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λzfl':bool.
 set_alu m t s 
 (match m return aux_set_typing bool with
  [ HC05 ⇒ set_z_flag_HC05
  | HC08 ⇒ set_z_flag_HC08
  | HCS08 ⇒ set_z_flag_HC08
  | RS08 ⇒ set_z_flag_RS08
  ] (alu m t s) zfl').

(* FLAG C *)

(* setter specifico HC05 di C *)
definition set_c_flag_HC05 ≝
λalu.λcfl':bool.
 mk_alu_HC05
  (acc_low_reg_HC05 alu)
  (indX_low_reg_HC05 alu)
  (sp_reg_HC05 alu)
  (sp_mask_HC05 alu)
  (sp_fix_HC05 alu)
  (pc_reg_HC05 alu)
  (pc_mask_HC05 alu)
  (h_flag_HC05 alu)
  (i_flag_HC05 alu)
  (n_flag_HC05 alu)
  (z_flag_HC05 alu)
  cfl'
  (irq_flag_HC05 alu).

(* setter specifico HC08/HCS08 di C *)
definition set_c_flag_HC08 ≝
λalu.λcfl':bool.
 mk_alu_HC08
  (acc_low_reg_HC08 alu)
  (indX_low_reg_HC08 alu)
  (indX_high_reg_HC08 alu)
  (sp_reg_HC08 alu)
  (pc_reg_HC08 alu)
  (v_flag_HC08 alu)
  (h_flag_HC08 alu)
  (i_flag_HC08 alu)
  (n_flag_HC08 alu)
  (z_flag_HC08 alu)
  cfl'
  (irq_flag_HC08 alu).

(* setter specifico RS08 di C *)
definition set_c_flag_RS08 ≝ 
λalu.λcfl':bool.
 mk_alu_RS08
  (acc_low_reg_RS08 alu)
  (pc_reg_RS08 alu)
  (pc_mask_RS08 alu)
  (spc_reg_RS08 alu)
  (x_map_RS08 alu)
  (ps_map_RS08 alu)
  (z_flag_RS08 alu)
  cfl'.

(* setter forte di C *)
definition set_c_flag ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λcfl':bool.
 set_alu m t s 
 (match m return aux_set_typing bool with
  [ HC05 ⇒ set_c_flag_HC05
  | HC08 ⇒ set_c_flag_HC08
  | HCS08 ⇒ set_c_flag_HC08
  | RS08 ⇒ set_c_flag_RS08
  ] (alu m t s) cfl').

(* FLAG IRQ *)

(* setter specifico HC05 di IRQ *)
definition set_irq_flag_HC05 ≝
λalu.λirqfl':bool.
 mk_alu_HC05
  (acc_low_reg_HC05 alu)
  (indX_low_reg_HC05 alu)
  (sp_reg_HC05 alu)
  (sp_mask_HC05 alu)
  (sp_fix_HC05 alu)
  (pc_reg_HC05 alu)
  (pc_mask_HC05 alu)
  (h_flag_HC05 alu)
  (i_flag_HC05 alu)
  (n_flag_HC05 alu)
  (z_flag_HC05 alu)
  (c_flag_HC05 alu)
  irqfl'.

(* setter specifico HC08/HCS08 di IRQ *)
definition set_irq_flag_HC08 ≝
λalu.λirqfl':bool.
 mk_alu_HC08
  (acc_low_reg_HC08 alu)
  (indX_low_reg_HC08 alu)
  (indX_high_reg_HC08 alu)
  (sp_reg_HC08 alu)
  (pc_reg_HC08 alu)
  (v_flag_HC08 alu)
  (h_flag_HC08 alu)
  (i_flag_HC08 alu)
  (n_flag_HC08 alu)
  (z_flag_HC08 alu)
  (c_flag_HC08 alu)
  irqfl'.

(* setter forte di IRQ *)
definition set_irq_flag ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λirqfl':bool.
 opt_map ?? (match m return aux_set_typing_opt bool with
             [ HC05 ⇒ Some ? set_irq_flag_HC05
             | HC08 ⇒ Some ? set_irq_flag_HC08
             | HCS08 ⇒ Some ? set_irq_flag_HC08
             | RS08 ⇒ None ? ])
 (λf.Some ? (set_alu m t s (f (alu m t s) irqfl'))).

(* setter debole di IRQ *)
definition setweak_irq_flag ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λirqfl':bool.
 match set_irq_flag m t s irqfl' with
  [ None ⇒ s | Some s' ⇒ s' ].

(* ***************** *)
(* CONFRONTO FRA ALU *)
(* ***************** *)

(* confronto registro per registro dell'HC05 *)
definition eq_alu_HC05 ≝
λalu1,alu2:alu_HC05.
 match alu1 with
  [ mk_alu_HC05 acclow1 indxlow1 sp1 spm1 spf1 pc1 pcm1 hfl1 ifl1 nfl1 zfl1 cfl1 irqfl1 ⇒
 match alu2 with
  [ mk_alu_HC05 acclow2 indxlow2 sp2 spm2 spf2 pc2 pcm2 hfl2 ifl2 nfl2 zfl2 cfl2 irqfl2 ⇒
   (eq_b8 acclow1 acclow2) ⊗
   (eq_b8 indxlow1 indxlow2) ⊗
   (eq_w16 sp1 sp2) ⊗
   (eq_w16 spm1 spm2) ⊗
   (eq_w16 spf1 spf2) ⊗
   (eq_w16 pc1 pc2) ⊗
   (eq_w16 pcm1 pcm2) ⊗
   (eq_bool hfl1 hfl2) ⊗
   (eq_bool ifl1 ifl2) ⊗
   (eq_bool nfl1 nfl2) ⊗
   (eq_bool zfl1 zfl2) ⊗
   (eq_bool cfl1 cfl2) ⊗
   (eq_bool irqfl1 irqfl2) ]].

(* confronto registro per registro dell'HC08 *)
definition eq_alu_HC08 ≝
λalu1,alu2:alu_HC08.
 match alu1 with
  [ mk_alu_HC08 acclow1 indxlow1 indxhigh1 sp1 pc1 vfl1 hfl1 ifl1 nfl1 zfl1 cfl1 irqfl1 ⇒
 match alu2 with
  [ mk_alu_HC08 acclow2 indxlow2 indxhigh2 sp2 pc2 vfl2 hfl2 ifl2 nfl2 zfl2 cfl2 irqfl2 ⇒
   (eq_b8 acclow1 acclow2) ⊗
   (eq_b8 indxlow1 indxlow2) ⊗
   (eq_b8 indxhigh1 indxhigh2) ⊗
   (eq_w16 sp1 sp2) ⊗
   (eq_w16 pc1 pc2) ⊗
   (eq_bool vfl1 vfl2) ⊗
   (eq_bool hfl1 hfl2) ⊗
   (eq_bool ifl1 ifl2) ⊗
   (eq_bool nfl1 nfl2) ⊗
   (eq_bool zfl1 zfl2) ⊗
   (eq_bool cfl1 cfl2) ⊗
   (eq_bool irqfl1 irqfl2) ]].

(* confronto registro per registro dell'RS08 *)
definition eq_alu_RS08 ≝
λalu1,alu2:alu_RS08.
 match alu1 with
  [ mk_alu_RS08 acclow1 pc1 pcm1 spc1 xm1 psm1 zfl1 cfl1 ⇒
 match alu2 with
  [ mk_alu_RS08 acclow2 pc2 pcm2 spc2 xm2 psm2 zfl2 cfl2 ⇒
   (eq_b8 acclow1 acclow2) ⊗
   (eq_w16 pc1 pc2) ⊗
   (eq_w16 pcm1 pcm2) ⊗
   (eq_w16 spc1 spc2) ⊗
   (eq_b8 xm1 xm2) ⊗
   (eq_b8 psm1 psm2) ⊗
   (eq_bool zfl1 zfl2) ⊗
   (eq_bool cfl1 cfl2) ]].

(* ******************** *)
(* CONFRONTO FRA STATUS *)
(* ******************** *)

(* la lettura da memoria ritorna un option byte8, quindi bisogna poterli confrontare *)
definition eq_b8_opt ≝
λb1,b2:option byte8.
 match b1 with
  [ None ⇒ match b2 with
   [ None ⇒ true | Some _ ⇒ false ]
  | Some b1' ⇒ match b2 with
   [ None ⇒ false | Some b2' ⇒ eq_b8 b1' b2' ]
  ].

(* confronto di una regione di memoria [inf,inf+n] *)
let rec forall_memory_ranged
 (t:memory_impl)
 (chk1:aux_chk_type t) (chk2:aux_chk_type t)
 (mem1:aux_mem_type t) (mem2:aux_mem_type t)
 (inf:word16) (n:nat) on n ≝
 match n return λ_.bool with
  [ O ⇒ eq_b8_opt (mem_read t mem1 chk1 inf) (mem_read t mem2 chk2 inf)
  | S n' ⇒ (eq_b8_opt (mem_read t mem1 chk1 (plus_w16nc inf (word16_of_nat n)))
                      (mem_read t mem2 chk2 (plus_w16nc inf (word16_of_nat n)))) ⊗
           (forall_memory_ranged t chk1 chk2 mem1 mem2 inf n')
  ].

(* il clk e' option (Prod5T byte8 (any_opcode m) (instr_mode) byte8 word16) *)
definition eq_clk ≝
λm:mcu_type.λc1,c2:option (Prod5T byte8 (any_opcode m) (instr_mode) byte8 word16).
 match c1 with
  [ None ⇒ match c2 with
   [ None ⇒ true | Some _ ⇒ false ]
  | Some c1' ⇒ match c2 with
   [ None ⇒ false | Some c2' ⇒ (eq_b8 (fst5T ????? c1') (fst5T ????? c2')) ⊗
                               (eqop m (snd5T ????? c1') (snd5T ????? c2')) ⊗
                               (eqim (thd5T ????? c1') (thd5T ????? c2')) ⊗
                               (eq_b8 (frth5T ????? c1') (frth5T ????? c2')) ⊗
                               (eq_w16 (ffth5T ????? c1') (ffth5T ????? c2')) ]
  ].

(* generalizzazione del confronto fra stati *)
definition eq_status ≝
λm:mcu_type.λt:memory_impl.λs1,s2:any_status m t.λinf:word16.λn:nat.
 match s1 with [ mk_any_status alu1 mem1 chk1 clk1 ⇒
 match s2 with [ mk_any_status alu2 mem2 chk2 clk2 ⇒

 (* 1) confronto della ALU *)
 (match m return λm:mcu_type.
   match m with
    [ HC05 ⇒ alu_HC05 | HC08 ⇒ alu_HC08 | HCS08 ⇒ alu_HC08 | RS08 ⇒ alu_RS08 ] →
   match m with
    [ HC05 ⇒ alu_HC05 | HC08 ⇒ alu_HC08 | HCS08 ⇒ alu_HC08 | RS08 ⇒ alu_RS08 ] →
   bool with
  [ HC05 ⇒ eq_alu_HC05 | HC08 ⇒ eq_alu_HC08 | HCS08 ⇒ eq_alu_HC08 | RS08 ⇒ eq_alu_RS08 ]
 alu1 alu2) ⊗

 (* 2) confronto della memoria in [inf,inf+n] *)
 (forall_memory_ranged t chk1 chk2 mem1 mem2 inf n) ⊗

 (* 3) confronto del clik *)
 (eq_clk m clk1 clk2)
 ]].

(* assioma da applicare per l'uguaglianza degli stati *)
axiom eq_status_axiom :
∀inf:word16.∀n:nat.∀m:mcu_type.∀t:memory_impl.∀s1,s2:any_status m t.
 (eq_status m t s1 s2 inf n = true) →
 s1 = s2.
