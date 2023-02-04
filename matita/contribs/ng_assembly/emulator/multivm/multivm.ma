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

include "emulator/multivm/Freescale_multivm.ma".
include "emulator/multivm/IP2022_multivm.ma".
include "emulator/read_write/fetch.ma".

(* raccordo *)
ndefinition execute_any ≝
λm.match m
    return λm.aux_pseudo_type m → Πt.any_status m t → word16 → 
              aux_im_type m → option (ProdT (any_status m t) word16)
   with
 [ HC05 ⇒ λps:aux_pseudo_type ?.Freescale_execute_any ps ?
 | HC08 ⇒ λps:aux_pseudo_type ?.Freescale_execute_any ps ?
 | HCS08 ⇒ λps:aux_pseudo_type ?.Freescale_execute_any ps ?
 | RS08 ⇒ λps:aux_pseudo_type ?.Freescale_execute_any ps ?
 | IP2022 ⇒ λps:aux_pseudo_type ?.IP2022_execute_any ps ?
 ].

(* raccordo *)
ndefinition check_susp_ps ≝
λm.match m
    return λm.aux_pseudo_type m → option susp_type
   with
 [ HC05 ⇒ Freescale_check_susp
 | HC08 ⇒ Freescale_check_susp
 | HCS08 ⇒ Freescale_check_susp
 | RS08 ⇒ Freescale_check_susp
 | IP2022 ⇒ IP2022_check_susp
 ].

ndefinition check_susp_s ≝
λm,t.λs:any_status m t.
 opt_map … (get_speed_reg … s)
  (λspeed.match eq_ex speed xF with
   [ true ⇒ Some ? STOP_MODE
   | false ⇒ None ? ]).

ndefinition check_susp ≝
λm,t.λs:any_status m t.λps:aux_pseudo_type m.
 match check_susp_s … s with
  [ None ⇒ check_susp_ps m ps
  | Some susp ⇒ Some ? susp
  ].

(* raccordo *)
ndefinition check_skip ≝
λm.match m
    return λm.aux_pseudo_type m → bool
   with
 [ HC05 ⇒ Freescale_check_skip
 | HC08 ⇒ Freescale_check_skip
 | HCS08 ⇒ Freescale_check_skip
 | RS08 ⇒ Freescale_check_skip
 | IP2022 ⇒ IP2022_check_skip
 ].

(* **** *)
(* TICK *)
(* **** *)

(* - errore: errore+stato (seguira' reset o …, cmq lo stato non va buttato)
   - sospensione: sospensione+stato (seguira' resume o …)
   - ok: stato *)
ninductive tick_result (A:Type) : Type ≝
  TickERR   : A → error_type → tick_result A
| TickSUSP  : A → susp_type → tick_result A
| TickOK    : A → tick_result A.

(* l'esecuzione e' considerata atomica quindi nel caso di un'instruzione
   da 3 cicli la successione sara'
     ([fetch/decode] s,clk:None) →
     (               s,clk:Some 1,pseudo,mode,3,cur_pc) →
     (               s,clk:Some 2,pseudo,mode,3,cur_pc) →
     ([execute]      s',clk:None) *)
ndefinition tick_execute ≝
λm,t.λs:any_status m t.
λps:aux_pseudo_type m.λi:aux_im_type m.
λcur_pc:word16.
 match execute_any m ps t s cur_pc i with
  (* errore! fine esecuzione *)
  [ None ⇒ TickERR ? (set_clk_desc … s (None ?)) ILL_FETCH_AD
  (* ok, aggiornamento centralizzato *)
  | Some S_newPC ⇒ match S_newPC with
   [ pair s_tmp1 new_pc ⇒
    (* clk azzerato *)
    let s_tmp2 ≝ set_clk_desc … s_tmp1 (None ?) in
    (* aggiornamento pc *)
    let s_tmp3 ≝ match eq_w16 (get_pc_reg … s) (get_pc_reg … s_tmp1) with
                  (* ok, new_pc → pc *)
                  [ true ⇒ set_pc_reg … s_tmp2 new_pc
                  (* effetto collaterale modifica pc! scartare new_pc *)
                  | false ⇒ s_tmp2 ] in
    match check_susp … s ps with
     (* esecuzione continua *)
     [ None ⇒ TickOK ? s_tmp3
     (* esecuzione sospesa *)
     | Some susp ⇒ TickSUSP ? s_tmp3 susp
     ]]].

(* avanza fra fetch / countdown / execute *)
ndefinition tick_skip_aux ≝
λm,t.λs:any_status m t.
 match get_skip_mode … s with
  [ None ⇒ false
  | Some b ⇒ b ].

ndefinition tick ≝
λm,t.λs:any_status m t.
 match clk_desc … s with
  (* e' il momento del fetch *)
  [ None ⇒ match fetch … s with
   (* errore nel fetch/decode? riportato in output, nessun avanzamento *)
   [ FetchERR err ⇒ TickERR ? s err
   (* nessun errore nel fetch *)
   | FetchOK info cur_pc ⇒ match tick_skip_aux … s with
    (* skip mode! *)
    [ true ⇒ TickOK ? (set_clk_desc …
                       (set_pc_reg …
                        (match check_skip m (fst4T … info) with
                         [ true ⇒ s | false ⇒ setweak_skip_mode … s false ]) cur_pc) (None ?))
    (* ciclo normale *)
    | false ⇒ match eq_b8 〈x0,x1〉 (fth4T … info) with
     (* un solo clk, execute subito *)
     [ true ⇒ tick_execute … s (fst4T … info) (snd4T … info) cur_pc
     (* piu' clk, execute rimandata *)
     | false ⇒ TickOK ? (set_clk_desc … s
                         (Some ? (quintuple … 〈x0,x1〉 (fst4T … info) (snd4T … info)
                                              (fth4T … info) cur_pc)))
     ]
    ]
   ]
  (* fetch gia' eseguito, e' il turno di execute? *)
  | Some info ⇒ match eq_b8 (succ_b8 (fst5T … info)) (fth5T … info) with
   (* si *)
   [ true ⇒ tick_execute … s (snd5T … info) (thd5T … info) (fft5T … info)
   (* no, avanzamento cur_clk *)
   | false ⇒ TickOK ? (set_clk_desc … s
                       (Some ? (quintuple … (succ_b8 (fst5T … info)) (snd5T … info)
                                            (thd5T … info) (fth5T … info) (fft5T … info))))
   ]
  ].

(* ********** *)
(* ESECUZIONE *)
(* ********** *)

nlet rec execute (m:mcu_type) (t:memory_impl) (s:tick_result (any_status m t)) (n:nat) on n ≝
 match s with
  [ TickERR s' error ⇒ TickERR ? s' error
  | TickSUSP s' susp ⇒ TickSUSP ? s' susp
  | TickOK s'        ⇒ match n with [ O ⇒ TickOK ? s' | S n' ⇒ execute m t (tick m t s') n' ]
  ].
