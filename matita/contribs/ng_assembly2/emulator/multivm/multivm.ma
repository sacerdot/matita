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
ndefinition check_susp ≝
λm.match m
    return λm.aux_pseudo_type m → option susp_type
   with
 [ HC05 ⇒ Freescale_check_susp
 | HC08 ⇒ Freescale_check_susp
 | HCS08 ⇒ Freescale_check_susp
 | RS08 ⇒ Freescale_check_susp
 | IP2022 ⇒ IP2022_check_susp
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

(* motiplicatore del ciclo di durata *)
(* 0 = sospensione *)
ndefinition clk_mult ≝
λm.match m
    return λm.Πt.any_status m t → nat
   with
 [ HC05 ⇒ Freescale_clk_mult HC05
 | HC08 ⇒ Freescale_clk_mult HC08
 | HCS08 ⇒ Freescale_clk_mult HCS08
 | RS08 ⇒ Freescale_clk_mult RS08
 | IP2022 ⇒ IP2022_clk_mult
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
    let s_tmp3 ≝ match eqc ? (get_pc_reg … s) (get_pc_reg … s_tmp1) with
                  (* ok, new_pc → pc *)
                  [ true ⇒ set_pc_reg … s_tmp2 new_pc
                  (* effetto collaterale modifica pc! scartare new_pc *)
                  | false ⇒ s_tmp2 ] in
    match check_susp m ps with
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

(* descrittore del fetch PSEUDO + INSTR_MODE + OPCODE + CICLI *)

(* descrittore del click = stato di avanzamento dell'esecuzione *)
(* 1) None = istruzione eseguita, attesa del fetch *)
(* 2) Some cur_clk,clks,pseudo,mode,cur_pc = fetch eseguito *)
ndefinition tick ≝
λm,t.λs:any_status m t.
 match clk_desc … s with
  (* e' il momento del fetch *)
  [ None ⇒ match fetch … s with
   (* errore nel fetch/decode? riportato in output, nessun avanzamento *)
   [ FetchERR err ⇒ TickERR ? s err
   (* nessun errore nel fetch *)
   | FetchOK finfo cur_pc ⇒ match tick_skip_aux … s with
    (* skip mode! *)
    [ true ⇒ TickOK ? (set_clk_desc …
                       (set_pc_reg …
                        (match check_skip m (fst4T … finfo) with
                         [ true ⇒ s | false ⇒ setweak_skip_mode … s false ]) cur_pc) (None ?))
    (* ciclo normale: applicare divisore a numero reale di cicli *)
    | false ⇒
     let real_clk ≝ (clk_mult … s)*(fth4T … finfo) in 
     match real_clk with
      (* 0 = stop *)
      [ O ⇒ TickSUSP ? s STOP_MODE
      | S clk' ⇒ match clk' with
       (* un solo clk, execute subito *)
       [ O ⇒ tick_execute … s (fst4T … finfo) (snd4T … finfo) cur_pc
       (* piu' clk, execute rimandata *)
       | S clk'' ⇒ TickOK ? (set_clk_desc … s
                            (Some ? (quintuple … nat1 real_clk
                                                 (fst4T … finfo) (snd4T … finfo) cur_pc)))
       ]
      ]
    ]
   ]
  (* fetch gia' eseguito, e' il turno di execute? *)
  | Some sinfo ⇒ match eqc ? (S (fst5T … sinfo)) (snd5T … sinfo) with
   (* si *)
   [ true ⇒ tick_execute … s (thd5T … sinfo) (fth5T … sinfo) (fft5T … sinfo)
   (* no, avanzamento cur_clk *)
   | false ⇒ TickOK ? (set_clk_desc … s
                       (Some ? (quintuple … (S (fst5T … sinfo)) (snd5T … sinfo)
                                            (thd5T … sinfo) (fth5T … sinfo) (fft5T … sinfo))))
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

nlemma breakpoint_err : ∀m,t,s,err,n.execute m t (TickERR ? s err) n = TickERR ? s err.
 #m; #t; #s; #err; #n;
 ncases n;
 ##[ ##2: #n1; ##]
 nnormalize;
 napply refl_eq.
nqed.

nlemma breakpoint_susp : ∀m,t,s,susp,n.execute m t (TickSUSP ? s susp) n = TickSUSP ? s susp.
 #m; #t; #s; #susp; #n;
 ncases n;
 ##[ ##2: #n1; ##]
 nnormalize;
 napply refl_eq.
nqed.

nlemma breakpoint :
 ∀m,t,n1,n2,s. execute m t s (n1 + n2) = execute m t (execute m t s n1) n2.
 #m; #t; #n1;
 nelim n1;
 ##[ ##1: nnormalize; #n2; #s; ncases s; nnormalize; ##[ ##1,2: #x ##] #y; napply refl_eq
 ##| ##2: #n3; #H; #n2; #s; ncases s;
          ##[ ##1: #x; #y; nnormalize; nrewrite > (breakpoint_err m t x y n2); napply refl_eq
          ##| ##2: #x; #y; nnormalize; nrewrite > (breakpoint_susp m t x y n2); napply refl_eq
          ##| ##3: #x; nrewrite > (Sn_p_n_to_S_npn n3 n2);
                   nchange with ((execute m t (tick m t x) (n3+n2)) =
                                 (execute m t (execute m t (tick m t x) n3) n2));
                   nrewrite > (H n2 (tick m t x));
                   napply refl_eq
          ##]
 ##]
nqed.
