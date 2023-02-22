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

include "freescale/model.ma".

(* errori possibili nel fetch *)
inductive error_type : Type ≝
  ILL_OP: error_type
| ILL_FETCH_AD: error_type
| ILL_EX_AD: error_type.

(* un tipo opzione ad hoc
   - errore: interessa solo l'errore
   - ok: interessa info e il nuovo pc
*)
inductive fetch_result (A:Type) : Type ≝
  FetchERR : error_type → fetch_result A
| FetchOK  : A → word16 → fetch_result A.

(* **************************** *)
(* FETCH E ACCESSO ALLA MEMORIA *)
(* **************************** *)

(* ausialiaria per RS08 read *)
(* come anticipato in status, nell'RS08 ci sono 2 registri importanti
   memory mapped, quindi bisona intercettare la lettura.
   NB: fare molta attenzione alle note sulle combinazioni possibili perche'
       il comportamento della memoria nell'RS08 e' strano e ci sono
       precise condizioni che impediscono una semantica circolare dell'accesso
       (divergenza=assenza di definizione) *)
definition RS08_memory_filter_read_aux ≝
λt:memory_impl.λs:any_status RS08 t.λaddr:word16.
λT:Type.λfREG:byte8 → option T.λfMEM:aux_mem_type t → aux_chk_type t → word16 → option T.
match s with
 [ mk_any_status alu mem chk _ ⇒ match alu with
  [ mk_alu_RS08 _ _ _ _ xm psm _ _ ⇒
(* 
   possibili accessi al registro X
   1) addr=000F: diretto
   2) addr=000E (X =0F): indiretto
   3) addr=00CF (PS=00): paging
  
   [NB] altre combinazioni non funzionano perche' la MCU non e' un oggetto reattivo:
   non si possono combinare due effetti contemporaneamente!
   per esempio accesso addr=00CE (PS=00,X=0F) non puo' produrre 2 indirezioni 
*) 
  match eq_w16 addr 〈〈x0,x0〉:〈x0,xF〉〉 ⊕
        (eq_w16 addr 〈〈x0,x0〉:〈x0,xE〉〉 ⊗ eq_b8 xm 〈x0,xF〉) ⊕
        (eq_w16 addr 〈〈x0,x0〉:〈xC,xF〉〉 ⊗ eq_b8 psm 〈x0,x0〉) with
   [ true ⇒ fREG xm
   | false ⇒
(* 
   possibili accessi al registro PS
   1) addr=001F: diretto
   2) addr=000E (X =1F): indiretto
   3) addr=00DF (PS=00): paging
*)
    match eq_w16 addr 〈〈x0,x0〉:〈x1,xF〉〉 ⊕
         (eq_w16 addr 〈〈x0,x0〉:〈x0,xE〉〉 ⊗ eq_b8 xm 〈x1,xF〉) ⊕
         (eq_w16 addr 〈〈x0,x0〉:〈xD,xF〉〉 ⊗ eq_b8 psm 〈x0,x0〉) with
     [ true ⇒ fREG psm
     | false ⇒
(* 
   accesso a D[X]: se accede a [00C0-00FF] e' la RAM fisica, non il paging 
   altrimenti sarebbero 2 indirezioni
*)
      match eq_w16 addr 〈〈x0,x0〉:〈x0,xE〉〉 with
       [ true ⇒ fMEM mem chk 〈〈x0,x0〉:xm〉
       | false ⇒ 
(* 
   accesso al paging: [00pp pppp ppxx xxxx] con p=PS x=addr
*)
        match in_range addr 〈〈x0,x0〉:〈xC,x0〉〉 〈〈x0,x0〉:〈xF,xF〉〉 with
         [ true ⇒ fMEM mem chk (or_w16 (fst ?? (shr_w16 (fst ?? (shr_w16 〈psm:〈x0,x0〉〉))))
                                             (and_w16 addr 〈〈x0,x0〉:〈x3,xF〉〉))
(*
   accesso normale
*)
         | false ⇒ fMEM mem chk addr ]]]]]].

(* lettura RS08 di un byte *)
definition RS08_memory_filter_read ≝
λt:memory_impl.λs:any_status RS08 t.λaddr:word16.
 RS08_memory_filter_read_aux t s addr byte8
  (λb.Some byte8 b)
  (λm:aux_mem_type t.λc:aux_chk_type t.λa:word16.mem_read t m c a).

(* lettura RS08 di un bit *)
definition RS08_memory_filter_read_bit ≝
λt:memory_impl.λs:any_status RS08 t.λaddr:word16.λsub:oct.
 RS08_memory_filter_read_aux t s addr bool
  (λb.Some bool (getn_array8T sub bool (bits_of_byte8 b)))
  (λm:aux_mem_type t.λc:aux_chk_type t.λa:word16.mem_read_bit t m c a sub).

(* in caso di RS08 si dirotta sul filtro, altrimenti si legge direttamente *)
definition memory_filter_read ≝
λm:mcu_type.λt:memory_impl.match m return λm:mcu_type.any_status m t → word16 → option byte8 with
 [ HC05 ⇒ λs:any_status HC05 t.λaddr:word16.
  mem_read t (get_mem_desc ? t s) (get_chk_desc ? t s) addr
 | HC08 ⇒ λs:any_status HC08 t.λaddr:word16.
  mem_read t (get_mem_desc ? t s) (get_chk_desc ? t s) addr
 | HCS08 ⇒ λs:any_status HCS08 t.λaddr:word16.
  mem_read t (get_mem_desc ? t s) (get_chk_desc ? t s) addr
 | RS08 ⇒ λs:any_status RS08 t.λaddr:word16.
  RS08_memory_filter_read t s addr
 ].

definition memory_filter_read_bit ≝
λm:mcu_type.λt:memory_impl.match m return λm:mcu_type.any_status m t → word16 → oct → option bool with
 [ HC05 ⇒ λs:any_status HC05 t.λaddr:word16.λsub:oct.
  mem_read_bit t (get_mem_desc ? t s) (get_chk_desc ? t s) addr sub
 | HC08 ⇒ λs:any_status HC08 t.λaddr:word16.λsub:oct.
  mem_read_bit t (get_mem_desc ? t s) (get_chk_desc ? t s) addr sub
 | HCS08 ⇒ λs:any_status HCS08 t.λaddr:word16.λsub:oct.
  mem_read_bit t (get_mem_desc ? t s) (get_chk_desc ? t s) addr sub
 | RS08 ⇒ λs:any_status RS08 t.λaddr:word16.λsub:oct.
  RS08_memory_filter_read_bit t s addr sub
 ].

(* ausialiaria per RS08 write *)
(* come anticipato in status, nell'RS08 ci sono 2 registri importanti
   memory mapped, quindi bisona intercettare la scrittura.
   NB: fare molta attenzione alle note sulle combinazioni possibili perche'
       il comportamento della memoria nell'RS08 e' strano e ci sono
       precise condizioni che impediscono una semantica circolare dell'accesso
       (divergenza=assenza di definizione) *)
definition RS08_memory_filter_write_aux ≝
λt:memory_impl.λs:any_status RS08 t.λaddr:word16.
λfREG:byte8 → byte8.λfMEM:aux_mem_type t → aux_chk_type t → word16 → option (aux_mem_type t).
match s with 
 [ mk_any_status alu mem chk clk ⇒ match alu with
  [ mk_alu_RS08 acclow pc pcm spc xm psm zfl cfl ⇒
(* 
   possibili accessi al registro X
   1) addr=000F: diretto
   2) addr=000E (X =0F): indiretto
   3) addr=00CF (PS=00): paging
  
   [NB] altre combinazioni non funzionano perche' la MCU non e' un oggetto reattivo:
   non si possono combinare due effetti contemporaneamente!
   per esempio accesso addr=00CE (PS=00,X=0F) non puo' produrre 2 indirezioni 
*) 
  match eq_w16 addr 〈〈x0,x0〉:〈x0,xF〉〉 ⊕
        (eq_w16 addr 〈〈x0,x0〉:〈x0,xE〉〉 ⊗ eq_b8 xm 〈x0,xF〉) ⊕
        (eq_w16 addr 〈〈x0,x0〉:〈xC,xF〉〉 ⊗ eq_b8 psm 〈x0,x0〉) with
   [ true ⇒ Some ? (mk_any_status RS08 t (mk_alu_RS08 acclow pc pcm spc (fREG xm) psm zfl cfl) mem chk clk)
   | false ⇒
(* 
   possibili accessi al registro PS
   1) addr=001F: diretto
   2) addr=000E (X =1F): indiretto
   3) addr=00DF (PS=00): paging
*)
    match eq_w16 addr 〈〈x0,x0〉:〈x1,xF〉〉 ⊕
         (eq_w16 addr 〈〈x0,x0〉:〈x0,xE〉〉 ⊗ eq_b8 xm 〈x1,xF〉) ⊕
         (eq_w16 addr 〈〈x0,x0〉:〈xD,xF〉〉 ⊗ eq_b8 psm 〈x0,x0〉) with
     [ true ⇒ Some ? (mk_any_status RS08 t (mk_alu_RS08 acclow pc pcm spc xm (fREG psm) zfl cfl) mem chk clk)
     | false ⇒
(* 
   accesso a D[X]: se accede a [00C0-00FF] e' la RAM fisica, non il paging 
   altrimenti sarebbero 2 indirezioni
*)
      match eq_w16 addr 〈〈x0,x0〉:〈x0,xE〉〉 with
       [ true ⇒ opt_map ?? (fMEM mem chk 〈〈x0,x0〉:xm〉)
                 (λmem'.Some ? (mk_any_status RS08 t (mk_alu_RS08 acclow pc pcm spc xm psm zfl cfl) mem' chk clk))
                                                      
       | false ⇒
(* 
   accesso al paging: [00pp pppp ppxx xxxx] con p=PS x=addr
*)
        match in_range addr 〈〈x0,x0〉:〈xC,x0〉〉 〈〈x0,x0〉:〈xF,xF〉〉 with
         [ true ⇒ opt_map ?? (fMEM mem chk (or_w16 (fst ?? (shr_w16 (fst ?? (shr_w16 〈psm:〈x0,x0〉〉))))
                                                   (and_w16 addr 〈〈x0,x0〉:〈x3,xF〉〉)))
                   (λmem'.Some ? (mk_any_status RS08 t (mk_alu_RS08 acclow pc pcm spc xm psm zfl cfl) mem' chk clk))
(*
   accesso normale
*)
         | false ⇒ opt_map ?? (fMEM mem chk addr)
                    (λmem'.Some ? (mk_any_status RS08 t (mk_alu_RS08 acclow pc pcm spc xm psm zfl cfl) mem' chk clk)) ]]]]]].

(* scrittura RS08 di un byte *)
definition RS08_memory_filter_write ≝
λt:memory_impl.λs:any_status RS08 t.λaddr:word16.λval:byte8.
 RS08_memory_filter_write_aux t s addr
  (λb.val)
  (λm:aux_mem_type t.λc:aux_chk_type t.λa:word16.mem_update t m c a val).

(* scrittura RS08 di un bit *)
definition RS08_memory_filter_write_bit ≝
λt:memory_impl.λs:any_status RS08 t.λaddr:word16.λsub:oct.λval:bool.
 RS08_memory_filter_write_aux t s addr
  (λb.byte8_of_bits (setn_array8T sub bool (bits_of_byte8 b) val))
  (λm:aux_mem_type t.λc:aux_chk_type t.λa:word16.mem_update_bit t m c a sub val).

(* in caso di RS08 si dirotta sul filtro, altrimenti si scrive direttamente *)
definition memory_filter_write ≝
λm:mcu_type.λt:memory_impl.match m
 return λm:mcu_type.any_status m t → word16 → byte8 → option (any_status m t) with
 [ HC05 ⇒ λs:any_status HC05 t.λaddr:word16.λval:byte8.
  opt_map ?? (mem_update t (get_mem_desc ? t s) (get_chk_desc ? t s) addr val)
   (λmem.Some ? (set_mem_desc ? t s mem)) 
 | HC08 ⇒ λs:any_status HC08 t.λaddr:word16.λval:byte8.
  opt_map ?? (mem_update t (get_mem_desc ? t s) (get_chk_desc ? t s) addr val)
   (λmem.Some ? (set_mem_desc ? t s mem))
 | HCS08 ⇒ λs:any_status HCS08 t.λaddr:word16.λval:byte8.
  opt_map ?? (mem_update t (get_mem_desc ? t s) (get_chk_desc ? t s) addr val)
   (λmem.Some ? (set_mem_desc ? t s mem)) 
 | RS08 ⇒ λs:any_status RS08 t.λaddr:word16.λval:byte8.
  RS08_memory_filter_write t s addr val
 ].

definition memory_filter_write_bit ≝
λm:mcu_type.λt:memory_impl.match m
 return λm:mcu_type.any_status m t → word16 → oct → bool → option (any_status m t) with
 [ HC05 ⇒ λs:any_status HC05 t.λaddr:word16.λsub:oct.λval:bool.
  opt_map ?? (mem_update_bit t (get_mem_desc ? t s) (get_chk_desc ? t s) addr sub val)
   (λmem.Some ? (set_mem_desc ? t s mem)) 
 | HC08 ⇒ λs:any_status HC08 t.λaddr:word16.λsub:oct.λval:bool.
  opt_map ?? (mem_update_bit t (get_mem_desc ? t s) (get_chk_desc ? t s) addr sub val)
   (λmem.Some ? (set_mem_desc ? t s mem))
 | HCS08 ⇒ λs:any_status HCS08 t.λaddr:word16.λsub:oct.λval:bool.
  opt_map ?? (mem_update_bit t (get_mem_desc ? t s) (get_chk_desc ? t s) addr sub val)
   (λmem.Some ? (set_mem_desc ? t s mem)) 
 | RS08 ⇒ λs:any_status RS08 t.λaddr:word16.λsub:oct.λval:bool.
  RS08_memory_filter_write_bit t s addr sub val
 ].

(*
   Da utilizzarsi solo per gli aggiornamenti di PC (per il fetch),
   NON per il caricamento degli indiretti.
   - il caricamento degli immediati spetta al fetcher
     (incremento progressivo di PC ciclo per ciclo, e riempimento del prefetch
      che a questo punto DEVE poter indirizzare qualsiasi locazione puntata da PC)
   - il caricamento degli indiretti non spetta al fetcher
*)
definition filtered_inc_w16 ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λw:word16.
 get_pc_reg m t (set_pc_reg m t s (succ_w16 w)).

let rec filtered_plus_w16 (m:mcu_type) (t:memory_impl) (s:any_status m t) (w:word16) (n:nat) on n ≝
 match n with
  [ O ⇒ w
  | S n' ⇒ filtered_plus_w16 m t s (filtered_inc_w16 m t s w) n' ].

(* 
   errore1: non esiste traduzione ILL_OP
   errore2: non e' riuscito a leggere ILL_FETCH_AD
   altrimenti OK=info+new_pc
*)
definition fetch ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.
 let pc ≝ get_pc_reg m t s in
 let pc_next1 ≝ filtered_inc_w16 m t s pc in
 let pc_next2 ≝ filtered_inc_w16 m t s pc_next1 in
 match memory_filter_read m t s pc with
  [ None ⇒ FetchERR ? ILL_FETCH_AD
  | Some bh ⇒ match full_info_of_word16 m (Byte bh) with
   (* non ha trovato una traduzione con 1 byte *)
   [ None ⇒ match m with
    (* HC05 non esistono op a 2 byte *)
    [ HC05 ⇒ FetchERR ? ILL_OP
    | HC08 ⇒ match eq_b8 bh 〈x9,xE〉 with
     (* HC08 se il primo byte e' 0x9E il secondo puo' avere senso *)
     [ true ⇒ match memory_filter_read m t s pc_next1 with
      [ None ⇒ FetchERR ? ILL_FETCH_AD | Some bl ⇒ match full_info_of_word16 m (Word (mk_word16 bh bl)) with
      [ None ⇒ FetchERR ? ILL_OP | Some info ⇒ FetchOK ? info pc_next2 ]]
     (* HC08 se il primo byte non e' 0x9E il secondo non puo' avere senso *)
     | false ⇒ FetchERR ? ILL_OP
     ]
    | HCS08 ⇒ match eq_b8 bh 〈x9,xE〉 with
     (* HCS08 se il primo byte e' 0x9E il secondo puo' avere senso *)
     [ true ⇒ match memory_filter_read m t s pc_next1 with
      [ None ⇒ FetchERR ? ILL_FETCH_AD | Some bl ⇒ match full_info_of_word16 m (Word (mk_word16 bh bl)) with
      [ None ⇒ FetchERR ? ILL_OP | Some info ⇒ FetchOK ? info pc_next2 ]]
     (* HCS08 se il primo byte non e' 0x9E il secondo non puo' avere senso *)
     | false ⇒ FetchERR ? ILL_OP
     ]
    (* RS08 non esistono op a 2 byte *)
    | RS08 ⇒ FetchERR ? ILL_OP
    ]
   (* ha trovato una traduzione con 1 byte *)
   | Some info ⇒ FetchOK ? info pc_next1 ]].

(* ************************ *)
(* MODALITA' INDIRIZZAMENTO *)
(* ************************ *)

(* mattoni base *)
(* - incrementano l'indirizzo normalmente *)
(* - incrementano PC attraverso il filtro *)

(* lettura byte da addr *)
definition loadb_from ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λaddr:word16.λcur_pc:word16.λfetched:nat.
 opt_map ?? (memory_filter_read m t s addr)
  (λb.Some ? (tripleT ??? s b (filtered_plus_w16 m t s cur_pc fetched))).

(* lettura bit da addr *)
definition loadbit_from ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λaddr:word16.λsub:oct.λcur_pc:word16.λfetched:nat.
 opt_map ?? (memory_filter_read_bit m t s addr sub)
  (λb.Some ? (tripleT ??? s b (filtered_plus_w16 m t s cur_pc fetched))).

(* lettura word da addr *)
definition loadw_from ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λaddr:word16.λcur_pc:word16.λfetched:nat.
 opt_map ?? (memory_filter_read m t s addr)
  (λbh.opt_map ?? (memory_filter_read m t s (succ_w16 addr))
   (λbl.Some ? (tripleT ??? s (mk_word16 bh bl) (filtered_plus_w16 m t s cur_pc fetched)))).

(* scrittura byte su addr *)
definition writeb_to ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λaddr:word16.λcur_pc:word16.λfetched:nat.λwriteb:byte8.
 opt_map ?? (memory_filter_write m t s addr writeb)
  (λtmps.Some ? (pair ?? tmps (filtered_plus_w16 m t s cur_pc fetched))).

(* scrittura bit su addr *)
definition writebit_to ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λaddr:word16.λsub:oct.λcur_pc:word16.λfetched:nat.λwriteb:bool.
 opt_map ?? (memory_filter_write_bit m t s addr sub writeb)
  (λtmps.Some ? (pair ?? tmps (filtered_plus_w16 m t s cur_pc fetched))).

(* scrittura word su addr *) 
definition writew_to ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λaddr:word16.λcur_pc:word16.λfetched:nat.λwritew:word16.
 opt_map ?? (memory_filter_write m t s addr (w16h writew))
  (λtmps1.opt_map ?? (memory_filter_write m t tmps1 (succ_w16 addr) (w16l writew))
    (λtmps2.Some ? (pair ?? tmps2 (filtered_plus_w16 m t tmps2 cur_pc fetched)))).

(* ausiliari per definire i tipi e la lettura/scrittura *)

(* ausiliaria per definire il tipo di aux_load *)
definition aux_load_typing ≝
λm:mcu_type.λt:memory_impl.λbyteflag:bool.
 any_status m t → word16 → word16 → nat →
 option (Prod3T (any_status m t) match byteflag with [ true ⇒ byte8 | false ⇒ word16 ] word16).

(* per non dover ramificare i vari load in byte/word *)
definition aux_load ≝
λm:mcu_type.λt:memory_impl.λbyteflag:bool.match byteflag return aux_load_typing m t with
 [ true ⇒ loadb_from m t | false ⇒ loadw_from m t ].

(* ausiliaria per definire il tipo di aux_write *)
definition aux_write_typing ≝
λm:mcu_type.λt:memory_impl.λbyteflag:bool.
 any_status m t → word16 → word16 → nat →
 match byteflag with [ true ⇒ byte8 | false ⇒ word16 ] →
 option (Prod (any_status m t) word16).

(* per non dover ramificare i vari load in byte/word *)
definition aux_write ≝
λm:mcu_type.λt:memory_impl.λbyteflag:bool.match byteflag return aux_write_typing m t with
 [ true ⇒ writeb_to m t | false ⇒ writew_to m t ].

(* modalita' vere e proprie *)

(* lettura da [curpc]: IMM1 comportamento asimmetrico, quindi non si appoggia a loadb *)
definition mode_IMM1_load ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.
 opt_map ?? (memory_filter_read m t s cur_pc)
  (λb.Some ? (tripleT ??? s b (filtered_inc_w16 m t s cur_pc))).

(* lettura da [curpc]: IMM1 + estensione a word *)
definition mode_IMM1EXT_load ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.
 opt_map ?? (memory_filter_read m t s cur_pc)
  (λb.Some ? (tripleT ??? s 〈〈x0,x0〉:b〉 (filtered_inc_w16 m t s cur_pc))).

(* lettura da [curpc]: IMM2 comportamento asimmetrico, quindi non si appoggia a loadw *)
definition mode_IMM2_load ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.
 opt_map ?? (memory_filter_read m t s cur_pc)
  (λbh.opt_map ?? (memory_filter_read m t s (filtered_inc_w16 m t s cur_pc))
   (λbl.Some ? (tripleT ??? s (mk_word16 bh bl) (filtered_plus_w16 m t s cur_pc 2)))).

(* lettura da [byte [curpc]]: true=DIR1 loadb, false=DIR1 loadw *)
definition mode_DIR1_load ≝
λbyteflag:bool.λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.
 opt_map ?? (memory_filter_read m t s cur_pc)
  (λaddr.(aux_load m t byteflag) s 〈〈x0,x0〉:addr〉 cur_pc 1).

(* lettura da [byte [curpc]]: loadbit *)
definition mode_DIR1n_load ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.λsub:oct.
 opt_map ?? (memory_filter_read m t s cur_pc)
  (λaddr.loadbit_from m t  s 〈〈x0,x0〉:addr〉 sub cur_pc 1).

(* scrittura su [byte [curpc]]: true=DIR1 writeb, false=DIR1 writew *)
definition mode_DIR1_write ≝
λbyteflag:bool.λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.
λwritebw:match byteflag with [ true ⇒ byte8 | false ⇒ word16 ].
 opt_map ?? (memory_filter_read m t s cur_pc)
  (λaddr.(aux_write m t byteflag) s 〈〈x0,x0〉:addr〉 cur_pc 1 writebw).

(* scrittura su [byte [curpc]]: writebit *)
definition mode_DIR1n_write ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.λsub:oct.λwriteb:bool.
 opt_map ?? (memory_filter_read m t s cur_pc)
  (λaddr.writebit_to m t s 〈〈x0,x0〉:addr〉 sub cur_pc 1 writeb).

(* lettura da [word [curpc]]: true=DIR2 loadb, false=DIR2 loadw *)
definition mode_DIR2_load ≝
λbyteflag:bool.λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.
 opt_map ?? (memory_filter_read m t s cur_pc)
  (λaddrh.opt_map ?? (memory_filter_read m t s (filtered_inc_w16 m t s cur_pc))
   (λaddrl.(aux_load m t byteflag) s 〈addrh:addrl〉 cur_pc 2)).

(* scrittura su [word [curpc]]: true=DIR2 writeb, false=DIR2 writew *)
definition mode_DIR2_write ≝
λbyteflag:bool.λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.
λwritebw:match byteflag with [ true ⇒ byte8 | false ⇒ word16 ].
 opt_map ?? (memory_filter_read m t s cur_pc)
  (λaddrh.opt_map ?? (memory_filter_read m t s (filtered_inc_w16 m t s cur_pc))
   (λaddrl.(aux_write m t byteflag) s 〈addrh:addrl〉 cur_pc 2 writebw)).

definition get_IX ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.
 match m with
  [ HC05 ⇒ opt_map ?? (get_indX_8_low_reg m t s) (λindx.Some ? 〈〈x0,x0〉:indx〉) 
  | HC08 ⇒ opt_map ?? (get_indX_16_reg m t s) (λindx.Some ? indx) 
  | HCS08 ⇒ opt_map ?? (get_indX_16_reg m t s) (λindx.Some ? indx) 
  | RS08 ⇒ None ? ].

(* lettura da [IX]: true=IX0 loadb, false=IX0 loadw *)
definition mode_IX0_load ≝
λbyteflag:bool.λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.
 opt_map ?? (get_IX m t s)
  (λaddr.(aux_load m t byteflag) s addr cur_pc 0).

(* scrittura su [IX]: true=IX0 writeb, false=IX0 writew *)
definition mode_IX0_write ≝
λbyteflag:bool.λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.
λwritebw:match byteflag with [ true ⇒ byte8 | false ⇒ word16 ].
 opt_map ?? (get_IX m t s)
  (λaddr.(aux_write m t byteflag) s addr cur_pc 0 writebw).

(* lettura da [IX+byte [pc]]: true=IX1 loadb, false=IX1 loadw *)
definition mode_IX1_load ≝
λbyteflag:bool.λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.
 opt_map ?? (get_IX m t s)
  (λaddr.opt_map ?? (memory_filter_read m t s cur_pc)
   (λoffs.(aux_load m t byteflag) s (plus_w16nc addr 〈〈x0,x0〉:offs〉) cur_pc 1)).

(* lettura da X+[byte curpc] *)
definition mode_IX1ADD_load ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.
 opt_map ?? (memory_filter_read m t s cur_pc)
  (λb.opt_map ?? (get_IX m t s)
   (λaddr.Some ? (tripleT ??? s (plus_w16nc addr 〈〈x0,x0〉:b〉) (filtered_inc_w16 m t s cur_pc)))).

(* scrittura su [IX+byte [pc]]: true=IX1 writeb, false=IX1 writew *)
definition mode_IX1_write ≝
λbyteflag:bool.λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.
λwritebw:match byteflag with [ true ⇒ byte8 | false ⇒ word16 ].
 opt_map ?? (get_IX m t s)
  (λaddr.opt_map ?? (memory_filter_read m t s cur_pc)
   (λoffs.(aux_write m t byteflag) s (plus_w16nc addr 〈〈x0,x0〉:offs〉) cur_pc 1 writebw)).

(* lettura da [IX+word [pc]]: true=IX2 loadb, false=IX2 loadw *)
definition mode_IX2_load ≝
λbyteflag:bool.λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.
 opt_map ?? (get_IX m t s)
  (λaddr.opt_map ?? (memory_filter_read m t s cur_pc)
   (λoffsh.opt_map ?? (memory_filter_read m t s (filtered_inc_w16 m t s cur_pc))
    (λoffsl.(aux_load m t byteflag) s (plus_w16nc addr 〈offsh:offsl〉) cur_pc 2))).

(* lettura da X+[word curpc] *)
definition mode_IX2ADD_load ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.
 opt_map ?? (memory_filter_read m t s cur_pc)
  (λbh.opt_map ?? (memory_filter_read m t s (filtered_inc_w16 m t s cur_pc))
   (λbl.opt_map ?? (get_IX m t s)
    (λaddr.Some ? (tripleT ??? s (plus_w16nc addr 〈bh:bl〉) (filtered_plus_w16 m t s cur_pc 2))))).

(* scrittura su [IX+word [pc]]: true=IX2 writeb, false=IX2 writew *)
definition mode_IX2_write ≝
λbyteflag:bool.λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.
λwritebw:match byteflag with [ true ⇒ byte8 | false ⇒ word16 ].
 opt_map ?? (get_IX m t s)
  (λaddr.opt_map ?? (memory_filter_read m t s cur_pc)
   (λoffsh.opt_map ?? (memory_filter_read m t s (filtered_inc_w16 m t s cur_pc))
    (λoffsl.(aux_write m t byteflag) s (plus_w16nc addr 〈offsh:offsl〉) cur_pc 2 writebw))).

(* lettura da [SP+byte [pc]]: true=SP1 loadb, false=SP1 loadw *)
definition mode_SP1_load ≝
λbyteflag:bool.λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.
 opt_map ?? (get_sp_reg m t s)
  (λaddr.opt_map ?? (memory_filter_read m t s cur_pc)
   (λoffs.(aux_load m t byteflag) s (plus_w16nc addr 〈〈x0,x0〉:offs〉) cur_pc 1)).

(* scrittura su [SP+byte [pc]]: true=SP1 writeb, false=SP1 writew *)
definition mode_SP1_write ≝
λbyteflag:bool.λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.
λwritebw:match byteflag with [ true ⇒ byte8 | false ⇒ word16 ].
 opt_map ?? (get_sp_reg m t s)
  (λaddr.opt_map ?? (memory_filter_read m t s cur_pc)
   (λoffs.(aux_write m t byteflag) s (plus_w16nc addr 〈〈x0,x0〉:offs〉) cur_pc 1 writebw)).

(* lettura da [SP+word [pc]]: true=SP2 loadb, false=SP2 loadw *)
definition mode_SP2_load ≝
λbyteflag:bool.λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.
 opt_map ?? (get_sp_reg m t s)
  (λaddr.opt_map ?? (memory_filter_read m t s cur_pc)
   (λoffsh.opt_map ?? (memory_filter_read m t s (filtered_inc_w16 m t s cur_pc))
    (λoffsl.(aux_load m t byteflag) s (plus_w16nc addr 〈offsh:offsl〉) cur_pc 2))).

(* scrittura su [SP+word [pc]]: true=SP2 writeb, false=SP2 writew *)
definition mode_SP2_write ≝
λbyteflag:bool.λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.
λwritebw:match byteflag with [ true ⇒ byte8 | false ⇒ word16 ].
 opt_map ?? (get_sp_reg m t s)
  (λaddr.opt_map ?? (memory_filter_read m t s cur_pc)
   (λoffsh.opt_map ?? (memory_filter_read m t s (filtered_inc_w16 m t s cur_pc))
    (λoffsl.(aux_write m t byteflag) s (plus_w16nc addr 〈offsh:offsl〉) cur_pc 2 writebw))).

(* ************************************** *)
(* raccordo di tutte le possibili letture *)
(* ************************************** *)

(* H:X++ *)
definition aux_inc_indX_16 ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.
 opt_map ?? (get_indX_16_reg m t s)
  (λX_op.opt_map ?? (set_indX_16_reg m t s (succ_w16 X_op))
   (λs_tmp.Some ? s_tmp)).

(* tutte le modalita' di lettura: false=loadb true=loadw *)
definition multi_mode_load ≝
λbyteflag:bool.λm:mcu_type.λt:memory_impl.
 match byteflag
 return λbyteflag:bool.any_status m t → word16 → instr_mode → 
  option (Prod3T (any_status m t) match byteflag with [ true ⇒ byte8 | false ⇒ word16 ] word16)
 with
  (* lettura di un byte *)
  [ true ⇒ λs:any_status m t.λcur_pc:word16.λi:instr_mode.match i with
(* NO: non ci sono indicazioni *)
   [ MODE_INH  ⇒ None ?
(* restituisce A *)
   | MODE_INHA ⇒ Some ? (tripleT ??? s (get_acc_8_low_reg m t s) cur_pc)
(* restituisce X *)
   | MODE_INHX ⇒ opt_map ?? (get_indX_8_low_reg m t s)
                  (λindx.Some ? (tripleT ??? s indx cur_pc))
(* restituisce H *)
   | MODE_INHH ⇒ opt_map ?? (get_indX_8_high_reg m t s)
                  (λindx.Some ? (tripleT ??? s indx cur_pc))

(* NO: solo lettura word *)
  | MODE_INHX0ADD ⇒ None ?
(* NO: solo lettura word *)
  | MODE_INHX1ADD ⇒ None ?
(* NO: solo lettura word *)
  | MODE_INHX2ADD ⇒ None ?

(* preleva 1 byte immediato *) 
   | MODE_IMM1 ⇒ mode_IMM1_load m t s cur_pc
(* NO: solo lettura word *)
   | MODE_IMM1EXT ⇒ None ?
(* NO: solo lettura word *)
   | MODE_IMM2 ⇒ None ?
(* preleva 1 byte da indirizzo diretto 1 byte *) 
   | MODE_DIR1 ⇒ mode_DIR1_load true m t s cur_pc
(* preleva 1 byte da indirizzo diretto 1 word *)
   | MODE_DIR2 ⇒ mode_DIR2_load true m t s cur_pc
(* preleva 1 byte da H:X *)
   | MODE_IX0  ⇒ mode_IX0_load true m t s cur_pc
(* preleva 1 byte da H:X+1 byte offset *)
   | MODE_IX1  ⇒ mode_IX1_load true m t s cur_pc
(* preleva 1 byte da H:X+1 word offset *)
   | MODE_IX2  ⇒ mode_IX2_load true m t s cur_pc
(* preleva 1 byte da SP+1 byte offset *)
   | MODE_SP1  ⇒ mode_SP1_load true m t s cur_pc
(* preleva 1 byte da SP+1 word offset *)
   | MODE_SP2  ⇒ mode_SP2_load true m t s cur_pc

(* come DIR1, chiamare scrittura per passo2: scrittura su DIR1 *)
   | MODE_DIR1_to_DIR1 ⇒ mode_DIR1_load true m t s cur_pc
(* come IMM1, chiamare scrittura per passo2: scrittura su DIR1 *)
   | MODE_IMM1_to_DIR1 ⇒ mode_IMM1_load m t s cur_pc
(* come IX0, chiamare scrittura per passo2: scrittura su DIR1 e X++ *)
   | MODE_IX0p_to_DIR1 ⇒ mode_IX0_load true m t s cur_pc
(* come DIR1, chiamare scrittura per passo2: scrittura su IX0 e X++ *)
   | MODE_DIR1_to_IX0p ⇒ mode_DIR1_load true m t s cur_pc

(* NO: solo lettura word/scrittura byte *)
   | MODE_INHA_and_IMM1 ⇒ None ?
(* NO: solo lettura word/scrittura byte *)     
   | MODE_INHX_and_IMM1 ⇒ None ?
(* NO: solo lettura word *) 
   | MODE_IMM1_and_IMM1 ⇒ None ?
(* NO: solo lettura word/scrittura byte *) 
   | MODE_DIR1_and_IMM1 ⇒ None ?
(* NO: solo lettura word/scrittura byte *) 
   | MODE_IX0_and_IMM1  ⇒ None ?
(* NO: solo lettura word *) 
   | MODE_IX0p_and_IMM1 ⇒ None ?
(* NO: solo lettura word/scrittura byte *) 
   | MODE_IX1_and_IMM1  ⇒ None ?
(* NO: solo lettura word *) 
   | MODE_IX1p_and_IMM1 ⇒ None ?
(* NO: solo lettura word/scrittura byte *) 
   | MODE_SP1_and_IMM1  ⇒ None ?

(* NO: solo scrittura byte *)
   | MODE_DIRn _          ⇒ None ?
(* NO: solo lettura word *)
   | MODE_DIRn_and_IMM1 _ ⇒ None ?
(* preleva 1 byte da 0000 0000 0000 xxxxb *)
   | MODE_TNY e           ⇒ opt_map ?? (memory_filter_read m t s 〈〈x0,x0〉:〈x0,e〉〉)
                             (λb.Some ? (tripleT ??? s b cur_pc))
(* preleva 1 byte da 0000 0000 000x xxxxb *)
   | MODE_SRT e           ⇒ opt_map ?? (memory_filter_read m t s 〈〈x0,x0〉:(byte8_of_bitrigesim e)〉)
                             (λb.Some ? (tripleT ??? s b cur_pc))
   ]
(* lettura di una word *)
  | false ⇒ λs:any_status m t.λcur_pc:word16.λi:instr_mode.match i with
(* NO: non ci sono indicazioni *)
   [ MODE_INH  ⇒ None ?
(* NO: solo lettura/scrittura byte *)
   | MODE_INHA ⇒ None ?
(* NO: solo lettura/scrittura byte *)
   | MODE_INHX ⇒ None ?
(* NO: solo lettura/scrittura byte *)
   | MODE_INHH ⇒ None ?

(* preleva 1 word immediato *) 
  | MODE_INHX0ADD ⇒ opt_map ?? (get_IX m t s)
                     (λw.Some ? (tripleT ??? s w cur_pc))
(* preleva 1 word immediato *) 
  | MODE_INHX1ADD ⇒ mode_IX1ADD_load m t s cur_pc
(* preleva 1 word immediato *) 
  | MODE_INHX2ADD ⇒ mode_IX2ADD_load m t s cur_pc

(* NO: solo lettura byte *)
   | MODE_IMM1 ⇒ None ?
(* preleva 1 word immediato *) 
   | MODE_IMM1EXT ⇒ mode_IMM1EXT_load m t s cur_pc
(* preleva 1 word immediato *) 
   | MODE_IMM2 ⇒ mode_IMM2_load m t s cur_pc
(* preleva 1 word da indirizzo diretto 1 byte *) 
   | MODE_DIR1 ⇒ mode_DIR1_load false m t s cur_pc
(* preleva 1 word da indirizzo diretto 1 word *) 
   | MODE_DIR2 ⇒ mode_DIR2_load false m t s cur_pc
(* preleva 1 word da H:X *)
   | MODE_IX0  ⇒ mode_IX0_load false m t s cur_pc
(* preleva 1 word da H:X+1 byte offset *)
   | MODE_IX1  ⇒ mode_IX1_load false m t s cur_pc
(* preleva 1 word da H:X+1 word offset *)
   | MODE_IX2  ⇒ mode_IX2_load false m t s cur_pc
(* preleva 1 word da SP+1 byte offset *)
   | MODE_SP1  ⇒ mode_SP1_load false m t s cur_pc
(* preleva 1 word da SP+1 word offset *)
   | MODE_SP2  ⇒ mode_SP2_load false m t s cur_pc

(* NO: solo lettura/scrittura byte *)
   | MODE_DIR1_to_DIR1 ⇒ None ?
(* NO: solo lettura/scrittura byte *)
   | MODE_IMM1_to_DIR1 ⇒ None ?
(* NO: solo lettura/scrittura byte *)
   | MODE_IX0p_to_DIR1 ⇒ None ?
(* NO: solo lettura/scrittura byte *)
   | MODE_DIR1_to_IX0p ⇒ None ?

(* preleva 2 byte, possibilita' modificare Io argomento *)
   | MODE_INHA_and_IMM1 ⇒ opt_map ?? (mode_IMM1_load m t s cur_pc)
                           (λS_immb_and_PC.match S_immb_and_PC with
                            [ tripleT _ immb cur_pc' ⇒
                             Some ? (tripleT ??? s 〈(get_acc_8_low_reg m t s):immb〉 cur_pc')])
(* preleva 2 byte, possibilita' modificare Io argomento *)
   | MODE_INHX_and_IMM1 ⇒ opt_map ?? (get_indX_8_low_reg m t s)
                           (λX_op.opt_map ?? (mode_IMM1_load m t s cur_pc)
                            (λS_immb_and_PC.match S_immb_and_PC with
                             [ tripleT _ immb cur_pc' ⇒
                              Some ? (tripleT ??? s 〈X_op:immb〉 cur_pc')]))
(* preleva 2 byte, NO possibilita' modificare Io argomento *)               
   | MODE_IMM1_and_IMM1 ⇒ opt_map ?? (mode_IMM1_load m t s cur_pc)
                           (λS_immb1_and_PC.match S_immb1_and_PC with
                            [ tripleT _ immb1 cur_pc' ⇒
                             opt_map ?? (mode_IMM1_load m t s cur_pc')
                              (λS_immb2_and_PC.match S_immb2_and_PC with
                               [ tripleT _ immb2 cur_pc'' ⇒
                                Some ? (tripleT ??? s 〈immb1:immb2〉 cur_pc'')])])
(* preleva 2 byte, possibilita' modificare Io argomento *)
   | MODE_DIR1_and_IMM1 ⇒ opt_map ?? (mode_DIR1_load true m t s cur_pc)
                           (λS_dirb_and_PC.match S_dirb_and_PC with
                            [ tripleT _ dirb cur_pc' ⇒
                             opt_map ?? (mode_IMM1_load m t s cur_pc')
                              (λS_immb_and_PC.match S_immb_and_PC with
                               [ tripleT _ immb cur_pc'' ⇒
                                Some ? (tripleT ??? s 〈dirb:immb〉 cur_pc'')])])
(* preleva 2 byte, possibilita' modificare Io argomento *)
   | MODE_IX0_and_IMM1  ⇒ opt_map ?? (mode_IX0_load true m t s cur_pc)
                           (λS_ixb_and_PC.match S_ixb_and_PC with
                            [ tripleT _ ixb cur_pc' ⇒
                             opt_map ?? (mode_IMM1_load m t s cur_pc')
                              (λS_immb_and_PC.match S_immb_and_PC with
                               [ tripleT _ immb cur_pc'' ⇒
                                Some ? (tripleT ??? s 〈ixb:immb〉 cur_pc'')])])
(* preleva 2 byte, H:X++, NO possibilita' modificare Io argomento *)
   | MODE_IX0p_and_IMM1 ⇒ opt_map ?? (mode_IX0_load true m t s cur_pc)
                           (λS_ixb_and_PC.match S_ixb_and_PC with
                            [ tripleT _ ixb cur_pc' ⇒
                             opt_map ?? (mode_IMM1_load m t s cur_pc')
                              (λS_immb_and_PC.match S_immb_and_PC with
                               [ tripleT _ immb cur_pc'' ⇒
                                (* H:X++ *)
                                opt_map ?? (aux_inc_indX_16 m t s)
                                 (λs'.Some ? (tripleT ??? s' 〈ixb:immb〉 cur_pc''))])])
(* preleva 2 byte, possibilita' modificare Io argomento *)
   | MODE_IX1_and_IMM1  ⇒ opt_map ?? (mode_IX1_load true m t s cur_pc)
                           (λS_ixb_and_PC.match S_ixb_and_PC with
                            [ tripleT _ ixb cur_pc' ⇒
                             opt_map ?? (mode_IMM1_load m t s cur_pc')
                              (λS_immb_and_PC.match S_immb_and_PC with
                               [ tripleT _ immb cur_pc'' ⇒
                                Some ? (tripleT ??? s 〈ixb:immb〉 cur_pc'')])])
(* preleva 2 byte, H:X++, NO possibilita' modificare Io argomento *)
   | MODE_IX1p_and_IMM1 ⇒ opt_map ?? (mode_IX1_load true m t s cur_pc)
                           (λS_ixb_and_PC.match S_ixb_and_PC with
                            [ tripleT _ ixb cur_pc' ⇒
                             opt_map ?? (mode_IMM1_load m t s cur_pc')
                              (λS_immb_and_PC.match S_immb_and_PC with
                               [ tripleT _ immb cur_pc'' ⇒
                                (* H:X++ *)
                                opt_map ?? (aux_inc_indX_16 m t s)
                                 (λs'.Some ? (tripleT ??? s' 〈ixb:immb〉 cur_pc''))])])
(* preleva 2 byte, possibilita' modificare Io argomento *)
   | MODE_SP1_and_IMM1  ⇒ opt_map ?? (mode_SP1_load true m t s cur_pc)
                           (λS_spb_and_PC.match S_spb_and_PC with
                            [ tripleT _ spb cur_pc' ⇒
                             opt_map ?? (mode_IMM1_load m t s cur_pc')
                              (λS_immb_and_PC.match S_immb_and_PC with
                               [ tripleT _ immb cur_pc'' ⇒
                                Some ? (tripleT ??? s 〈spb:immb〉 cur_pc'')])])

(* NO: solo scrittura byte *)
   | MODE_DIRn _            ⇒ None ?
(* preleva 2 byte, il primo e' filtrato per azzerare tutti i bit tranne n-simo *)
   | MODE_DIRn_and_IMM1 msk ⇒ opt_map ?? (mode_DIR1n_load m t s cur_pc msk)
                               (λS_dirbn_and_PC.match S_dirbn_and_PC with
                                [ tripleT _ dirbn cur_pc'   ⇒
                                 opt_map ?? (mode_IMM1_load m t s cur_pc')
                                  (λS_immb_and_PC.match S_immb_and_PC with
                                   [ tripleT _ immb cur_pc'' ⇒
                                     Some ? (tripleT ??? s 〈〈x0,match dirbn with [ true ⇒ x1 | false ⇒ x0 ]〉:immb〉 cur_pc'') ])])
(* NO: solo lettura/scrittura byte *)
   | MODE_TNY _             ⇒ None ?
(* NO: solo lettura/scrittura byte *)
   | MODE_SRT _             ⇒ None ?
   ]
  ].

(* **************************************** *)
(* raccordo di tutte le possibili scritture *)
(* **************************************** *)

(* tutte le modalita' di scrittura: true=writeb, false=writew *)
definition multi_mode_write ≝
λbyteflag:bool.λm:mcu_type.λt:memory_impl.match byteflag
 return λbyteflag:bool.any_status m t → word16 → instr_mode →
  match byteflag with [ true ⇒ byte8 | false ⇒ word16 ] →
  option (Prod (any_status m t) word16) with
 (* scrittura di un byte *)
 [ true ⇒ λs:any_status m t.λcur_pc:word16.λi:instr_mode.λwriteb:byte8.match i with
(* NO: non ci sono indicazioni *)
  [ MODE_INH        ⇒ None ?
(* scrive A *)
  | MODE_INHA       ⇒ Some ? (pair ?? (set_acc_8_low_reg m t s writeb) cur_pc)
(* scrive X *)
  | MODE_INHX       ⇒ opt_map ?? (set_indX_8_low_reg m t s writeb)
                      (λtmps.Some ? (pair ?? tmps cur_pc)) 
(* scrive H *)
  | MODE_INHH       ⇒ opt_map ?? (set_indX_8_high_reg m t s writeb)
                       (λtmps.Some ? (pair ?? tmps cur_pc)) 

(* NO: solo lettura word *)
  | MODE_INHX0ADD ⇒ None ?
(* NO: solo lettura word *)
  | MODE_INHX1ADD ⇒ None ?
(* NO: solo lettura word *)
  | MODE_INHX2ADD ⇒ None ?

(* NO: solo lettura byte *)
  | MODE_IMM1       ⇒ None ?
(* NO: solo lettura word *)
  | MODE_IMM1EXT    ⇒ None ?
(* NO: solo lettura word *)
  | MODE_IMM2       ⇒ None ?
(* scrive 1 byte su indirizzo diretto 1 byte *)
  | MODE_DIR1       ⇒ mode_DIR1_write true m t s cur_pc writeb
(* scrive 1 byte su indirizzo diretto 1 word *)
  | MODE_DIR2       ⇒ mode_DIR2_write true m t s cur_pc writeb
(* scrive 1 byte su H:X *)
  | MODE_IX0        ⇒ mode_IX0_write true m t s cur_pc writeb
(* scrive 1 byte su H:X+1 byte offset *)
  | MODE_IX1        ⇒ mode_IX1_write true m t s cur_pc writeb
(* scrive 1 byte su H:X+1 word offset *)
  | MODE_IX2        ⇒ mode_IX2_write true m t s cur_pc writeb
(* scrive 1 byte su SP+1 byte offset *)
  | MODE_SP1        ⇒ mode_SP1_write true m t s cur_pc writeb
(* scrive 1 byte su SP+1 word offset *)
  | MODE_SP2        ⇒ mode_SP2_write true m t s cur_pc writeb

(* passo2: scrittura su DIR1, passo1: lettura da DIR1 *)
  | MODE_DIR1_to_DIR1   ⇒ mode_DIR1_write true m t s cur_pc writeb
(* passo2: scrittura su DIR1, passo1: lettura da IMM1 *)
  | MODE_IMM1_to_DIR1   ⇒ mode_DIR1_write true m t s cur_pc writeb
(* passo2: scrittura su DIR1 e X++, passo1: lettura da IX0 *)
  | MODE_IX0p_to_DIR1   ⇒ opt_map ?? (mode_DIR1_write true m t s cur_pc writeb)
                           (λS_and_PC.match S_and_PC with [ pair S_op PC_op ⇒
                            (* H:X++ *)
                            opt_map ?? (aux_inc_indX_16 m t S_op)
                             (λS_op'.Some ? (pair ?? S_op' PC_op))])
(* passo2: scrittura su IX0 e X++, passo1: lettura da DIR1 *)
  | MODE_DIR1_to_IX0p   ⇒ opt_map ?? (mode_IX0_write true m t s cur_pc writeb)
                           (λS_and_PC.match S_and_PC with [ pair S_op PC_op ⇒
                            (* H:X++ *)
                            opt_map ?? (aux_inc_indX_16 m t S_op)
                             (λS_op'.Some ? (pair ?? S_op' PC_op))])

(* dopo aver prelevato 2 byte la possibilita' modificare Io argomento = INHA *)
  | MODE_INHA_and_IMM1 ⇒ Some ? (pair ?? (set_acc_8_low_reg m t s writeb) cur_pc)
(* dopo aver prelevato 2 byte la possibilita' modificare Io argomento = INHX *)  
  | MODE_INHX_and_IMM1 ⇒ opt_map ?? (set_indX_8_low_reg m t s writeb)
                           (λtmps.Some ? (pair ?? tmps cur_pc)) 
(* NO: solo lettura word *) 
  | MODE_IMM1_and_IMM1 ⇒ None ?
(* dopo aver prelevato 2 byte la possibilita' modificare Io argomento = DIR1 *) 
  | MODE_DIR1_and_IMM1 ⇒ mode_DIR1_write true m t s cur_pc writeb
(* dopo aver prelevato 2 byte la possibilita' modificare Io argomento = IX0 *)
  | MODE_IX0_and_IMM1  ⇒ mode_IX0_write true m t s cur_pc writeb
(* NO: solo lettura word *) 
  | MODE_IX0p_and_IMM1 ⇒ None ?
(* dopo aver prelevato 2 byte la possibilita' modificare Io argomento = IX1 *)
  | MODE_IX1_and_IMM1  ⇒ mode_IX1_write true m t s cur_pc writeb
(* NO: solo lettura word *) 
  | MODE_IX1p_and_IMM1 ⇒ None ?
(* dopo aver prelevato 2 byte la possibilita' modificare Io argomento = SP1 *)
  | MODE_SP1_and_IMM1  ⇒ mode_SP1_write true m t s cur_pc writeb

(* scrive 1 byte, ma la scrittura avviene solo per n-simo bit = leggi/modifica bit/scrivi *)
  | MODE_DIRn msk ⇒ mode_DIR1n_write m t s cur_pc msk (getn_array8T msk bool (bits_of_byte8 writeb))   
(* NO: solo lettura word *)
  | MODE_DIRn_and_IMM1 _ ⇒ None ?
(* scrive 1 byte su 0000 0000 0000 xxxxb *)
  | MODE_TNY e ⇒ opt_map ?? (memory_filter_write m t s 〈〈x0,x0〉:〈x0,e〉〉 writeb)
                   (λtmps.Some ? (pair ?? tmps cur_pc))
(* scrive 1 byte su 0000 0000 000x xxxxb *)
  | MODE_SRT e ⇒ opt_map ?? (memory_filter_write m t s 〈〈x0,x0〉:(byte8_of_bitrigesim e)〉 writeb)
                      (λtmps.Some ? (pair ?? tmps cur_pc)) ]
 (* scrittura di una word *)
 | false ⇒ λs:any_status m t.λcur_pc:word16.λi:instr_mode.λwritew:word16.match i with
(* NO: non ci sono indicazioni *)
  [ MODE_INH        ⇒ None ?
(* NO: solo lettura/scrittura byte *)
  | MODE_INHA       ⇒ None ?
(* NO: solo lettura/scrittura byte *)
  | MODE_INHX       ⇒ None ?
(* NO: solo lettura/scrittura byte *)
  | MODE_INHH       ⇒ None ?

(* NO: solo lettura word *)
  | MODE_INHX0ADD ⇒ None ?
(* NO: solo lettura word *)
  | MODE_INHX1ADD ⇒ None ?
(* NO: solo lettura word *)
  | MODE_INHX2ADD ⇒ None ?

(* NO: solo lettura byte *)
  | MODE_IMM1       ⇒ None ?
(* NO: solo lettura word *)
  | MODE_IMM1EXT    ⇒ None ?
(* NO: solo lettura word *)
  | MODE_IMM2       ⇒ None ?
(* scrive 1 word su indirizzo diretto 1 byte *) 
  | MODE_DIR1       ⇒ mode_DIR1_write false m t s cur_pc writew
(* scrive 1 word su indirizzo diretto 1 word *)
  | MODE_DIR2       ⇒ mode_DIR2_write false m t s cur_pc writew
(* scrive 1 word su H:X *)
  | MODE_IX0        ⇒ mode_IX0_write false m t s cur_pc writew
(* scrive 1 word su H:X+1 byte offset *)
  | MODE_IX1        ⇒ mode_IX1_write false m t s cur_pc writew
(* scrive 1 word su H:X+1 word offset *)
  | MODE_IX2        ⇒ mode_IX2_write false m t s cur_pc writew
(* scrive 1 word su SP+1 byte offset *)
  | MODE_SP1        ⇒ mode_SP1_write false m t s cur_pc writew
(* scrive 1 word su SP+1 word offset *)
  | MODE_SP2        ⇒ mode_SP2_write false m t s cur_pc writew

(* NO: solo lettura/scrittura byte *)
  | MODE_DIR1_to_DIR1 ⇒ None ?
(* NO: solo lettura/scrittura byte *)
  | MODE_IMM1_to_DIR1 ⇒ None ?
(* NO: solo lettura/scrittura byte *)
  | MODE_IX0p_to_DIR1 ⇒ None ?
(* NO: solo lettura/scrittura byte *)
  | MODE_DIR1_to_IX0p ⇒ None ?

(* NO: solo lettura word/scrittura byte *)
  | MODE_INHA_and_IMM1 ⇒ None ?
(* NO: solo lettura word/scrittura byte *)     
  | MODE_INHX_and_IMM1 ⇒ None ?
(* NO: solo lettura word *) 
  | MODE_IMM1_and_IMM1 ⇒ None ?
(* NO: solo lettura word/scrittura byte *) 
  | MODE_DIR1_and_IMM1 ⇒ None ?
(* NO: solo lettura word/scrittura byte *) 
  | MODE_IX0_and_IMM1  ⇒ None ?
(* NO: solo lettura word *) 
  | MODE_IX0p_and_IMM1 ⇒ None ?
(* NO: solo lettura word/scrittura byte *)
  | MODE_IX1_and_IMM1  ⇒ None ?
(* NO: solo lettura word *) 
  | MODE_IX1p_and_IMM1 ⇒ None ?
(* NO: solo lettura word/scrittura byte *) 
  | MODE_SP1_and_IMM1  ⇒ None ?

(* NO: solo scrittura byte *)
  | MODE_DIRn _          ⇒ None ?
(* NO: solo lettura word *)
  | MODE_DIRn_and_IMM1 _ ⇒ None ?
(* NO: solo lettura/scrittura byte *)
  | MODE_TNY _           ⇒ None ?
(* NO: solo lettura/scrittura byte *)
  | MODE_SRT _           ⇒ None ?
  ]
 ].
