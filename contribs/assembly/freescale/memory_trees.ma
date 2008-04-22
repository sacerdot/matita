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

include "freescale/memory_struct.ma".

(* ********************* *)
(* MEMORIA E DESCRITTORE *)
(* ********************* *)

(* tutta la memoria non installata *)
definition mt_out_of_bound_memory ≝
let lev4 ≝ array_16T ? 
           MEM_OUT_OF_BOUND MEM_OUT_OF_BOUND MEM_OUT_OF_BOUND MEM_OUT_OF_BOUND
           MEM_OUT_OF_BOUND MEM_OUT_OF_BOUND MEM_OUT_OF_BOUND MEM_OUT_OF_BOUND
           MEM_OUT_OF_BOUND MEM_OUT_OF_BOUND MEM_OUT_OF_BOUND MEM_OUT_OF_BOUND
           MEM_OUT_OF_BOUND MEM_OUT_OF_BOUND MEM_OUT_OF_BOUND MEM_OUT_OF_BOUND
           in
let lev3 ≝ array_16T ?
           lev4 lev4 lev4 lev4 lev4 lev4 lev4 lev4
           lev4 lev4 lev4 lev4 lev4 lev4 lev4 lev4
           in
let lev2 ≝ array_16T ?
           lev3 lev3 lev3 lev3 lev3 lev3 lev3 lev3
           lev3 lev3 lev3 lev3 lev3 lev3 lev3 lev3
           in
let lev1 ≝ array_16T ?
           lev2 lev2 lev2 lev2 lev2 lev2 lev2 lev2
           lev2 lev2 lev2 lev2 lev2 lev2 lev2 lev2
           in
lev1.

(* tutta la memoria a 0 *)
definition mt_zero_memory ≝
let lev4 ≝ array_16T ? 
           (mk_byte8 x0 x0) (mk_byte8 x0 x0) (mk_byte8 x0 x0) (mk_byte8 x0 x0)
           (mk_byte8 x0 x0) (mk_byte8 x0 x0) (mk_byte8 x0 x0) (mk_byte8 x0 x0)
           (mk_byte8 x0 x0) (mk_byte8 x0 x0) (mk_byte8 x0 x0) (mk_byte8 x0 x0)
           (mk_byte8 x0 x0) (mk_byte8 x0 x0) (mk_byte8 x0 x0) (mk_byte8 x0 x0)
           in
let lev3 ≝ array_16T ?
           lev4 lev4 lev4 lev4 lev4 lev4 lev4 lev4
           lev4 lev4 lev4 lev4 lev4 lev4 lev4 lev4
           in
let lev2 ≝ array_16T ?
           lev3 lev3 lev3 lev3 lev3 lev3 lev3 lev3
           lev3 lev3 lev3 lev3 lev3 lev3 lev3 lev3
           in
let lev1 ≝ array_16T ?
           lev2 lev2 lev2 lev2 lev2 lev2 lev2 lev2
           lev2 lev2 lev2 lev2 lev2 lev2 lev2 lev2
           in
lev1.

(* visita di un albero da 64KB di elementi: ln16(65536)=4 passaggi *)
definition mt_visit ≝
λT:Type.λdata:Prod16T (Prod16T (Prod16T (Prod16T T))).λaddr:word16.
 match addr with
  [ mk_word16 wh wl ⇒
 getn_array16T (b8l wl) ?
  (getn_array16T (b8h wl) ?
   (getn_array16T (b8l wh) ?
    (getn_array16T (b8h wh) ? data))) ].

(* scrittura di un elemento in un albero da 64KB *)
definition mt_update ≝
λT:Type.λdata:Prod16T (Prod16T (Prod16T (Prod16T T))).λaddr:word16.λv:T.
 match addr with
  [ mk_word16 wh wl ⇒
 let lev2 ≝ getn_array16T (b8h wh) ? data in
 let lev3 ≝ getn_array16T (b8l wh) ? lev2 in
 let lev4 ≝ getn_array16T (b8h wl) ? lev3 in
 setn_array16T (b8h wh) ? data
  (setn_array16T (b8l wh) ? lev2
   (setn_array16T (b8h wl) ? lev3
    (setn_array16T (b8l wl) T lev4 v))) ].

(* scrittura di un range in un albero da 64KB *)
definition mt_update_ranged ≝
λT:Type.λdata:Prod16T (Prod16T (Prod16T (Prod16T T))).λi,s:word16.λv:T.
 (* ok i≤s *)
 match le_w16 i s with
  [ true ⇒
 match i with
  [ mk_word16 ih il ⇒
 match s with
  [ mk_word16 sh sl ⇒
 let aux_4 ≝ Prod16T T in
 let aux_3 ≝ Prod16T (Prod16T T) in
 let aux_2 ≝ Prod16T (Prod16T (Prod16T T)) in

 let ilev2 ≝ getn_array16T (b8h ih) aux_2 data in
 let ilev3 ≝ getn_array16T (b8l ih) aux_3 ilev2 in
 let ilev4 ≝ getn_array16T (b8h il) aux_4 ilev3 in

 let slev2 ≝ getn_array16T (b8h sh) aux_2 data in
 let slev3 ≝ getn_array16T (b8l sh) aux_3 slev2 in
 let slev4 ≝ getn_array16T (b8h sl) aux_4 slev3 in

 let vlev4 ≝ array_16T T v v v v v v v v v v v v v v v v in
 let vlev3 ≝ array_16T aux_4 vlev4 vlev4 vlev4 vlev4 vlev4 vlev4 vlev4 vlev4
                             vlev4 vlev4 vlev4 vlev4 vlev4 vlev4 vlev4 vlev4 in
 let vlev2 ≝ array_16T aux_3 vlev3 vlev3 vlev3 vlev3 vlev3 vlev3 vlev3 vlev3
                             vlev3 vlev3 vlev3 vlev3 vlev3 vlev3 vlev3 vlev3 in

 match eq_ex (b8h ih) (b8h sh) with
  [ true ⇒ match eq_ex (b8l ih) (b8l sh) with
   [ true ⇒ match eq_ex (b8h il) (b8h sl) with
    (* caso 0x...(X) a 0x...(Y) *)
    [ true ⇒ setn_array16T (b8h ih) aux_2 data
              (setn_array16T (b8l ih) aux_3 ilev2
               (setn_array16T (b8h il) aux_4 ilev3
                (* cambio a partire da livello 4 *)
                (setmn_array16T (b8l il) (b8l sl) T ilev4 v))) (* ...X,...Y *)
    (* caso 0x..(X1)(X2) a 0x..(Y1)(Y2) *)
    | false ⇒ setn_array16T (b8h ih) aux_2 data
               (setn_array16T (b8l ih) aux_3 ilev2
                (* cambio a partire da livello 3 *)
                (setn_array16T (b8h sl) aux_4 (* ..(Y1)0,..(Y1)(Y2) *)
                 (setmn_array16T_succ_pred (b8h il) (b8h sl) aux_4 (* ..(X1+1).,..(Y1-1). *)
                  (setn_array16T (b8h il) aux_4 ilev3
                   (setmn_array16T (b8l il) xF T ilev4 v)) (* ..(X1)(X2),..(X1)F *)
                  vlev4)
                 (setmn_array16T x0 (b8l sl) T slev4 v))) ]
   (* caso 0x.(X1)(X2)(X3) a 0x..(Y1)(Y2)(Y3) *)
   | false ⇒ setn_array16T (b8h ih) aux_2 data
              (* cambio a partire da livello 2 *)
              (setn_array16T (b8l sh) aux_3
               (setmn_array16T_succ_pred (b8l ih) (b8l sh) aux_3 (* .(X1+1)..,.(Y1-1).. *)
                (setn_array16T (b8l ih) aux_3 ilev2
                 (setmn_array16T_succ (b8h il) aux_4 (* .(X1)(X2+1).,.(X1)F. *)
                  (setn_array16T (b8h il) aux_4 ilev3
                   (setmn_array16T (b8l il) xF T ilev4 v)) (* .(X1)(X2)(X3),.(X1)(X2)F *)
                  vlev4))
                vlev3)
               (setmn_array16T_pred (b8h sl) aux_4 (* .(Y1)0.,.(Y1)(Y2-1). *)
                (setn_array16T (b8h sl) aux_4 slev3
                 (setmn_array16T x0 (b8l sl) T slev4 v)) (* .(Y1)(Y2)0,.(Y1)(Y2)(Y3) *)
                vlev4))
   ]
  (* caso 0x(X1)(X2)(X3)(X4) a 0x(Y1)(Y2)(Y3)(Y4) *)
  | false ⇒ setn_array16T (b8h sh) aux_2
             (setmn_array16T_succ_pred (b8h ih) (b8h sh) aux_2 (* (X+1)...,(Y-1)... *)
              (setn_array16T (b8h ih) aux_2 data
               (setmn_array16T_succ (b8l ih) aux_3 (* (X1)(X2+1)..,(X1)F.. *)
                (setn_array16T (b8l ih) aux_3 ilev2
                 (setmn_array16T_succ (b8h il) aux_4 (* (X1)(X2)(X3+1).,(X1)(X2)F. *)
                  (setn_array16T (b8h il) aux_4 ilev3
                   (setmn_array16T (b8l il) xF T ilev4 v)) (* (X1)(X2)(X3)(X4),(X1)(X2)(X3)F *)
                  vlev4))
                vlev3))
               vlev2)
             (setmn_array16T_pred (b8l sh) aux_3 (* (Y1)0..,(Y1)(Y2-1).. *)
              (setn_array16T (b8l sh) aux_3 slev2
               (setmn_array16T_pred (b8h sl) aux_4 (* (Y1)(Y2)0.,(Y1)(Y2)(Y3-1). *)
                (setn_array16T (b8h sl) aux_4 slev3
                 (setmn_array16T x0 (b8l sl) T slev4 v)) (* (Y1)(Y2)(Y3)0,(Y1)(Y2)(Y3)(Y4) *)
                vlev4))
              vlev3) ]]]
 (* no i>s *)
 | false ⇒ data
 ].
 
definition mt_chk_get ≝
λchk:Prod16T (Prod16T (Prod16T (Prod16T memory_type))).λaddr:word16.
 match mt_visit ? chk addr with
 [ MEM_READ_ONLY ⇒ array_8T ? MEM_READ_ONLY MEM_READ_ONLY MEM_READ_ONLY MEM_READ_ONLY MEM_READ_ONLY MEM_READ_ONLY MEM_READ_ONLY MEM_READ_ONLY
 | MEM_READ_WRITE ⇒ array_8T ? MEM_READ_WRITE MEM_READ_WRITE MEM_READ_WRITE MEM_READ_WRITE MEM_READ_WRITE MEM_READ_WRITE MEM_READ_WRITE MEM_READ_WRITE
 | MEM_OUT_OF_BOUND ⇒ array_8T ? MEM_OUT_OF_BOUND MEM_OUT_OF_BOUND MEM_OUT_OF_BOUND MEM_OUT_OF_BOUND MEM_OUT_OF_BOUND MEM_OUT_OF_BOUND MEM_OUT_OF_BOUND MEM_OUT_OF_BOUND
 ].

(* scrivi controllando il tipo di memoria *)
definition mt_mem_update ≝
λmem:Prod16T (Prod16T (Prod16T (Prod16T byte8))).
λchk:Prod8T memory_type.
λaddr:word16.λv:byte8.
 match getn_array8T o0 ? chk with
  (* ROM? ok, ma il valore viene perso *)
  [ MEM_READ_ONLY ⇒ Some ? mem
  (* RAM? ok *)
  | MEM_READ_WRITE ⇒ Some ? (mt_update ? mem addr v)
  (* NON INSTALLATA? no *)
  | MEM_OUT_OF_BOUND ⇒ None ? ].  

(* leggi controllando il tipo di memoria *)
definition mt_mem_read ≝
λmem:Prod16T (Prod16T (Prod16T (Prod16T byte8))).
λchk:Prod16T (Prod16T (Prod16T (Prod16T memory_type))).
λaddr:word16.
 match  mt_visit ? chk addr with
  [ MEM_READ_ONLY ⇒ Some ? (mt_visit ? mem addr)
  | MEM_READ_WRITE ⇒ Some ? (mt_visit ? mem addr)
  | MEM_OUT_OF_BOUND ⇒ None ? ].

(* ************************** *)
(* CARICAMENTO PROGRAMMA/DATI *)
(* ************************** *)

(* carica a paratire da addr, scartando source (pescando da old_mem) se si supera 0xFFFF... *)
let rec mt_load_from_source_at (old_mem:Prod16T (Prod16T (Prod16T (Prod16T byte8))))
                               (source:list byte8) (addr:word16) on source ≝
match source with
 (* fine di source: carica da old_mem *)
 [ nil ⇒ old_mem
 | cons hd tl ⇒ match lt_w16 addr 〈〈xF,xF〉:〈xF,xF〉〉 with
  (* non supera 0xFFFF, ricorsione *)
  [ true ⇒ mt_load_from_source_at (mt_update ? old_mem addr hd) tl (plus_w16nc addr 〈〈x0,x0〉:〈x0,x1〉〉)
  (* supera 0xFFFF, niente ricorsione *)
  | false ⇒ mt_update ? old_mem addr hd
  ]].

(* ********************** *)
(* TEOREMI/LEMMMI/ASSIOMI *)
(* ********************** *)

(* lettura da locazione diversa da quella in cui scrivo e' vecchio *)
(* NB: sembra corretto, ma 2^32 casi!!! *)
(*
lemma ok_mt_update :
 forall_word16 (λaddr1.
 forall_word16 (λaddr2.
  (eq_w16 addr1 addr2) ⊙
  (eq_b8 (mt_visit ? (mt_update ? mt_zero_memory addr1 〈xF,xF〉) addr2)
         (mk_byte8 x0 x0))))
  = true.
 reflexivity.
qed.
*)

(* verifica scrittura di range *)
(* NB: sembra corretto, ma 2^48 casi!!! *)
(*
lemma ok_mt_update_ranged :
 forall_word16 (λaddr1.
 forall_word16 (λaddr2.
 forall_word16 (λaddr3.
  (in_range addr3 addr1 addr2) ⊙
  (eq_b8 (mt_visit ? (mt_update_ranged ? mt_zero_memory addr1 addr2 〈xF,xF〉) addr3)
         (mk_byte8 x0 x0)))))
  = true.
 reflexivity.
qed.
*)
