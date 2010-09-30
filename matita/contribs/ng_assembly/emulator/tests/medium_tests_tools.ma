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

include "emulator/multivm/multivm.ma".

(* ********* *)
(* INDIRIZZI *)
(* ********* *)

(* specifico per MC9S08GB60 in modo da caricare codice compilato da CodeWarrior *)
(* l'obbiettivo e' dimostrare una routine scritta in C *)
(* passo 1 e' formalizzare l'uso di 3Kb dei 4Kb di RAM [0x0100-0x0CFF] *)
ndefinition dTest_HCS08_RAM ≝ 〈〈x0,x1〉:〈x0,x0〉〉.
ndefinition dTest_HCS08_prog ≝ 〈〈x1,x8〉:〈xC,x8〉〉.

(* ***** *)
(* TOOLS *)
(* ***** *)

(* visita di un albero da 256B di elementi: ln16(256)=2 passaggi *)
ndefinition dTest_visit ≝
λdata:Array16T (Array16T (list byte8)).λaddr:byte8.
 getn_array16T (cnL ? addr) ?
  (getn_array16T (cnH ? addr) ? data).

(* scrittura di un elemento in un albero da 256B *)
ndefinition dTest_update ≝
λdata:Array16T (Array16T (list byte8)).λaddr:byte8.λv:list byte8.
 let lev2 ≝ getn_array16T (cnH ? addr) ? data in
 setn_array16T (cnH ? addr) ? data
  (setn_array16T (cnL ? addr) ? lev2 v) .

(* array a 0 *)
ndefinition dTest_zero_array ≝
let elem ≝ nil byte8 in
let lev2 ≝ mk_Array16T ? 
           elem elem elem elem elem elem elem elem
           elem elem elem elem elem elem elem elem
           in
let lev1 ≝ mk_Array16T ?
           lev2 lev2 lev2 lev2 lev2 lev2 lev2 lev2
           lev2 lev2 lev2 lev2 lev2 lev2 lev2 lev2
           in
lev1.

(* incrementa n-simo elemento *)
ndefinition dTest_inc ≝
λdata:Array16T (Array16T (list byte8)).λaddr:byte8.
 dTest_update data addr ((dTest_visit data addr)@[ addr ]).

(* costruisce una lista a partire dai conteggi per elemento *)
ndefinition dTest_build_list_from_count ≝
λdata:Array16T (Array16T (list byte8)).
 let aux1 ≝ λparam1:Array16T (list byte8).
  match param1 with
   [ mk_Array16T e00 e01 e02 e03 e04 e05 e06 e07 e08 e09 e10 e11 e12 e13 e14 e15 ⇒
    e00@e01@e02@e03@e04@e05@e06@e07@e08@e09@e10@e11@e12@e13@e14@e15 ] in
 let aux2 ≝ λparam2:Array16T (Array16T (list byte8)).
  match param2 with
   [ mk_Array16T e00 e01 e02 e03 e04 e05 e06 e07 e08 e09 e10 e11 e12 e13 e14 e15 ⇒
    (aux1 e00)@(aux1 e01)@(aux1 e02)@(aux1 e03)@(aux1 e04)@(aux1 e05)@(aux1 e06)@(aux1 e07)@
    (aux1 e08)@(aux1 e09)@(aux1 e10)@(aux1 e11)@(aux1 e12)@(aux1 e13)@(aux1 e14)@(aux1 e15) ] in
 aux2 data.

(* ci sono ora tutti gli elementi per definire l'ordinamento *)
(* di una lista di byte8 secondo il counting sort *)
nlet rec byte8_list_ordering_aux (source:list byte8) (count:Array16T (Array16T (list byte8))) on source ≝
 match source with
  [ nil ⇒ dTest_build_list_from_count count
  | cons hd tl ⇒ byte8_list_ordering_aux tl (dTest_inc count hd)
  ].

ndefinition byte8_list_ordering ≝
λsource:list byte8.byte8_list_ordering_aux source dTest_zero_array.

(* strlen esadecimale limitato, considerando overflow! *)
nlet rec byte8_bounded_strlen_aux (source:list byte8) (count,limit:word16) on source ≝
 match source with
  [ nil ⇒ True
  | cons _ tl ⇒ match eq_w16 count 〈〈xF,xF〉:〈xF,xF〉〉 with
   [ true ⇒ False
   | false ⇒ match le_w16 (succ_w16 count) limit with
    [ true ⇒ byte8_bounded_strlen_aux tl (succ_w16 count) limit
    | false ⇒ False
    ]
   ]
  ].

ndefinition byte8_bounded_strlen ≝
λsource:list byte8.λlimit:word16.
 byte8_bounded_strlen_aux source 〈〈x0,x0〉:〈x0,x0〉〉 limit.

(* strlen esadecimale normale *)
nlet rec byte8_strlen_aux (source:list byte8) (count:word16) on source ≝
 match source with
  [ nil ⇒ count
  | cons _ tl ⇒ byte8_strlen_aux tl (succ_w16 count)
  ].

ndefinition byte8_strlen ≝
λsource:list byte8.
 byte8_strlen_aux source 〈〈x0,x0〉:〈x0,x0〉〉.

(* hex dump: memory -> list byte8 *)
nlet rec byte8_hexdump_aux (t:memory_impl) (mem:aux_mem_type t) (inf:word32) (count:nat) (out:list byte8) on count ≝
 match count with
  [ O ⇒ out
  | S n ⇒ byte8_hexdump_aux t mem (succ_w32 inf) n (out@[ mem_read_abs t mem inf ])
  ].

ndefinition byte8_hexdump ≝
λt:memory_impl.λmem:aux_mem_type t.λinf:word32.λcount:nat.
 byte8_hexdump_aux t mem inf count [].

(* ************* *)
(* TEST PATTERNS *)
(* ************* *)

(* lista di 3072 numeri random generati da Mathematica, in blocchi da 32 *)
ndefinition dTest_random_ex00 ≝
[〈x8,x1〉;〈x5,xE〉;〈x7,x6〉;〈xD,x1〉;〈x7,x5〉;〈x1,x0〉;〈x8,x5〉;〈x9,x0〉;〈x1,xF〉;〈x1,x2〉;〈xE,x2〉;〈x3,xC〉;〈x1,xD〉;〈x0,x6〉;〈x3,xC〉;〈xD,x1〉
;〈x8,x3〉;〈xE,xB〉;〈x7,x2〉;〈x1,xF〉;〈x9,x0〉;〈xF,x0〉;〈x4,x7〉;〈xA,x3〉;〈xD,x0〉;〈x4,x6〉;〈xC,x5〉;〈x3,x2〉;〈xC,x9〉;〈x0,xB〉;〈x1,xB〉;〈x7,x3〉 ].

ndefinition dTest_random_ex01 ≝
[〈x1,x1〉;〈xA,xF〉;〈xD,x2〉;〈xB,xF〉;〈x0,xB〉;〈xB,xC〉;〈x0,x8〉;〈xE,x5〉;〈xF,xE〉;〈xA,xC〉;〈xF,xC〉;〈x9,x4〉;〈x3,x4〉;〈x8,x8〉;〈x2,x8〉;〈xD,xB〉
;〈xD,x3〉;〈x3,xD〉;〈x3,x8〉;〈x6,xA〉;〈x4,xD〉;〈x7,x4〉;〈x4,x9〉;〈x7,xE〉;〈x6,xF〉;〈x4,xD〉;〈x3,xD〉;〈x3,xA〉;〈xC,x2〉;〈xD,x3〉;〈x3,x6〉;〈x7,x0〉 ].

ndefinition dTest_random_ex02 ≝
[〈x8,x0〉;〈xC,x9〉;〈x3,xB〉;〈x5,x2〉;〈x8,xF〉;〈x1,xE〉;〈x8,x4〉;〈x5,x2〉;〈x2,xD〉;〈xA,xF〉;〈x1,xB〉;〈x0,x1〉;〈x3,x5〉;〈x7,x2〉;〈x1,x0〉;〈x0,x7〉
;〈x5,xD〉;〈xA,xB〉;〈xE,x0〉;〈x7,x6〉;〈xB,xD〉;〈x3,xC〉;〈x0,xD〉;〈xC,xE〉;〈xB,x7〉;〈x9,xD〉;〈xA,x9〉;〈xF,x3〉;〈xC,x1〉;〈x9,x3〉;〈x8,xC〉;〈x4,xE〉 ].

ndefinition dTest_random_ex03 ≝
[〈xF,x8〉;〈xC,x3〉;〈x1,x3〉;〈x3,xA〉;〈xA,x2〉;〈xB,xD〉;〈x1,x0〉;〈x9,xB〉;〈x5,xC〉;〈xC,x8〉;〈xE,x5〉;〈xC,x8〉;〈xA,x6〉;〈xF,xB〉;〈x1,x3〉;〈xC,x8〉
;〈x6,x4〉;〈x0,x9〉;〈xD,x6〉;〈xD,x7〉;〈x3,x9〉;〈xF,x9〉;〈xE,x4〉;〈x0,x3〉;〈x4,x9〉;〈xC,xE〉;〈x7,x1〉;〈x5,x7〉;〈x3,x4〉;〈x2,xE〉;〈xA,x3〉;〈x5,x3〉 ].

ndefinition dTest_random_ex04 ≝
[〈xF,x9〉;〈x2,xA〉;〈xF,x0〉;〈xE,x1〉;〈x6,x6〉;〈x8,x9〉;〈x2,xE〉;〈x8,x6〉;〈xC,x7〉;〈x2,xD〉;〈x1,x2〉;〈xD,x5〉;〈x4,xA〉;〈x7,x9〉;〈x6,xD〉;〈x1,xB〉
;〈x4,x1〉;〈x9,x4〉;〈x6,xC〉;〈x6,xD〉;〈xF,x4〉;〈x5,xD〉;〈x8,xB〉;〈xB,xE〉;〈xC,x8〉;〈xE,x5〉;〈xA,x4〉;〈xB,xA〉;〈xB,x1〉;〈x2,x1〉;〈x5,x0〉;〈x6,xB〉 ].

ndefinition dTest_random_ex05 ≝
[〈x9,x5〉;〈x0,x6〉;〈x4,x5〉;〈xE,x0〉;〈x0,xF〉;〈x5,xA〉;〈xC,xE〉;〈xC,x8〉;〈x8,x2〉;〈x4,xF〉;〈xC,x2〉;〈xF,x5〉;〈xF,x8〉;〈x1,x3〉;〈xD,xA〉;〈x2,xB〉
;〈x7,x9〉;〈xB,xF〉;〈xA,x4〉;〈x5,xA〉;〈xD,x2〉;〈x7,x6〉;〈x8,xD〉;〈x1,xF〉;〈x1,x5〉;〈x5,xA〉;〈xD,xE〉;〈x2,x3〉;〈x9,xD〉;〈x7,xE〉;〈x6,x7〉;〈x6,x3〉 ].

ndefinition dTest_random_ex06 ≝
[〈x1,x1〉;〈xF,x5〉;〈x2,x4〉;〈xD,x6〉;〈x6,xA〉;〈x0,xC〉;〈x7,xF〉;〈x1,x2〉;〈xD,x6〉;〈xE,xE〉;〈xB,xA〉;〈x4,x4〉;〈x3,x9〉;〈x9,x2〉;〈x6,x6〉;〈xE,xA〉
;〈x2,x3〉;〈x4,x4〉;〈xC,xF〉;〈x7,x4〉;〈x6,xB〉;〈x8,x3〉;〈x7,x7〉;〈x0,x4〉;〈x6,x4〉;〈xB,x3〉;〈x3,xC〉;〈x2,x6〉;〈xF,xC〉;〈xD,x5〉;〈x4,x1〉;〈xB,x7〉 ].

ndefinition dTest_random_ex07 ≝
[〈x2,x4〉;〈xE,x0〉;〈xB,x4〉;〈x1,x3〉;〈x3,x2〉;〈x4,x5〉;〈x1,x8〉;〈xD,xB〉;〈x0,x0〉;〈xB,x6〉;〈x5,xF〉;〈x3,xA〉;〈xB,x7〉;〈x4,xF〉;〈xB,x4〉;〈xD,xF〉
;〈xF,x4〉;〈x1,xA〉;〈x1,x0〉;〈xE,x9〉;〈xC,x5〉;〈x2,xC〉;〈xB,xC〉;〈x5,xB〉;〈x0,x5〉;〈x4,xA〉;〈x5,x2〉;〈xC,x0〉;〈x1,xF〉;〈x5,x9〉;〈xF,x2〉;〈xE,x5〉 ].

ndefinition dTest_random_ex08 ≝
[〈x9,x7〉;〈x5,x1〉;〈xF,x7〉;〈x3,xC〉;〈x7,x7〉;〈x8,x1〉;〈x7,xC〉;〈xB,x0〉;〈x1,xD〉;〈x1,xA〉;〈x7,xB〉;〈x4,x7〉;〈x7,x9〉;〈xC,x2〉;〈x3,xF〉;〈xD,x3〉
;〈xB,x6〉;〈xD,x7〉;〈xC,x9〉;〈x9,x2〉;〈x0,xD〉;〈x7,xF〉;〈x0,xB〉;〈x7,x5〉;〈x0,xE〉;〈x5,x1〉;〈x9,xF〉;〈x4,xC〉;〈xE,x5〉;〈xD,x0〉;〈xC,x1〉;〈x3,x9〉 ].

ndefinition dTest_random_ex09 ≝
[〈x7,xF〉;〈xE,xA〉;〈x4,x1〉;〈x0,x5〉;〈x0,x8〉;〈x7,xE〉;〈x7,x6〉;〈x2,xF〉;〈x6,x2〉;〈x7,x1〉;〈xF,x8〉;〈x3,x8〉;〈xB,x6〉;〈x7,x0〉;〈xD,xD〉;〈xD,x0〉
;〈xA,xD〉;〈x7,x8〉;〈x3,xD〉;〈x7,xB〉;〈xC,xC〉;〈x6,xD〉;〈x3,xF〉;〈xA,xC〉;〈xC,x7〉;〈x6,xE〉;〈xF,xF〉;〈x4,x5〉;〈xC,x1〉;〈x7,x4〉;〈xB,xF〉;〈x2,x9〉 ].

ndefinition dTest_random_ex0A ≝
[〈x4,x9〉;〈xC,x5〉;〈x7,xC〉;〈x2,xD〉;〈xF,x2〉;〈xC,xC〉;〈xF,xA〉;〈x5,x8〉;〈xA,xC〉;〈x5,x8〉;〈x5,x1〉;〈x0,xE〉;〈x4,x8〉;〈x7,x0〉;〈x4,x1〉;〈xE,xD〉
;〈x9,x5〉;〈xB,x4〉;〈x4,x7〉;〈xF,x1〉;〈x8,x1〉;〈xE,x4〉;〈x4,x0〉;〈x5,x4〉;〈x7,xB〉;〈xA,x1〉;〈xD,x2〉;〈x0,x2〉;〈xC,x5〉;〈x7,xD〉;〈x7,xA〉;〈xF,x1〉 ].

ndefinition dTest_random_ex0B ≝
[〈x0,x0〉;〈x8,xD〉;〈x6,x6〉;〈xB,x0〉;〈xA,x9〉;〈x7,xA〉;〈x2,xB〉;〈x2,xC〉;〈x6,xF〉;〈x5,xF〉;〈x6,xF〉;〈x4,xE〉;〈x2,xB〉;〈x1,x1〉;〈xF,xF〉;〈x4,x7〉
;〈x7,xF〉;〈xC,xF〉;〈xD,x3〉;〈x8,x5〉;〈xB,x8〉;〈x4,xD〉;〈x9,x9〉;〈x8,x3〉;〈x7,x6〉;〈xE,x8〉;〈x3,x0〉;〈xF,x8〉;〈xD,x0〉;〈x5,x9〉;〈xB,x8〉;〈x7,x1〉 ].

ndefinition dTest_random_ex0C ≝
[〈x5,x7〉;〈xA,xF〉;〈xB,x5〉;〈xD,x5〉;〈xF,xC〉;〈x8,x2〉;〈x1,x6〉;〈x1,x0〉;〈xB,x3〉;〈xC,x1〉;〈x1,xA〉;〈x0,x1〉;〈x1,x1〉;〈xF,xF〉;〈x5,x9〉;〈x2,x4〉
;〈xC,x5〉;〈x7,x2〉;〈xD,x8〉;〈xD,x0〉;〈xA,xD〉;〈xF,xE〉;〈xD,x7〉;〈x1,x1〉;〈xC,xE〉;〈xF,x9〉;〈xB,x8〉;〈x7,x7〉;〈x3,xA〉;〈x1,xF〉;〈x6,x1〉;〈x1,xB〉 ].

ndefinition dTest_random_ex0D ≝
[〈xB,xB〉;〈x5,x5〉;〈x8,x0〉;〈x7,xC〉;〈x2,x5〉;〈x3,x4〉;〈x8,x9〉;〈xF,x2〉;〈xC,x9〉;〈xD,xF〉;〈x3,x5〉;〈xC,x5〉;〈x1,x2〉;〈xF,x0〉;〈x0,x5〉;〈xD,xE〉
;〈x2,x6〉;〈x4,x9〉;〈xB,x7〉;〈x3,x9〉;〈x0,x5〉;〈xC,x2〉;〈xD,xB〉;〈xF,xC〉;〈x9,xF〉;〈xA,x9〉;〈x6,x6〉;〈xA,xD〉;〈x4,xA〉;〈x3,xF〉;〈xB,xF〉;〈x6,xD〉 ].

ndefinition dTest_random_ex0E ≝
[〈x8,x7〉;〈x6,xA〉;〈xB,x1〉;〈x3,xE〉;〈xB,x6〉;〈x0,xE〉;〈x7,xA〉;〈x3,xB〉;〈x4,x5〉;〈xE,x9〉;〈xC,xE〉;〈x6,xA〉;〈x6,xA〉;〈x7,x0〉;〈x6,x0〉;〈x6,xA〉
;〈x2,xC〉;〈xD,x2〉;〈xB,x8〉;〈x3,x6〉;〈x2,x1〉;〈x0,x0〉;〈x5,x4〉;〈x3,x1〉;〈x6,x0〉;〈x1,xB〉;〈x4,xC〉;〈xC,xA〉;〈xB,xE〉;〈x5,xF〉;〈x8,x1〉;〈xB,x7〉 ].

ndefinition dTest_random_ex0F ≝
[〈x9,xB〉;〈x2,x6〉;〈x9,x4〉;〈x2,xB〉;〈x4,x1〉;〈x2,xB〉;〈x9,x8〉;〈x6,x3〉;〈x6,x6〉;〈x6,x5〉;〈x4,x6〉;〈x2,x3〉;〈xE,x5〉;〈x0,x7〉;〈x9,xE〉;〈x1,xC〉
;〈x3,x8〉;〈x5,xC〉;〈x9,x7〉;〈x6,x3〉;〈x5,x3〉;〈x6,x6〉;〈x0,x8〉;〈x5,xD〉;〈x0,x8〉;〈xD,xB〉;〈x6,xE〉;〈x5,x6〉;〈x7,x0〉;〈x3,x2〉;〈x4,x5〉;〈x0,x2〉 ].

ndefinition dTest_random_ex10 ≝
[〈x6,x3〉;〈x7,x2〉;〈x9,xC〉;〈xD,x9〉;〈x5,x0〉;〈x0,x6〉;〈x5,x9〉;〈x1,x7〉;〈x6,x8〉;〈xD,x2〉;〈xD,x7〉;〈x8,xE〉;〈x6,x9〉;〈x5,xF〉;〈x8,x1〉;〈x8,x4〉
;〈x8,x7〉;〈xD,xC〉;〈x9,x8〉;〈xE,x5〉;〈xB,x5〉;〈xC,x3〉;〈x2,x5〉;〈x6,xC〉;〈x9,x2〉;〈xD,xD〉;〈x2,xA〉;〈xD,x1〉;〈x1,x4〉;〈x7,xE〉;〈x1,x7〉;〈xB,x2〉 ].

ndefinition dTest_random_ex11 ≝
[〈x9,x8〉;〈x5,x5〉;〈xF,xC〉;〈x3,xD〉;〈x8,xD〉;〈xE,xF〉;〈x8,x1〉;〈xB,x8〉;〈xB,xB〉;〈x5,x1〉;〈x0,x0〉;〈xB,x4〉;〈x2,xE〉;〈x3,x0〉;〈x6,x0〉;〈x7,xE〉
;〈x9,x0〉;〈xE,x3〉;〈xF,x4〉;〈x7,x2〉;〈x1,xC〉;〈xB,x3〉;〈x7,x8〉;〈x1,xB〉;〈x9,xF〉;〈x1,xB〉;〈x0,x3〉;〈xA,x3〉;〈x0,x5〉;〈xD,xE〉;〈x3,x8〉;〈xB,xA〉 ].

ndefinition dTest_random_ex12 ≝
[〈x0,xE〉;〈xE,xD〉;〈xE,xC〉;〈x1,xF〉;〈x3,x8〉;〈xE,x3〉;〈xF,x7〉;〈xA,xA〉;〈xE,x9〉;〈x3,xD〉;〈xF,xF〉;〈xF,x3〉;〈x1,x4〉;〈x2,xC〉;〈x8,x8〉;〈x6,x1〉
;〈x3,x0〉;〈xA,xB〉;〈x1,x8〉;〈xD,xC〉;〈xF,xE〉;〈x6,xA〉;〈x2,x9〉;〈xF,x1〉;〈xC,xB〉;〈x9,x0〉;〈x7,x8〉;〈x9,x9〉;〈x1,xF〉;〈x2,x8〉;〈xF,x9〉;〈xC,xB〉 ].

ndefinition dTest_random_ex13 ≝
[〈x1,x4〉;〈x8,x4〉;〈xF,x3〉;〈xD,x6〉;〈x7,xE〉;〈xE,xC〉;〈x5,x6〉;〈xC,xE〉;〈xD,xA〉;〈x5,xE〉;〈x6,x1〉;〈xF,x1〉;〈x6,x6〉;〈x6,x9〉;〈x9,x3〉;〈x5,x9〉
;〈x3,xC〉;〈x1,xD〉;〈x6,xB〉;〈xF,x4〉;〈x5,x9〉;〈x4,xD〉;〈x3,x8〉;〈xA,x9〉;〈x3,xB〉;〈x7,xF〉;〈xB,x2〉;〈xE,xC〉;〈xA,xE〉;〈xF,x6〉;〈xB,x2〉;〈x2,x2〉 ].

ndefinition dTest_random_ex14 ≝
[〈x6,x4〉;〈x2,x7〉;〈x6,xC〉;〈x2,x0〉;〈xE,xE〉;〈x5,x1〉;〈x3,xE〉;〈x8,x8〉;〈xD,xD〉;〈xC,x1〉;〈xD,xC〉;〈xC,x1〉;〈x6,x6〉;〈x6,x1〉;〈x4,x2〉;〈x7,x7〉
;〈x3,x6〉;〈x0,x8〉;〈x2,x9〉;〈x6,x0〉;〈xA,x9〉;〈xF,xC〉;〈x7,xC〉;〈xA,x7〉;〈xB,x4〉;〈xF,xC〉;〈x8,x7〉;〈x1,xD〉;〈x6,xC〉;〈xA,x2〉;〈x3,xF〉;〈x1,xD〉 ].

ndefinition dTest_random_ex15 ≝
[〈x1,x7〉;〈x0,xF〉;〈x0,x2〉;〈x2,x6〉;〈xA,x2〉;〈x6,xA〉;〈x5,xC〉;〈xE,xD〉;〈x2,x7〉;〈xC,x5〉;〈x7,xB〉;〈xF,x5〉;〈x9,xC〉;〈x8,x5〉;〈x6,x3〉;〈x5,x6〉
;〈xC,x3〉;〈x4,xB〉;〈x1,xB〉;〈xA,x0〉;〈x1,xB〉;〈x8,x9〉;〈x3,x5〉;〈xD,x6〉;〈xD,x9〉;〈xD,xD〉;〈x2,xE〉;〈x6,x2〉;〈x7,x5〉;〈xE,x7〉;〈x1,x8〉;〈x4,xD〉 ].

ndefinition dTest_random_ex16 ≝
[〈xD,x7〉;〈x5,x8〉;〈xA,x7〉;〈x5,xF〉;〈x9,x4〉;〈x8,x7〉;〈xA,x8〉;〈xE,x7〉;〈x2,xB〉;〈xF,x2〉;〈xE,x7〉;〈xB,x9〉;〈x0,x6〉;〈xA,xF〉;〈xD,xA〉;〈xD,xC〉
;〈xC,x6〉;〈x3,xF〉;〈x8,xD〉;〈x7,x9〉;〈x9,x5〉;〈xD,xA〉;〈x5,xB〉;〈x9,x2〉;〈xE,xE〉;〈x3,xC〉;〈xF,xE〉;〈x4,x9〉;〈x5,xA〉;〈x1,x0〉;〈x4,xD〉;〈x8,x9〉 ].

ndefinition dTest_random_ex17 ≝
[〈x8,x3〉;〈x2,x6〉;〈xE,xC〉;〈x8,xD〉;〈xC,x9〉;〈x7,x7〉;〈xE,xE〉;〈xF,x1〉;〈x4,x0〉;〈x6,xD〉;〈x4,x9〉;〈x5,x7〉;〈x9,xB〉;〈xC,x4〉;〈x1,xF〉;〈x8,x0〉
;〈x9,x5〉;〈xB,xC〉;〈xE,x8〉;〈xF,x9〉;〈xD,x7〉;〈x1,x4〉;〈x3,xE〉;〈xC,x3〉;〈x6,xF〉;〈x8,xF〉;〈x7,x2〉;〈xD,x5〉;〈xB,xE〉;〈x8,xA〉;〈xA,x3〉;〈xF,x7〉 ].

ndefinition dTest_random_ex18 ≝
[〈x6,x0〉;〈x3,xA〉;〈x7,x4〉;〈xF,xB〉;〈xB,xD〉;〈x7,x4〉;〈x8,x3〉;〈xE,x3〉;〈x9,xD〉;〈xD,x9〉;〈xB,x8〉;〈x1,x3〉;〈x5,x0〉;〈x4,x0〉;〈x8,xA〉;〈x9,x6〉
;〈x3,xA〉;〈xA,x6〉;〈xE,xC〉;〈x7,xC〉;〈x1,x5〉;〈x8,x7〉;〈x4,xD〉;〈x6,xA〉;〈xA,xA〉;〈xE,x0〉;〈xB,xA〉;〈xF,xF〉;〈x3,xB〉;〈xE,x2〉;〈x5,x1〉;〈x2,x2〉 ].

ndefinition dTest_random_ex19 ≝
[〈x2,x2〉;〈x1,xF〉;〈xA,x1〉;〈x2,x1〉;〈xA,xF〉;〈x3,x7〉;〈x8,xA〉;〈xD,xF〉;〈xE,x3〉;〈x6,x9〉;〈xE,xE〉;〈xC,x4〉;〈xE,x7〉;〈x7,x1〉;〈x9,x6〉;〈x1,x1〉
;〈xE,x4〉;〈x3,x9〉;〈xE,x5〉;〈xA,xF〉;〈xF,x5〉;〈x5,x7〉;〈xE,xB〉;〈x5,x5〉;〈x6,x5〉;〈x8,xB〉;〈x3,xE〉;〈x8,xD〉;〈x4,x6〉;〈x5,x3〉;〈xB,x2〉;〈x1,x9〉 ].

ndefinition dTest_random_ex1A ≝
[〈x3,x4〉;〈xE,x9〉;〈x4,xA〉;〈x4,xB〉;〈x5,x2〉;〈x3,x0〉;〈x3,xF〉;〈xA,x7〉;〈x4,xF〉;〈x1,xA〉;〈xB,x8〉;〈x6,x4〉;〈x5,xB〉;〈xD,x9〉;〈x6,xD〉;〈x6,x1〉
;〈xA,x5〉;〈xC,xF〉;〈x8,xC〉;〈xD,xD〉;〈xE,x6〉;〈xD,x5〉;〈x3,x6〉;〈x0,xC〉;〈x8,xD〉;〈xF,x7〉;〈x4,xE〉;〈x9,xC〉;〈xB,xF〉;〈x2,xB〉;〈x4,x4〉;〈xD,x1〉 ].

ndefinition dTest_random_ex1B ≝
[〈xC,x0〉;〈x8,x0〉;〈x0,x8〉;〈xA,xD〉;〈xC,xE〉;〈xB,xD〉;〈x4,xC〉;〈x5,x3〉;〈x6,x5〉;〈xB,x6〉;〈x4,x8〉;〈xF,x6〉;〈x6,x4〉;〈x7,xC〉;〈x9,x8〉;〈x1,x0〉
;〈x9,xD〉;〈xF,xD〉;〈x4,x9〉;〈xC,x4〉;〈xD,xD〉;〈x1,x4〉;〈xB,x6〉;〈x6,xF〉;〈x3,xB〉;〈x4,x6〉;〈xD,x7〉;〈x1,xA〉;〈x4,x4〉;〈xA,x4〉;〈x8,x1〉;〈x3,x1〉 ].

ndefinition dTest_random_ex1C ≝
[〈xA,x2〉;〈x4,x0〉;〈x7,x0〉;〈x3,x9〉;〈x9,xA〉;〈x4,xC〉;〈x4,xF〉;〈x9,x3〉;〈x9,xD〉;〈xD,x4〉;〈x9,x7〉;〈x3,x9〉;〈xA,x8〉;〈xA,x8〉;〈xF,x9〉;〈xB,x3〉
;〈xE,x7〉;〈xD,x8〉;〈x4,xD〉;〈x6,xD〉;〈x8,x8〉;〈x6,xB〉;〈x5,x4〉;〈x5,x5〉;〈x9,x2〉;〈x1,x9〉;〈xE,x4〉;〈xB,x1〉;〈xE,x3〉;〈x4,x6〉;〈xD,x5〉;〈x6,xC〉 ].

ndefinition dTest_random_ex1D ≝
[〈xF,x9〉;〈x3,x3〉;〈xE,x5〉;〈xD,x2〉;〈x7,x7〉;〈x1,x8〉;〈x8,x6〉;〈x1,x4〉;〈x7,xE〉;〈x1,xE〉;〈xC,x8〉;〈xB,x4〉;〈xC,xE〉;〈xC,x7〉;〈x5,x7〉;〈x2,xD〉
;〈x5,x2〉;〈xE,x7〉;〈x5,x7〉;〈x9,xB〉;〈x1,xA〉;〈x4,x9〉;〈x0,x9〉;〈x4,xB〉;〈xF,x6〉;〈xB,x5〉;〈x0,xA〉;〈x2,xC〉;〈xB,xA〉;〈x1,xF〉;〈x2,x6〉;〈x3,x8〉 ].

ndefinition dTest_random_ex1E ≝
[〈x6,x0〉;〈x3,x4〉;〈xC,x4〉;〈x8,x9〉;〈xB,xF〉;〈x0,x4〉;〈x5,xF〉;〈xF,x4〉;〈x1,x1〉;〈xF,x3〉;〈x4,xA〉;〈xE,x2〉;〈xD,x8〉;〈x3,x6〉;〈xF,xA〉;〈x4,x3〉
;〈x0,xC〉;〈x6,x0〉;〈x5,x1〉;〈x2,xD〉;〈x0,x3〉;〈xF,xC〉;〈x9,x2〉;〈x2,x1〉;〈xC,xA〉;〈x7,x5〉;〈x6,x6〉;〈xD,xC〉;〈x8,x4〉;〈xC,x4〉;〈x6,xF〉;〈xF,x0〉 ].

ndefinition dTest_random_ex1F ≝
[〈x0,x4〉;〈x5,x2〉;〈xA,xB〉;〈x9,xA〉;〈xC,xE〉;〈xA,xA〉;〈x2,xF〉;〈x3,x6〉;〈xF,x3〉;〈xA,x7〉;〈x4,x2〉;〈x0,x7〉;〈x5,xE〉;〈xB,x6〉;〈x5,xB〉;〈x9,x8〉
;〈x7,x9〉;〈x4,x3〉;〈x8,x8〉;〈x9,xA〉;〈x0,xA〉;〈x5,x5〉;〈xE,x3〉;〈x9,x8〉;〈x7,x5〉;〈xA,x2〉;〈xE,xA〉;〈xB,x9〉;〈x3,x2〉;〈x4,x1〉;〈x0,x7〉;〈x3,x8〉 ].

ndefinition dTest_random_ex20 ≝
[〈xB,x1〉;〈x0,x3〉;〈x4,xE〉;〈x6,xF〉;〈x9,x7〉;〈x3,xC〉;〈x5,x4〉;〈xB,xB〉;〈xB,xC〉;〈x0,xB〉;〈x0,xC〉;〈xA,xB〉;〈x3,xB〉;〈x2,x8〉;〈xA,xA〉;〈x0,x4〉
;〈x5,x0〉;〈xA,x3〉;〈x6,xB〉;〈xF,xA〉;〈xF,x0〉;〈xE,x6〉;〈x1,x8〉;〈xD,x8〉;〈x7,xA〉;〈x5,xF〉;〈x0,x3〉;〈x8,x2〉;〈x9,x6〉;〈x9,xA〉;〈xB,xF〉;〈x1,x5〉 ].

ndefinition dTest_random_ex21 ≝
[〈x8,x5〉;〈xE,xF〉;〈xB,x3〉;〈x7,xB〉;〈xE,xE〉;〈xE,xF〉;〈x1,x0〉;〈x6,x9〉;〈xC,x2〉;〈xF,x9〉;〈x2,xD〉;〈x8,x1〉;〈xF,x3〉;〈x0,xE〉;〈xC,x3〉;〈x7,xF〉
;〈xD,xD〉;〈x2,xE〉;〈x2,xA〉;〈xB,xD〉;〈xE,xA〉;〈x9,x2〉;〈xF,xF〉;〈xF,xA〉;〈x7,xB〉;〈xD,x3〉;〈x3,x0〉;〈x7,x5〉;〈x6,x7〉;〈xA,x8〉;〈x0,xF〉;〈x2,x1〉 ].

ndefinition dTest_random_ex22 ≝
[〈xD,xC〉;〈xE,x5〉;〈xE,x2〉;〈x8,x9〉;〈x2,x9〉;〈xC,x5〉;〈xA,x3〉;〈xA,x2〉;〈x4,x2〉;〈x3,xF〉;〈xA,x3〉;〈x5,x8〉;〈xE,x0〉;〈x7,xC〉;〈x0,x3〉;〈xF,xF〉
;〈x2,x8〉;〈x8,xB〉;〈x8,xB〉;〈x1,x2〉;〈xD,x8〉;〈xA,x8〉;〈x7,x6〉;〈xB,x9〉;〈xE,x2〉;〈xF,xE〉;〈x2,x1〉;〈x3,xF〉;〈xA,xC〉;〈x4,x6〉;〈xB,xC〉;〈xF,x8〉 ].

ndefinition dTest_random_ex23 ≝
[〈xD,x3〉;〈xE,xB〉;〈xF,xC〉;〈x9,xF〉;〈xE,x7〉;〈x6,x1〉;〈xC,xB〉;〈xB,xF〉;〈x4,xE〉;〈xC,x4〉;〈x9,x7〉;〈x1,xE〉;〈x0,xD〉;〈x7,x9〉;〈x8,x3〉;〈xA,xB〉
;〈x4,xC〉;〈x2,x6〉;〈x6,x3〉;〈x6,xF〉;〈xE,xE〉;〈x5,x9〉;〈x8,x1〉;〈x0,x2〉;〈x2,xC〉;〈xE,xD〉;〈x6,xF〉;〈x0,x4〉;〈x1,x0〉;〈xE,x0〉;〈xD,xA〉;〈xB,xE〉 ].

ndefinition dTest_random_ex24 ≝
[〈xE,xE〉;〈x5,x7〉;〈xB,x0〉;〈x3,x1〉;〈x4,x1〉;〈xD,xC〉;〈x3,xC〉;〈xC,xC〉;〈x5,x8〉;〈x2,x8〉;〈x2,xC〉;〈x1,xB〉;〈x8,x6〉;〈xD,x6〉;〈xF,x9〉;〈xD,x5〉
;〈x4,xA〉;〈xE,xA〉;〈x0,xB〉;〈x2,x0〉;〈x2,xC〉;〈x4,x2〉;〈xC,xE〉;〈x4,x5〉;〈x2,xB〉;〈x0,x1〉;〈xA,xA〉;〈xB,x1〉;〈x6,xE〉;〈xB,x7〉;〈xB,x7〉;〈x2,x8〉 ].

ndefinition dTest_random_ex25 ≝
[〈x9,x5〉;〈x1,x9〉;〈xA,x7〉;〈x5,xC〉;〈x4,xE〉;〈x7,xB〉;〈x3,xE〉;〈xD,x3〉;〈x9,x0〉;〈x8,x6〉;〈x7,x1〉;〈x1,x4〉;〈xD,x2〉;〈xD,x4〉;〈xB,x4〉;〈xF,x2〉
;〈x3,x1〉;〈x2,x8〉;〈x4,x5〉;〈xF,xD〉;〈x7,x8〉;〈x5,xD〉;〈xF,xA〉;〈xF,x3〉;〈x9,x5〉;〈x4,xD〉;〈x3,x1〉;〈xB,x8〉;〈xC,xC〉;〈x2,x1〉;〈x1,x9〉;〈x4,x2〉 ].

ndefinition dTest_random_ex26 ≝
[〈x2,xA〉;〈xF,x2〉;〈xB,xA〉;〈x0,x4〉;〈x9,xF〉;〈x4,x3〉;〈x4,x5〉;〈x1,xC〉;〈x7,x4〉;〈xB,xB〉;〈x7,x0〉;〈x5,xE〉;〈x0,x1〉;〈xA,xC〉;〈x6,xD〉;〈xD,x7〉
;〈x9,xC〉;〈x9,xD〉;〈x1,xA〉;〈x9,x8〉;〈xB,x1〉;〈xF,xC〉;〈x6,x1〉;〈xA,x3〉;〈x4,x1〉;〈x4,x1〉;〈xA,xF〉;〈x1,xD〉;〈xE,x1〉;〈x3,x2〉;〈x1,x9〉;〈x6,x0〉 ].

ndefinition dTest_random_ex27 ≝
[〈x2,x9〉;〈x9,x7〉;〈x8,x5〉;〈x5,x3〉;〈x5,x3〉;〈x9,x1〉;〈xB,x3〉;〈x9,x4〉;〈xD,x5〉;〈x9,xD〉;〈x4,xC〉;〈x3,x6〉;〈x0,xE〉;〈x8,x4〉;〈xA,x1〉;〈x4,x6〉
;〈x6,xA〉;〈x1,xF〉;〈xF,x3〉;〈x6,xB〉;〈xB,xE〉;〈x4,xA〉;〈x1,x9〉;〈x7,x5〉;〈xF,xC〉;〈xC,x6〉;〈xE,xA〉;〈x7,xE〉;〈xD,x1〉;〈x3,x3〉;〈x6,x7〉;〈xB,x7〉 ].

ndefinition dTest_random_ex28 ≝
[〈xE,xE〉;〈x5,x9〉;〈xE,x2〉;〈xD,xD〉;〈x2,x2〉;〈x8,xC〉;〈x9,xB〉;〈x3,xE〉;〈x9,x8〉;〈xF,xC〉;〈x1,x3〉;〈xE,x2〉;〈x0,xC〉;〈x4,xE〉;〈x3,x1〉;〈x8,x7〉
;〈x6,x7〉;〈x6,xA〉;〈x4,xC〉;〈x4,xC〉;〈x7,x2〉;〈x0,x0〉;〈x0,x5〉;〈x1,xF〉;〈xF,x6〉;〈x3,x0〉;〈xE,xE〉;〈xD,xE〉;〈xB,x1〉;〈x4,xC〉;〈xF,x7〉;〈xE,xC〉 ].

ndefinition dTest_random_ex29 ≝
[〈x2,xC〉;〈x4,x0〉;〈x6,xB〉;〈x6,x8〉;〈x9,x0〉;〈x8,x8〉;〈x6,xF〉;〈xB,x3〉;〈x4,x7〉;〈x6,x2〉;〈x9,x2〉;〈x9,xB〉;〈x2,xB〉;〈x3,x2〉;〈x4,x0〉;〈xA,x7〉
;〈x8,x9〉;〈x4,x0〉;〈x2,x3〉;〈x5,xC〉;〈xF,x9〉;〈x2,x9〉;〈x6,x2〉;〈xA,xE〉;〈x5,xB〉;〈xC,x9〉;〈x2,xC〉;〈x9,x2〉;〈x6,xF〉;〈xF,x5〉;〈xA,x0〉;〈x0,xE〉 ].

ndefinition dTest_random_ex2A ≝
[〈xD,xE〉;〈xF,x9〉;〈x0,x9〉;〈x1,x0〉;〈x3,x9〉;〈x4,x6〉;〈xC,x5〉;〈xE,x2〉;〈x8,x3〉;〈xD,x5〉;〈x8,xE〉;〈x4,x6〉;〈x4,xC〉;〈xA,xC〉;〈x7,xF〉;〈x4,xF〉
;〈xC,x1〉;〈x4,xF〉;〈x1,xA〉;〈x6,x1〉;〈x9,x6〉;〈x0,xB〉;〈x0,x0〉;〈x6,xF〉;〈x2,x6〉;〈x8,xC〉;〈xE,xE〉;〈x9,x3〉;〈x1,xB〉;〈x9,xE〉;〈xA,x5〉;〈x9,x6〉 ].

ndefinition dTest_random_ex2B ≝
[〈x2,xA〉;〈xE,xB〉;〈x4,x6〉;〈x5,xF〉;〈x3,xC〉;〈xD,x6〉;〈x2,xD〉;〈x9,x4〉;〈x6,xB〉;〈xF,x4〉;〈xD,xA〉;〈x6,x9〉;〈x5,x9〉;〈xA,xC〉;〈xB,xD〉;〈x9,xE〉
;〈x4,x8〉;〈x0,x2〉;〈xD,xC〉;〈x5,xC〉;〈x6,x0〉;〈x2,xA〉;〈x6,xE〉;〈xC,xA〉;〈x6,xE〉;〈x1,xF〉;〈xD,x4〉;〈x3,xA〉;〈xB,x0〉;〈x9,xE〉;〈x8,xF〉;〈xA,xB〉 ].

ndefinition dTest_random_ex2C ≝
[〈xB,x2〉;〈x0,x2〉;〈x4,x7〉;〈x7,xD〉;〈xA,xB〉;〈xD,xB〉;〈xB,x5〉;〈x6,xD〉;〈xE,x2〉;〈x8,x9〉;〈x4,xD〉;〈x0,x4〉;〈xB,xE〉;〈xF,xA〉;〈x2,x2〉;〈x1,x4〉
;〈x7,x1〉;〈x1,x2〉;〈x1,xB〉;〈x0,xD〉;〈xB,xA〉;〈x5,xA〉;〈x6,xC〉;〈x1,xE〉;〈x3,xA〉;〈x0,xF〉;〈x6,xE〉;〈x4,x4〉;〈xC,x8〉;〈xB,x5〉;〈x8,xC〉;〈x0,x3〉 ].

ndefinition dTest_random_ex2D ≝
[〈x0,x6〉;〈x6,x4〉;〈x8,x5〉;〈x2,x8〉;〈x6,x4〉;〈x2,x2〉;〈x8,x1〉;〈x7,x6〉;〈xF,xE〉;〈xF,xA〉;〈x6,x2〉;〈x9,x1〉;〈xB,xE〉;〈xB,xC〉;〈x6,x1〉;〈x4,xB〉
;〈x7,xE〉;〈x5,x0〉;〈xB,xC〉;〈xE,xE〉;〈x6,x3〉;〈xC,xF〉;〈x1,xD〉;〈xF,xD〉;〈x6,x2〉;〈x5,xC〉;〈x8,x5〉;〈x9,xE〉;〈xA,x5〉;〈x2,x6〉;〈xE,x7〉;〈x4,x6〉 ].

ndefinition dTest_random_ex2E ≝
[〈x3,xB〉;〈xE,xA〉;〈xB,xE〉;〈x0,x4〉;〈x8,x8〉;〈xF,x2〉;〈x9,x2〉;〈x0,xB〉;〈xD,x9〉;〈xE,x9〉;〈x2,x9〉;〈x3,x8〉;〈x8,x8〉;〈x8,xA〉;〈x6,x9〉;〈x1,x7〉
;〈x4,xB〉;〈xB,xF〉;〈x0,xC〉;〈xF,x2〉;〈xF,xD〉;〈x7,x3〉;〈x5,x9〉;〈xB,xE〉;〈x5,x4〉;〈x1,xC〉;〈xD,x3〉;〈x3,x1〉;〈x6,x2〉;〈x1,xB〉;〈xB,x7〉;〈x3,x2〉 ].

ndefinition dTest_random_ex2F ≝
[〈xA,x4〉;〈xF,x1〉;〈x7,x0〉;〈x9,xA〉;〈x4,x6〉;〈xA,x1〉;〈x1,xC〉;〈x0,x4〉;〈x6,xC〉;〈xF,x2〉;〈xE,x6〉;〈xC,x1〉;〈xA,x4〉;〈xF,x2〉;〈x2,xA〉;〈x4,xB〉
;〈x3,x5〉;〈x9,xB〉;〈x9,x9〉;〈xF,xF〉;〈x0,x1〉;〈x1,x3〉;〈xF,x9〉;〈x5,xC〉;〈x3,xC〉;〈x5,x1〉;〈x8,xA〉;〈xA,x5〉;〈x5,xF〉;〈x9,xE〉;〈x5,xE〉;〈xC,x6〉 ].

ndefinition dTest_random_ex30 ≝
[〈x2,x1〉;〈x3,x7〉;〈xD,x2〉;〈xB,x9〉;〈x9,x8〉;〈xA,x1〉;〈x6,x0〉;〈xE,x9〉;〈x4,x5〉;〈xC,xA〉;〈xD,x7〉;〈xB,xD〉;〈xC,xF〉;〈x0,xF〉;〈x2,x4〉;〈xE,x5〉
;〈x7,x9〉;〈x4,xB〉;〈x1,xC〉;〈x5,x7〉;〈x3,xA〉;〈x2,x4〉;〈x2,x2〉;〈x0,x8〉;〈x3,x3〉;〈xE,x2〉;〈xA,x2〉;〈x5,x8〉;〈x2,x5〉;〈x5,x4〉;〈x7,x1〉;〈x2,xB〉 ].

ndefinition dTest_random_ex31 ≝
[〈xF,xF〉;〈xE,xD〉;〈x4,x8〉;〈xF,x6〉;〈x2,x3〉;〈x3,x1〉;〈xB,xA〉;〈x5,x1〉;〈x9,xF〉;〈xA,xA〉;〈xC,xC〉;〈x0,x3〉;〈x1,x5〉;〈xC,x7〉;〈x2,xD〉;〈xD,x3〉
;〈xE,xB〉;〈x8,xF〉;〈x8,x4〉;〈x4,x0〉;〈x5,x3〉;〈xA,xD〉;〈x6,x7〉;〈xE,xC〉;〈xA,xF〉;〈xD,xC〉;〈x1,xC〉;〈x7,x4〉;〈x6,xB〉;〈xA,xD〉;〈xC,xD〉;〈xA,x7〉 ].

ndefinition dTest_random_ex32 ≝
[〈x1,x1〉;〈x1,x0〉;〈xC,xF〉;〈xB,xE〉;〈xA,x1〉;〈x0,x1〉;〈x3,xF〉;〈xC,x0〉;〈x8,x5〉;〈x2,x8〉;〈x6,xB〉;〈xC,x3〉;〈x6,xD〉;〈xD,x8〉;〈x7,x5〉;〈x5,xA〉
;〈xF,x0〉;〈x2,x2〉;〈x4,xB〉;〈x9,xC〉;〈x3,x1〉;〈xE,x4〉;〈xE,x7〉;〈xC,x6〉;〈xF,xC〉;〈x3,x0〉;〈xD,x5〉;〈xF,x9〉;〈x1,xA〉;〈x4,x0〉;〈x1,xF〉;〈x6,xD〉 ].

ndefinition dTest_random_ex33 ≝
[〈xD,x5〉;〈x7,x8〉;〈xB,x5〉;〈x7,x6〉;〈xC,x9〉;〈xE,x1〉;〈xD,xF〉;〈x1,x2〉;〈x6,x1〉;〈xD,xF〉;〈x9,xF〉;〈x5,x7〉;〈x7,xD〉;〈x0,xB〉;〈xA,xD〉;〈x5,xA〉
;〈xA,x1〉;〈x8,x4〉;〈xE,x5〉;〈xF,x7〉;〈xB,xC〉;〈xD,x3〉;〈xA,x5〉;〈xB,x4〉;〈x8,x5〉;〈x6,x7〉;〈x3,x6〉;〈xF,xC〉;〈xB,x1〉;〈xB,x3〉;〈xC,xB〉;〈x1,xE〉 ].

ndefinition dTest_random_ex34 ≝
[〈xE,xC〉;〈x6,xE〉;〈xE,x1〉;〈x1,xC〉;〈xA,x5〉;〈x5,x3〉;〈x9,x8〉;〈xF,x6〉;〈xD,xF〉;〈x4,x1〉;〈x1,x3〉;〈x2,xE〉;〈x7,xF〉;〈x0,xE〉;〈x3,x8〉;〈x3,xC〉
;〈xD,x4〉;〈x8,xC〉;〈x2,xA〉;〈x2,x8〉;〈x4,xE〉;〈x7,xE〉;〈x0,xE〉;〈xF,x7〉;〈xC,xA〉;〈x3,xE〉;〈xE,x4〉;〈xB,x4〉;〈x0,x5〉;〈x5,x8〉;〈xD,xC〉;〈x7,x8〉 ].

ndefinition dTest_random_ex35 ≝
[〈xD,x9〉;〈xF,x9〉;〈x7,x9〉;〈x8,x4〉;〈x0,x2〉;〈x3,xF〉;〈xC,xF〉;〈x3,x8〉;〈xD,x7〉;〈x2,x6〉;〈x1,xD〉;〈x1,x8〉;〈x4,xD〉;〈xE,xA〉;〈x7,xA〉;〈xD,x4〉
;〈x2,x4〉;〈x0,xD〉;〈x4,xD〉;〈x9,x0〉;〈x1,x7〉;〈x1,xE〉;〈x6,xE〉;〈xB,x6〉;〈xC,xC〉;〈xC,x0〉;〈xB,x0〉;〈x5,xE〉;〈x9,x9〉;〈x6,xD〉;〈xC,xF〉;〈xE,xE〉 ].

ndefinition dTest_random_ex36 ≝
[〈x2,x9〉;〈xC,xF〉;〈xA,x2〉;〈x0,xC〉;〈xA,xB〉;〈x7,x4〉;〈x2,x9〉;〈x4,xE〉;〈x8,x2〉;〈x9,x3〉;〈x6,x9〉;〈x7,xB〉;〈xE,xC〉;〈xC,x7〉;〈x8,x9〉;〈xC,xA〉
;〈xD,xD〉;〈xA,xC〉;〈x6,x5〉;〈x8,x0〉;〈x1,x4〉;〈x0,x9〉;〈x5,x5〉;〈x0,xE〉;〈x8,x4〉;〈x5,xE〉;〈x6,xF〉;〈x3,x4〉;〈x1,x8〉;〈xC,x9〉;〈x8,xB〉;〈xE,x4〉 ].

ndefinition dTest_random_ex37 ≝
[〈x3,xE〉;〈xC,x4〉;〈x1,x6〉;〈xA,x4〉;〈x1,x9〉;〈x3,x4〉;〈x0,xE〉;〈x5,xE〉;〈xF,x9〉;〈x0,x3〉;〈x1,x3〉;〈x7,x2〉;〈x2,x7〉;〈x2,x8〉;〈xA,x7〉;〈x6,xD〉
;〈xC,x1〉;〈x1,xD〉;〈xF,x0〉;〈x2,x8〉;〈xF,xB〉;〈xF,x6〉;〈x3,x8〉;〈x0,x1〉;〈xF,x9〉;〈xB,xC〉;〈x6,x6〉;〈xF,x8〉;〈x6,xE〉;〈xD,x1〉;〈xB,x5〉;〈x3,x8〉 ].

ndefinition dTest_random_ex38 ≝
[〈x4,x3〉;〈xB,x6〉;〈x6,x8〉;〈xA,xC〉;〈x0,x9〉;〈xF,xD〉;〈x0,x9〉;〈x6,x8〉;〈xE,x0〉;〈x2,x2〉;〈xA,xF〉;〈x4,x0〉;〈x2,x6〉;〈x0,xC〉;〈x5,x2〉;〈xA,x7〉
;〈xA,xD〉;〈xC,x3〉;〈x8,x2〉;〈xD,xC〉;〈x3,xC〉;〈x6,x5〉;〈xF,x2〉;〈xE,x8〉;〈xC,x0〉;〈x0,x6〉;〈x6,x4〉;〈xB,x1〉;〈x2,x0〉;〈x9,x5〉;〈x2,x2〉;〈xD,xD〉 ].

ndefinition dTest_random_ex39 ≝
[〈xA,xD〉;〈xF,xF〉;〈x1,xB〉;〈x8,xB〉;〈xB,x6〉;〈x4,xA〉;〈xB,xB〉;〈x9,x8〉;〈x1,xA〉;〈xE,xC〉;〈x7,xB〉;〈xA,x6〉;〈x2,xC〉;〈xE,x1〉;〈xC,x7〉;〈xD,xC〉
;〈x1,x9〉;〈x0,x6〉;〈x0,xA〉;〈x9,xF〉;〈x5,x2〉;〈x2,xB〉;〈xC,xA〉;〈x2,xF〉;〈x4,x0〉;〈xF,x8〉;〈xE,xA〉;〈x8,x7〉;〈x8,x9〉;〈xF,xD〉;〈x5,xD〉;〈x0,x0〉 ].

ndefinition dTest_random_ex3A ≝
[〈x6,xE〉;〈x0,x0〉;〈x0,xD〉;〈x3,x0〉;〈x4,x3〉;〈x5,xA〉;〈x8,xF〉;〈x8,xA〉;〈xA,x4〉;〈x5,x0〉;〈x8,xF〉;〈x0,xC〉;〈x7,x7〉;〈xF,x2〉;〈x6,x5〉;〈xE,x4〉
;〈x2,xD〉;〈xE,x5〉;〈xA,x8〉;〈x7,xF〉;〈x7,x8〉;〈xE,x3〉;〈x9,x5〉;〈xD,xA〉;〈x0,x7〉;〈x2,x9〉;〈x5,x1〉;〈x9,x4〉;〈xE,x4〉;〈x0,x1〉;〈xB,xF〉;〈x6,xE〉 ].

ndefinition dTest_random_ex3B ≝
[〈x9,x8〉;〈x9,xC〉;〈x9,x0〉;〈xA,x8〉;〈x0,xA〉;〈x3,xD〉;〈x3,xC〉;〈x5,x0〉;〈xE,xB〉;〈x1,x2〉;〈xC,x4〉;〈x5,xF〉;〈x4,x7〉;〈x7,xB〉;〈x2,xC〉;〈xD,xF〉
;〈x7,x8〉;〈x1,x3〉;〈x7,x4〉;〈xE,x0〉;〈x7,xB〉;〈x7,x1〉;〈x4,x7〉;〈x4,x8〉;〈x1,xB〉;〈xE,x3〉;〈x6,xB〉;〈x0,xB〉;〈x4,xB〉;〈x5,x9〉;〈x9,x3〉;〈xD,xF〉 ].

ndefinition dTest_random_ex3C ≝
[〈xE,x1〉;〈x1,xB〉;〈xD,x0〉;〈xE,xD〉;〈x4,x7〉;〈x4,xD〉;〈xC,x2〉;〈xD,xE〉;〈x5,xC〉;〈xD,xA〉;〈x9,x5〉;〈xC,x8〉;〈x1,x0〉;〈x7,x7〉;〈x7,xF〉;〈xC,x0〉
;〈xA,x7〉;〈xD,x3〉;〈xD,x3〉;〈xD,x8〉;〈x3,x4〉;〈xA,x1〉;〈x1,x5〉;〈xE,x0〉;〈x0,x4〉;〈x1,xE〉;〈x8,x2〉;〈xC,xA〉;〈xD,x9〉;〈x1,x1〉;〈xB,x1〉;〈xC,x9〉 ].

ndefinition dTest_random_ex3D ≝
[〈x4,xC〉;〈x4,xB〉;〈x0,x9〉;〈x4,x8〉;〈xF,xC〉;〈xD,xD〉;〈x6,xE〉;〈xC,xA〉;〈x7,x6〉;〈xA,xE〉;〈x8,xE〉;〈x3,xB〉;〈xF,xB〉;〈x6,x5〉;〈x8,x3〉;〈x1,xD〉
;〈xD,xB〉;〈xA,xE〉;〈x4,xF〉;〈xC,x6〉;〈x1,xE〉;〈xC,x5〉;〈xC,xC〉;〈x7,xC〉;〈x2,x8〉;〈xF,x9〉;〈xD,x2〉;〈x8,x6〉;〈x1,x5〉;〈xF,xA〉;〈x4,x1〉;〈x4,x5〉 ].

ndefinition dTest_random_ex3E ≝
[〈x2,xE〉;〈x9,x5〉;〈xB,xF〉;〈x0,xD〉;〈x8,xB〉;〈x8,xD〉;〈x1,x1〉;〈x9,xC〉;〈xB,x8〉;〈xF,xB〉;〈x2,x6〉;〈xD,x6〉;〈x9,x1〉;〈x0,xD〉;〈xC,xD〉;〈x0,x7〉
;〈x5,x0〉;〈xF,xA〉;〈x2,x9〉;〈x3,xF〉;〈x0,xC〉;〈x2,xB〉;〈xF,xE〉;〈x9,x7〉;〈x5,x5〉;〈x5,xA〉;〈x6,xD〉;〈x9,x6〉;〈x0,x5〉;〈x0,x9〉;〈x4,x5〉;〈xE,xF〉 ].

ndefinition dTest_random_ex3F ≝
[〈x0,xF〉;〈x7,x4〉;〈x9,x3〉;〈x6,xC〉;〈x8,x2〉;〈x3,x7〉;〈xE,xB〉;〈x5,x0〉;〈xF,x5〉;〈xC,x4〉;〈x0,xB〉;〈x3,x8〉;〈x2,xD〉;〈x8,xA〉;〈x9,x3〉;〈x6,xD〉
;〈x1,xD〉;〈xE,x5〉;〈xF,x7〉;〈xE,x7〉;〈xD,x7〉;〈x5,xC〉;〈xB,x4〉;〈x5,x0〉;〈x7,x5〉;〈x0,xD〉;〈xF,x3〉;〈xC,xE〉;〈x3,x1〉;〈xF,x1〉;〈x8,xE〉;〈x8,xF〉 ].

ndefinition dTest_random_ex40 ≝
[〈xD,xB〉;〈x1,x4〉;〈xF,x6〉;〈x0,x3〉;〈xA,xB〉;〈xA,xE〉;〈xB,xC〉;〈xE,xB〉;〈xC,x8〉;〈x6,x7〉;〈xC,xC〉;〈xF,xF〉;〈x4,xF〉;〈xC,x6〉;〈x2,x9〉;〈x9,x5〉
;〈xB,xC〉;〈x6,x5〉;〈x5,x2〉;〈xF,x2〉;〈x3,x5〉;〈xC,x4〉;〈xF,x4〉;〈x9,xB〉;〈x4,x5〉;〈x1,xC〉;〈xD,xB〉;〈x6,x1〉;〈xF,xE〉;〈x3,xF〉;〈xB,x9〉;〈xD,x8〉 ].

ndefinition dTest_random_ex41 ≝
[〈xF,x1〉;〈xA,xC〉;〈x0,x7〉;〈xA,x4〉;〈xB,x8〉;〈x8,x8〉;〈x9,x5〉;〈xB,x8〉;〈x5,x6〉;〈x3,x2〉;〈x5,xA〉;〈x3,xE〉;〈x2,x2〉;〈x0,xB〉;〈x9,x6〉;〈xE,xE〉
;〈x6,xF〉;〈x1,xE〉;〈x3,x2〉;〈x4,x9〉;〈x4,xF〉;〈xC,xC〉;〈xD,xB〉;〈x5,x1〉;〈x4,xD〉;〈xD,x1〉;〈x4,xF〉;〈x0,x9〉;〈x5,xA〉;〈xA,xC〉;〈xE,x7〉;〈x8,x6〉 ].

ndefinition dTest_random_ex42 ≝
[〈x5,x8〉;〈xA,x5〉;〈xA,x7〉;〈x5,xE〉;〈x3,x6〉;〈x1,x1〉;〈x3,xA〉;〈x8,x9〉;〈x8,x2〉;〈xD,xC〉;〈x6,x2〉;〈x0,xE〉;〈xA,xB〉;〈x2,xB〉;〈x2,x5〉;〈xF,x9〉
;〈x7,x7〉;〈x8,x6〉;〈x1,xD〉;〈x7,x9〉;〈x5,x1〉;〈xB,xD〉;〈x9,x8〉;〈xB,x7〉;〈xB,xB〉;〈xF,x6〉;〈xD,x9〉;〈x6,x6〉;〈x0,x1〉;〈x1,x2〉;〈xE,xB〉;〈x0,xA〉 ].

ndefinition dTest_random_ex43 ≝
[〈xC,xD〉;〈x1,xA〉;〈xA,xA〉;〈xC,xC〉;〈x6,x5〉;〈x4,x2〉;〈x8,xF〉;〈x2,xA〉;〈x4,x8〉;〈xC,x6〉;〈xB,xA〉;〈xD,x8〉;〈x2,xD〉;〈x2,x9〉;〈xE,x8〉;〈x5,x7〉
;〈x7,x7〉;〈x7,xA〉;〈xB,x4〉;〈x4,x9〉;〈x6,x5〉;〈x4,x3〉;〈x5,x7〉;〈xF,xE〉;〈xC,x6〉;〈xC,x7〉;〈x6,x2〉;〈x6,x7〉;〈x5,x8〉;〈xD,x6〉;〈x9,xA〉;〈xC,x8〉 ].

ndefinition dTest_random_ex44 ≝
[〈xE,x8〉;〈x3,x0〉;〈x6,x0〉;〈x7,x3〉;〈x8,x9〉;〈x2,x3〉;〈x0,x8〉;〈x7,xA〉;〈xA,xC〉;〈x5,xD〉;〈x6,xD〉;〈xC,xE〉;〈x0,xC〉;〈x1,xB〉;〈x1,x7〉;〈xC,x1〉
;〈x4,x2〉;〈x5,x3〉;〈x1,x5〉;〈x7,xC〉;〈x7,x4〉;〈x2,xB〉;〈x2,x5〉;〈x5,x6〉;〈x6,x1〉;〈xE,xC〉;〈x0,xB〉;〈x4,x2〉;〈x0,x4〉;〈xC,xA〉;〈x0,x9〉;〈xA,xB〉 ].

ndefinition dTest_random_ex45 ≝
[〈x1,xB〉;〈xD,x0〉;〈x9,xF〉;〈x6,xA〉;〈x7,xF〉;〈x4,x1〉;〈xF,x8〉;〈xE,xA〉;〈x8,x2〉;〈x8,x1〉;〈x4,x1〉;〈xC,xE〉;〈xC,xE〉;〈x0,xD〉;〈x2,xB〉;〈x3,x3〉
;〈xA,x3〉;〈x6,x4〉;〈xF,xA〉;〈xA,x6〉;〈x3,x9〉;〈x7,xF〉;〈xF,x6〉;〈xB,x2〉;〈x5,x5〉;〈x6,xB〉;〈xA,xC〉;〈x3,x3〉;〈x9,x3〉;〈xE,x7〉;〈xB,xE〉;〈x3,x4〉 ].

ndefinition dTest_random_ex46 ≝
[〈xC,xF〉;〈xE,xF〉;〈xA,x2〉;〈xE,xE〉;〈xE,xD〉;〈xC,xB〉;〈xB,x0〉;〈x8,x9〉;〈xD,xA〉;〈x3,xB〉;〈xB,xE〉;〈x3,xE〉;〈x3,x3〉;〈x5,x1〉;〈xA,x5〉;〈x3,xC〉
;〈xC,xC〉;〈xA,x0〉;〈xF,xD〉;〈x3,x9〉;〈xC,xB〉;〈xF,xC〉;〈x1,xF〉;〈x8,xD〉;〈x6,x8〉;〈xD,x4〉;〈x8,xC〉;〈xA,xA〉;〈x8,xE〉;〈x3,xA〉;〈x9,x7〉;〈x2,x6〉 ].

ndefinition dTest_random_ex47 ≝
[〈x6,xB〉;〈xA,xC〉;〈x8,xA〉;〈x4,xB〉;〈x7,x4〉;〈x3,xF〉;〈xB,x7〉;〈xB,xF〉;〈x0,xC〉;〈xE,x6〉;〈xC,xD〉;〈x4,x2〉;〈xF,xA〉;〈xE,xE〉;〈xF,x9〉;〈x0,xC〉
;〈x2,xC〉;〈x7,x9〉;〈x7,xE〉;〈xD,x8〉;〈x4,x0〉;〈x7,xC〉;〈x3,x8〉;〈x4,x9〉;〈x7,x1〉;〈x7,x5〉;〈xB,x7〉;〈x3,x6〉;〈x0,x7〉;〈x1,xA〉;〈x2,xC〉;〈x1,xE〉 ].

ndefinition dTest_random_ex48 ≝
[〈x3,xC〉;〈x7,xA〉;〈x3,x8〉;〈x4,xA〉;〈x3,x4〉;〈x2,x0〉;〈x9,x5〉;〈x6,x0〉;〈xF,x7〉;〈xC,x3〉;〈xB,x1〉;〈x6,xE〉;〈xB,x1〉;〈x7,x0〉;〈x7,x4〉;〈x3,xB〉
;〈x0,xD〉;〈x6,xD〉;〈xF,xB〉;〈xE,x5〉;〈xE,x2〉;〈x6,x6〉;〈x6,x8〉;〈x0,x8〉;〈xF,xB〉;〈x3,xC〉;〈x8,xC〉;〈xD,xD〉;〈x0,x2〉;〈x2,xE〉;〈x6,xE〉;〈xF,x1〉 ].

ndefinition dTest_random_ex49 ≝
[〈xA,xF〉;〈x7,x9〉;〈x6,x7〉;〈xE,x2〉;〈x4,xC〉;〈xA,x5〉;〈x7,x9〉;〈xC,x6〉;〈xB,x5〉;〈xA,xF〉;〈x1,x5〉;〈xF,xE〉;〈xE,x2〉;〈x2,xB〉;〈xC,xA〉;〈xE,x6〉
;〈x3,xE〉;〈x2,xC〉;〈x5,x8〉;〈x7,x2〉;〈xC,xE〉;〈x7,x1〉;〈x8,xC〉;〈xB,xE〉;〈x2,x0〉;〈x6,x6〉;〈x0,x7〉;〈x6,xF〉;〈xD,x1〉;〈x8,x2〉;〈x3,x1〉;〈xF,x3〉 ].

ndefinition dTest_random_ex4A ≝
[〈x9,x5〉;〈x9,x1〉;〈x1,x2〉;〈xF,x3〉;〈x4,xF〉;〈x6,xC〉;〈xA,x6〉;〈x8,xE〉;〈xB,x2〉;〈x7,x8〉;〈xD,xE〉;〈x7,x9〉;〈xC,x5〉;〈x2,x2〉;〈xF,x3〉;〈x0,x7〉
;〈xE,x7〉;〈x9,xE〉;〈x9,x2〉;〈x7,x3〉;〈x3,xC〉;〈xA,x1〉;〈xD,xA〉;〈x2,x1〉;〈x2,x3〉;〈x4,x5〉;〈xE,x5〉;〈x7,x4〉;〈x8,x4〉;〈xC,x2〉;〈x6,x8〉;〈x3,x5〉 ].

ndefinition dTest_random_ex4B ≝
[〈x9,xA〉;〈xC,x8〉;〈x2,xE〉;〈x1,xD〉;〈xD,x1〉;〈xA,x6〉;〈xD,xF〉;〈x0,x6〉;〈x7,xF〉;〈x8,xC〉;〈x2,x8〉;〈xF,x6〉;〈xC,x3〉;〈xF,x8〉;〈x6,x2〉;〈xF,x9〉
;〈x5,x7〉;〈x2,x7〉;〈xD,x1〉;〈xD,x3〉;〈x0,xB〉;〈xA,x3〉;〈x8,x7〉;〈x8,x3〉;〈xC,x9〉;〈x1,x4〉;〈xB,x4〉;〈xC,x5〉;〈xE,xD〉;〈x5,x4〉;〈xE,x1〉;〈xB,x9〉 ].

ndefinition dTest_random_ex4C ≝
[〈x2,x9〉;〈x6,xF〉;〈xE,x3〉;〈x0,xD〉;〈xC,xC〉;〈xF,x6〉;〈x0,xD〉;〈x2,x4〉;〈x4,x5〉;〈x6,xE〉;〈xE,x4〉;〈xD,xB〉;〈xF,x9〉;〈xC,x1〉;〈xD,x4〉;〈xB,x4〉
;〈xB,x5〉;〈x6,x6〉;〈x1,xC〉;〈x6,xE〉;〈xA,xF〉;〈x4,x0〉;〈xE,x6〉;〈x4,x9〉;〈x7,xE〉;〈x4,x1〉;〈x1,x8〉;〈x8,x7〉;〈xD,xF〉;〈xB,xB〉;〈x6,x0〉;〈x0,x5〉 ].

ndefinition dTest_random_ex4D ≝
[〈xF,x4〉;〈x5,xD〉;〈xA,x1〉;〈xD,x6〉;〈x6,x7〉;〈x2,xA〉;〈xC,x8〉;〈x7,x7〉;〈xF,x9〉;〈x8,xA〉;〈xF,x9〉;〈x2,x6〉;〈xE,xF〉;〈x7,x4〉;〈x5,x8〉;〈x6,xA〉
;〈xC,x8〉;〈x3,x5〉;〈x1,x0〉;〈xC,x5〉;〈x1,xE〉;〈x0,xB〉;〈x8,x3〉;〈x6,xA〉;〈x4,x4〉;〈x8,xD〉;〈x5,xC〉;〈xF,xB〉;〈xF,xE〉;〈x9,x2〉;〈x0,x3〉;〈x4,x3〉 ].

ndefinition dTest_random_ex4E ≝
[〈x0,x5〉;〈xA,xF〉;〈xC,x0〉;〈xF,x3〉;〈x0,x4〉;〈x2,x8〉;〈x9,xD〉;〈x0,x9〉;〈x3,x5〉;〈xE,x3〉;〈x5,xF〉;〈x4,x5〉;〈xA,xB〉;〈xC,xD〉;〈x8,xC〉;〈xF,xD〉
;〈x2,xC〉;〈x9,xD〉;〈xA,xF〉;〈x6,x4〉;〈x4,x3〉;〈x8,x0〉;〈x8,x2〉;〈xE,x5〉;〈x8,xE〉;〈x3,xD〉;〈x2,xD〉;〈xD,xB〉;〈xD,xF〉;〈xA,xB〉;〈x0,x8〉;〈x1,x6〉 ].

ndefinition dTest_random_ex4F ≝
[〈xE,xC〉;〈x7,xE〉;〈xA,x7〉;〈xC,xB〉;〈xD,x8〉;〈x5,xC〉;〈x2,xC〉;〈x8,x8〉;〈x9,x8〉;〈xC,x2〉;〈xA,xD〉;〈x1,xD〉;〈xB,x0〉;〈xB,x1〉;〈xC,xE〉;〈x9,x3〉
;〈xE,x2〉;〈xF,x4〉;〈xD,xB〉;〈xA,x5〉;〈xB,x6〉;〈x4,x9〉;〈x8,x7〉;〈x1,xD〉;〈xA,x2〉;〈x7,x9〉;〈x3,x5〉;〈xB,xE〉;〈x5,x5〉;〈xC,xD〉;〈x6,x3〉;〈x2,xC〉 ].

ndefinition dTest_random_ex50 ≝
[〈x1,x0〉;〈x1,xF〉;〈xE,xC〉;〈x3,xB〉;〈x8,xA〉;〈x3,xF〉;〈x3,x8〉;〈x8,x0〉;〈x1,xC〉;〈x2,xD〉;〈x9,x2〉;〈x5,xF〉;〈xE,x1〉;〈xB,x5〉;〈xB,xC〉;〈x8,x3〉
;〈xB,x6〉;〈x1,xB〉;〈xE,xD〉;〈x4,xF〉;〈x3,xA〉;〈xC,x4〉;〈xF,xE〉;〈xF,xF〉;〈xC,xB〉;〈x8,x1〉;〈x6,x7〉;〈xC,x2〉;〈x5,x9〉;〈xD,xA〉;〈x0,xA〉;〈x9,xC〉 ].

ndefinition dTest_random_ex51 ≝
[〈x2,x2〉;〈xE,xB〉;〈x9,x3〉;〈xE,x2〉;〈x7,xF〉;〈xA,xC〉;〈x4,xA〉;〈x8,x2〉;〈x8,x1〉;〈x3,xF〉;〈xE,xB〉;〈x8,xB〉;〈x0,xF〉;〈x9,xC〉;〈x4,x1〉;〈x8,x2〉
;〈x9,xB〉;〈x7,xC〉;〈x5,x1〉;〈xA,x7〉;〈xA,xB〉;〈xA,xD〉;〈x9,x2〉;〈x1,x9〉;〈xF,x0〉;〈xF,xD〉;〈x9,x3〉;〈xF,x6〉;〈xA,xD〉;〈x2,x4〉;〈xC,xB〉;〈xD,xE〉 ].

ndefinition dTest_random_ex52 ≝
[〈xB,x5〉;〈xA,xB〉;〈x8,x1〉;〈x5,x4〉;〈xA,xE〉;〈x2,x4〉;〈x6,x4〉;〈xD,x2〉;〈xD,x0〉;〈xF,xE〉;〈x3,x3〉;〈x2,xA〉;〈x7,x5〉;〈x0,x7〉;〈x8,xF〉;〈x3,xA〉
;〈x1,x2〉;〈x9,xF〉;〈xB,xE〉;〈x1,xB〉;〈x1,xB〉;〈x1,xF〉;〈xC,x7〉;〈xF,x1〉;〈x7,xC〉;〈x9,x1〉;〈x5,xD〉;〈x3,x2〉;〈xD,x9〉;〈xD,x6〉;〈xE,xA〉;〈x0,x6〉 ].

ndefinition dTest_random_ex53 ≝
[〈x5,xB〉;〈x6,x9〉;〈x6,xB〉;〈xA,xC〉;〈x0,x9〉;〈x1,x6〉;〈xA,x3〉;〈xC,xA〉;〈x8,xE〉;〈x8,x3〉;〈x3,x4〉;〈xB,x7〉;〈x4,x1〉;〈x2,x7〉;〈xB,x3〉;〈x0,x1〉
;〈xE,x6〉;〈x0,x6〉;〈x8,xC〉;〈x0,x4〉;〈x3,xD〉;〈xB,xE〉;〈x2,xC〉;〈x6,x6〉;〈xB,x5〉;〈x8,x6〉;〈x1,x1〉;〈x1,x3〉;〈x6,xD〉;〈xD,x0〉;〈xB,xE〉;〈x8,xD〉 ].

ndefinition dTest_random_ex54 ≝
[〈xC,x7〉;〈x5,x5〉;〈x0,x2〉;〈xC,x1〉;〈x7,x6〉;〈x5,xF〉;〈x2,x0〉;〈x5,xE〉;〈xE,x4〉;〈x3,xE〉;〈x7,x7〉;〈xE,x1〉;〈x3,xF〉;〈xE,x8〉;〈x6,xC〉;〈x4,xA〉
;〈xA,x0〉;〈xF,xE〉;〈xC,xE〉;〈x3,xF〉;〈x6,x7〉;〈x9,x4〉;〈x3,xF〉;〈xE,xF〉;〈xE,xF〉;〈x8,x6〉;〈xD,x9〉;〈x4,xA〉;〈x0,x8〉;〈x8,xB〉;〈xC,x8〉;〈x1,xC〉 ].

ndefinition dTest_random_ex55 ≝
[〈xA,xD〉;〈x2,x0〉;〈xA,x7〉;〈x8,xC〉;〈x0,x6〉;〈x6,x7〉;〈xA,xF〉;〈x7,x3〉;〈xC,xD〉;〈x1,x6〉;〈x8,x4〉;〈x3,x2〉;〈xD,x0〉;〈xF,x3〉;〈xD,xC〉;〈xD,xB〉
;〈xB,x7〉;〈x2,x4〉;〈x6,xA〉;〈x6,x3〉;〈x1,xC〉;〈xA,x1〉;〈xD,xE〉;〈xB,xC〉;〈x9,x2〉;〈xF,x1〉;〈x5,xC〉;〈xE,x7〉;〈xE,x0〉;〈xD,x5〉;〈xA,x4〉;〈x4,xA〉 ].

ndefinition dTest_random_ex56 ≝
[〈x0,x0〉;〈xD,x6〉;〈x2,x2〉;〈x9,xC〉;〈x5,x2〉;〈x8,xF〉;〈xE,x8〉;〈x2,x2〉;〈xA,x2〉;〈xF,x0〉;〈x9,x8〉;〈x3,x8〉;〈x0,xD〉;〈xF,x6〉;〈x4,x3〉;〈x7,x9〉
;〈x8,x2〉;〈xA,xF〉;〈xD,x5〉;〈xC,x1〉;〈x8,x2〉;〈x5,x2〉;〈xD,xB〉;〈x8,xF〉;〈x7,xE〉;〈xD,x1〉;〈x9,xD〉;〈xA,x6〉;〈x8,xE〉;〈x9,xE〉;〈xA,x9〉;〈x8,xE〉 ].

ndefinition dTest_random_ex57 ≝
[〈xD,x1〉;〈xF,x6〉;〈xB,x0〉;〈xE,xA〉;〈x8,x3〉;〈xE,x9〉;〈xF,x7〉;〈x3,xB〉;〈x4,xA〉;〈x0,x9〉;〈x1,xE〉;〈x3,x2〉;〈xD,x2〉;〈x5,xD〉;〈xD,x7〉;〈xA,xB〉
;〈x4,xD〉;〈x6,xF〉;〈x5,x9〉;〈xF,xC〉;〈x4,x3〉;〈x4,x1〉;〈x0,x0〉;〈x3,xC〉;〈x9,x4〉;〈x5,x2〉;〈x5,x9〉;〈x6,xC〉;〈x6,xE〉;〈xE,x8〉;〈x6,x6〉;〈xF,x5〉 ].

ndefinition dTest_random_ex58 ≝
[〈x9,xC〉;〈x5,x7〉;〈x6,xC〉;〈xE,x2〉;〈x3,xB〉;〈xA,x2〉;〈x2,x1〉;〈xE,xE〉;〈xF,x6〉;〈x4,xF〉;〈xF,x3〉;〈x6,x2〉;〈xD,xB〉;〈x8,xF〉;〈x6,x4〉;〈xD,x3〉
;〈x8,x0〉;〈x6,x9〉;〈x9,x7〉;〈x4,x7〉;〈x8,xB〉;〈xB,x6〉;〈x3,x8〉;〈x4,x5〉;〈xB,xE〉;〈x0,xD〉;〈x6,x1〉;〈xC,xF〉;〈x7,x8〉;〈xC,xF〉;〈x4,x1〉;〈x7,xF〉 ].

ndefinition dTest_random_ex59 ≝
[〈xF,x4〉;〈x5,xA〉;〈x8,xB〉;〈x7,x2〉;〈xE,x6〉;〈x7,xD〉;〈x4,xC〉;〈x1,x8〉;〈xE,xE〉;〈x3,xA〉;〈x1,x2〉;〈x9,x4〉;〈x3,x4〉;〈x3,x0〉;〈x3,x9〉;〈x0,x0〉
;〈x9,x5〉;〈x6,x0〉;〈xF,xA〉;〈x7,xF〉;〈xA,x6〉;〈xC,x7〉;〈xB,x1〉;〈x7,xE〉;〈x0,xD〉;〈x2,x4〉;〈xF,xF〉;〈x4,x3〉;〈x7,x8〉;〈x8,x8〉;〈x6,xC〉;〈x0,x7〉 ].

ndefinition dTest_random_ex5A ≝
[〈x7,x3〉;〈x9,x2〉;〈xC,x8〉;〈x0,xB〉;〈x5,x0〉;〈x9,x7〉;〈xF,x4〉;〈x1,xB〉;〈xD,xB〉;〈x4,x5〉;〈x6,x2〉;〈x9,x1〉;〈x8,x7〉;〈x5,xD〉;〈xF,x5〉;〈x6,x1〉
;〈x3,x8〉;〈xF,x3〉;〈x8,xA〉;〈x4,xF〉;〈xD,xB〉;〈x3,xD〉;〈x4,x3〉;〈x2,xF〉;〈xB,xA〉;〈xA,x9〉;〈xB,x4〉;〈xA,x9〉;〈x2,x6〉;〈x7,xE〉;〈x8,xC〉;〈x1,x6〉 ].

ndefinition dTest_random_ex5B ≝
[〈xF,xC〉;〈x1,xC〉;〈xA,x7〉;〈x9,xD〉;〈x7,xC〉;〈x8,x5〉;〈xA,x7〉;〈x3,x5〉;〈x8,x6〉;〈x4,xF〉;〈xC,x8〉;〈x9,xA〉;〈x0,xD〉;〈x2,x4〉;〈x0,x4〉;〈x5,x8〉
;〈x4,x2〉;〈x3,x0〉;〈x7,x5〉;〈x8,xD〉;〈xB,xC〉;〈x7,x2〉;〈x3,x4〉;〈xF,x9〉;〈x4,x6〉;〈x5,xE〉;〈xF,x4〉;〈x5,xC〉;〈x6,x7〉;〈x0,x4〉;〈x8,x8〉;〈x2,x8〉 ].

ndefinition dTest_random_ex5C ≝
[〈xA,x9〉;〈xE,xC〉;〈xE,xC〉;〈x7,xC〉;〈x4,x6〉;〈x6,xE〉;〈x1,xC〉;〈xD,x9〉;〈xC,x0〉;〈x6,x1〉;〈x5,x8〉;〈x5,xE〉;〈x3,x7〉;〈xB,x0〉;〈x9,x9〉;〈x9,x7〉
;〈xA,x0〉;〈x9,xB〉;〈x7,x7〉;〈x4,xA〉;〈xD,x0〉;〈xB,x5〉;〈x1,xD〉;〈xA,x6〉;〈x4,xA〉;〈xC,x5〉;〈x3,xA〉;〈x9,x4〉;〈xB,x4〉;〈x5,x0〉;〈x0,x6〉;〈xC,x0〉 ].

ndefinition dTest_random_ex5D ≝
[〈xA,x8〉;〈x0,x2〉;〈x5,xF〉;〈x0,xE〉;〈x2,x1〉;〈x0,x3〉;〈xB,x1〉;〈x9,x6〉;〈x0,x2〉;〈x9,x7〉;〈x8,x0〉;〈x1,xA〉;〈x0,xB〉;〈x3,xD〉;〈x2,x1〉;〈x7,xF〉
;〈x0,x3〉;〈x2,x9〉;〈x3,x2〉;〈x6,x6〉;〈xB,xF〉;〈x3,xB〉;〈x5,x7〉;〈x5,x3〉;〈xE,x7〉;〈xD,x5〉;〈xE,x5〉;〈x4,x5〉;〈xA,x3〉;〈x1,xA〉;〈x1,xB〉;〈xF,x8〉 ].

ndefinition dTest_random_ex5E ≝
[〈xC,xF〉;〈xB,x3〉;〈x9,x5〉;〈x5,x9〉;〈x4,xE〉;〈x6,x4〉;〈x4,x3〉;〈xF,x4〉;〈x2,x5〉;〈xC,xC〉;〈x6,x1〉;〈x3,x5〉;〈xD,xF〉;〈x3,x6〉;〈x5,x5〉;〈xC,xF〉
;〈x9,xA〉;〈x1,x1〉;〈xF,x6〉;〈xD,x4〉;〈x4,xF〉;〈x9,xB〉;〈xA,xF〉;〈xF,x2〉;〈x0,x3〉;〈x1,x9〉;〈x9,xB〉;〈xA,xB〉;〈xC,x4〉;〈x1,x9〉;〈xA,x1〉;〈xE,xA〉 ].

ndefinition dTest_random_ex5F ≝
[〈x1,xB〉;〈x2,x5〉;〈xA,xD〉;〈xA,xA〉;〈x0,x0〉;〈x5,xB〉;〈x9,xD〉;〈x6,xF〉;〈x8,x8〉;〈x6,xF〉;〈x3,x0〉;〈x8,x5〉;〈xC,x6〉;〈x1,x7〉;〈x5,x7〉;〈x1,x1〉
;〈xA,xB〉;〈x0,x2〉;〈xD,xD〉;〈x9,x2〉;〈x4,xD〉;〈x8,x2〉;〈x0,x2〉;〈x3,x5〉;〈xC,xB〉;〈x4,x4〉;〈xA,x4〉;〈x4,x1〉;〈xD,x5〉;〈x1,x2〉;〈xE,x7〉;〈x4,xD〉 ].

ndefinition dTest_random_32 ≝ 
 dTest_random_ex00.

ndefinition dTest_random_64 ≝ 
 dTest_random_32@dTest_random_ex01.

ndefinition dTest_random_128 ≝ 
 dTest_random_64@dTest_random_ex02@dTest_random_ex03.

ndefinition dTest_random_256 ≝ 
 dTest_random_128@
 dTest_random_ex04@dTest_random_ex05@dTest_random_ex06@dTest_random_ex07.

ndefinition dTest_random_512 ≝ 
 dTest_random_256@
 dTest_random_ex08@dTest_random_ex09@dTest_random_ex0A@dTest_random_ex0B@
 dTest_random_ex0C@dTest_random_ex0D@dTest_random_ex0E@dTest_random_ex0F.

ndefinition dTest_random_1024 ≝ 
 dTest_random_512@
 dTest_random_ex10@dTest_random_ex11@dTest_random_ex12@dTest_random_ex13@
 dTest_random_ex14@dTest_random_ex15@dTest_random_ex16@dTest_random_ex17@
 dTest_random_ex18@dTest_random_ex19@dTest_random_ex1A@dTest_random_ex1B@
 dTest_random_ex1C@dTest_random_ex1D@dTest_random_ex1E@dTest_random_ex1F.

ndefinition dTest_random_2048 ≝ 
 dTest_random_1024@
 dTest_random_ex20@dTest_random_ex21@dTest_random_ex22@dTest_random_ex23@
 dTest_random_ex24@dTest_random_ex25@dTest_random_ex26@dTest_random_ex27@
 dTest_random_ex28@dTest_random_ex29@dTest_random_ex2A@dTest_random_ex2B@
 dTest_random_ex2C@dTest_random_ex2D@dTest_random_ex2E@dTest_random_ex2F@
 dTest_random_ex30@dTest_random_ex31@dTest_random_ex32@dTest_random_ex33@
 dTest_random_ex34@dTest_random_ex35@dTest_random_ex36@dTest_random_ex37@
 dTest_random_ex38@dTest_random_ex39@dTest_random_ex3A@dTest_random_ex3B@
 dTest_random_ex3C@dTest_random_ex3D@dTest_random_ex3E@dTest_random_ex3F.

ndefinition dTest_random_3072 ≝ 
 dTest_random_2048@
 dTest_random_ex40@dTest_random_ex41@dTest_random_ex42@dTest_random_ex43@
 dTest_random_ex44@dTest_random_ex45@dTest_random_ex46@dTest_random_ex47@
 dTest_random_ex48@dTest_random_ex49@dTest_random_ex4A@dTest_random_ex4B@
 dTest_random_ex4C@dTest_random_ex4D@dTest_random_ex4E@dTest_random_ex4F@
 dTest_random_ex50@dTest_random_ex51@dTest_random_ex52@dTest_random_ex53@
 dTest_random_ex54@dTest_random_ex55@dTest_random_ex56@dTest_random_ex57@
 dTest_random_ex58@dTest_random_ex59@dTest_random_ex5A@dTest_random_ex5B@
 dTest_random_ex5C@dTest_random_ex5D@dTest_random_ex5E@dTest_random_ex5F.

(* campitura di 128 0x00 *)
ndefinition dTest_bytes_aux : list byte8 ≝
[
〈x0,x0〉;〈x0,x0〉;〈x0,x0〉;〈x0,x0〉;〈x0,x0〉;〈x0,x0〉;〈x0,x0〉;〈x0,x0〉;〈x0,x0〉;〈x0,x0〉;〈x0,x0〉;〈x0,x0〉;〈x0,x0〉;〈x0,x0〉;〈x0,x0〉;〈x0,x0〉;
〈x0,x0〉;〈x0,x0〉;〈x0,x0〉;〈x0,x0〉;〈x0,x0〉;〈x0,x0〉;〈x0,x0〉;〈x0,x0〉;〈x0,x0〉;〈x0,x0〉;〈x0,x0〉;〈x0,x0〉;〈x0,x0〉;〈x0,x0〉;〈x0,x0〉;〈x0,x0〉;
〈x0,x0〉;〈x0,x0〉;〈x0,x0〉;〈x0,x0〉;〈x0,x0〉;〈x0,x0〉;〈x0,x0〉;〈x0,x0〉;〈x0,x0〉;〈x0,x0〉;〈x0,x0〉;〈x0,x0〉;〈x0,x0〉;〈x0,x0〉;〈x0,x0〉;〈x0,x0〉;
〈x0,x0〉;〈x0,x0〉;〈x0,x0〉;〈x0,x0〉;〈x0,x0〉;〈x0,x0〉;〈x0,x0〉;〈x0,x0〉;〈x0,x0〉;〈x0,x0〉;〈x0,x0〉;〈x0,x0〉;〈x0,x0〉;〈x0,x0〉;〈x0,x0〉;〈x0,x0〉;
〈x0,x0〉;〈x0,x0〉;〈x0,x0〉;〈x0,x0〉;〈x0,x0〉;〈x0,x0〉;〈x0,x0〉;〈x0,x0〉;〈x0,x0〉;〈x0,x0〉;〈x0,x0〉;〈x0,x0〉;〈x0,x0〉;〈x0,x0〉;〈x0,x0〉;〈x0,x0〉;
〈x0,x0〉;〈x0,x0〉;〈x0,x0〉;〈x0,x0〉;〈x0,x0〉;〈x0,x0〉;〈x0,x0〉;〈x0,x0〉;〈x0,x0〉;〈x0,x0〉;〈x0,x0〉;〈x0,x0〉;〈x0,x0〉;〈x0,x0〉;〈x0,x0〉;〈x0,x0〉;
〈x0,x0〉;〈x0,x0〉;〈x0,x0〉;〈x0,x0〉;〈x0,x0〉;〈x0,x0〉;〈x0,x0〉;〈x0,x0〉;〈x0,x0〉;〈x0,x0〉;〈x0,x0〉;〈x0,x0〉;〈x0,x0〉;〈x0,x0〉;〈x0,x0〉;〈x0,x0〉;
〈x0,x0〉;〈x0,x0〉;〈x0,x0〉;〈x0,x0〉;〈x0,x0〉;〈x0,x0〉;〈x0,x0〉;〈x0,x0〉;〈x0,x0〉;〈x0,x0〉;〈x0,x0〉;〈x0,x0〉;〈x0,x0〉;〈x0,x0〉;〈x0,x0〉;〈x0,x0〉
].

(* blocco di 0x00 lungo 0x0380 da caricare dopo dati per azzerare
   counters, index, position, e stack di esecuzione *)
ndefinition dTest_zeros : list byte8 ≝
 dTest_bytes_aux@dTest_bytes_aux@dTest_bytes_aux@dTest_bytes_aux@dTest_bytes_aux@dTest_bytes_aux@dTest_bytes_aux.

ndefinition dTest_zeros3K : list byte8 ≝
  dTest_bytes_aux@dTest_bytes_aux@dTest_bytes_aux@dTest_bytes_aux@dTest_bytes_aux@dTest_bytes_aux@
  dTest_bytes_aux@dTest_bytes_aux@dTest_bytes_aux@dTest_bytes_aux@dTest_bytes_aux@dTest_bytes_aux@
  dTest_bytes_aux@dTest_bytes_aux@dTest_bytes_aux@dTest_bytes_aux@dTest_bytes_aux@dTest_bytes_aux@
  dTest_bytes_aux@dTest_bytes_aux@dTest_bytes_aux@dTest_bytes_aux@dTest_bytes_aux@dTest_bytes_aux.
