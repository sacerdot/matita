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
(*                                                                        *)
(* Sviluppato da:                                                         *)
(*   Cosimo Oliboni, oliboni@cs.unibo.it                                  *)
(*                                                                        *)
(* ********************************************************************** *)

include "freescale/word16.ma".

(* *********************** *)
(* DEFINIZIONE DELLE DWORD *)
(* *********************** *)

record word32 : Type ≝
 {
 w32h: word16;
 w32l: word16
 }.

(* \langle \rangle *)
notation "〈x.y〉" non associative with precedence 80
 for @{ 'mk_word32 $x $y }.
interpretation "mk_word32" 'mk_word32 x y = (mk_word32 x y).

(* operatore = *)
definition eq_w32 ≝ λw1,w2.(eq_w16 (w32h w1) (w32h w2)) ⊗ (eq_w16 (w32l w1) (w32l w2)).

(* operatore < *)
definition lt_w32 ≝
λw1,w2:word32.match lt_w16 (w32h w1) (w32h w2) with
 [ true ⇒ true
 | false ⇒ match gt_w16 (w32h w1) (w32h w2) with
  [ true ⇒ false
  | false ⇒ lt_w16 (w32l w1) (w32l w2) ]].

(* operatore ≤ *)
definition le_w32 ≝ λw1,w2:word32.(eq_w32 w1 w2) ⊕ (lt_w32 w1 w2).

(* operatore > *)
definition gt_w32 ≝ λw1,w2:word32.⊖ (le_w32 w1 w2).

(* operatore ≥ *)
definition ge_w32 ≝ λw1,w2:word32.⊖ (lt_w32 w1 w2).

(* operatore and *)
definition and_w32 ≝
λw1,w2:word32.mk_word32 (and_w16 (w32h w1) (w32h w2)) (and_w16 (w32l w1) (w32l w2)).

(* operatore or *)
definition or_w32 ≝
λw1,w2:word32.mk_word32 (or_w16 (w32h w1) (w32h w2)) (or_w16 (w32l w1) (w32l w2)).

(* operatore xor *)
definition xor_w32 ≝
λw1,w2:word32.mk_word32 (xor_w16 (w32h w1) (w32h w2)) (xor_w16 (w32l w1) (w32l w2)).

(* operatore rotazione destra con carry *)
definition rcr_w32 ≝
λw:word32.λc:bool.match rcr_w16 (w32h w) c with
 [ pair wh' c' ⇒ match rcr_w16 (w32l w) c' with
  [ pair wl' c'' ⇒ pair ?? (mk_word32 wh' wl') c'' ]]. 

(* operatore shift destro *)
definition shr_w32 ≝
λw:word32.match rcr_w16 (w32h w) false with
 [ pair wh' c' ⇒ match rcr_w16 (w32l w) c' with
  [ pair wl' c'' ⇒ pair ?? (mk_word32 wh' wl') c'' ]].

(* operatore rotazione destra *)
definition ror_w32 ≝
λw:word32.match rcr_w16 (w32h w) false with
 [ pair wh' c' ⇒ match rcr_w16 (w32l w) c' with
  [ pair wl' c'' ⇒ match c'' with
   [ true ⇒ mk_word32 (or_w16 (mk_word16 (mk_byte8 x8 x0) (mk_byte8 x0 x0)) wh') wl'
   | false ⇒ mk_word32 wh' wl' ]]].

(* operatore rotazione destra n-volte *)
let rec ror_w32_n (w:word32) (n:nat) on n ≝
 match n with
  [ O ⇒ w
  | S n' ⇒ ror_w32_n (ror_w32 w) n' ].

(* operatore rotazione sinistra con carry *)
definition rcl_w32 ≝
λw:word32.λc:bool.match rcl_w16 (w32l w) c with
 [ pair wl' c' ⇒ match rcl_w16 (w32h w) c' with
  [ pair wh' c'' ⇒ pair ?? (mk_word32 wh' wl') c'' ]]. 

(* operatore shift sinistro *)
definition shl_w32 ≝
λw:word32.match rcl_w16 (w32l w) false with
 [ pair wl' c' ⇒ match rcl_w16 (w32h w) c' with
  [ pair wh' c'' ⇒ pair ?? (mk_word32 wh' wl') c'' ]].

(* operatore rotazione sinistra *)
definition rol_w32 ≝
λw:word32.match rcl_w16 (w32l w) false with
 [ pair wl' c' ⇒ match rcl_w16 (w32h w) c' with
  [ pair wh' c'' ⇒ match c'' with
   [ true ⇒ mk_word32 wh' (or_w16 (mk_word16 (mk_byte8 x0 x0) (mk_byte8 x0 x1)) wl')
   | false ⇒ mk_word32 wh' wl' ]]].

(* operatore rotazione sinistra n-volte *)
let rec rol_w32_n (w:word32) (n:nat) on n ≝
 match n with
  [ O ⇒ w
  | S n' ⇒ rol_w32_n (rol_w32 w) n' ].

(* operatore not/complemento a 1 *)
definition not_w32 ≝
λw:word32.mk_word32 (not_w16 (w32h w)) (not_w16 (w32l w)).

(* operatore somma con carry *)
definition plus_w32 ≝
λw1,w2:word32.λc:bool.
 match plus_w16 (w32l w1) (w32l w2) c with
  [ pair l c' ⇒ match plus_w16 (w32h w1) (w32h w2) c' with
   [ pair h c'' ⇒ pair ?? (mk_word32 h l) c'' ]].

(* operatore somma senza carry *)
definition plus_w32nc ≝
λw1,w2:word32.fst ?? (plus_w32 w1 w2 false).

(* operatore carry della somma *)
definition plus_w32c ≝
λw1,w2:word32.snd ?? (plus_w32 w1 w2 false).

(* operatore Most Significant Bit *)
definition MSB_w32 ≝ λw:word32.eq_ex x8 (and_ex x8 (b8h (w16h (w32h w)))).

(* word → naturali *)
definition nat_of_word32 ≝ λw:word32. (256 * 256 * (w32h w)) + (nat_of_word16 (w32l w)).

coercion nat_of_word32.

(* naturali → word *)
definition word32_of_nat ≝
 λn.mk_word32 (word16_of_nat (n / (256*256))) (word16_of_nat n).

(* operatore predecessore *)
definition pred_w32 ≝
λw:word32.match eq_w16 (w32l w) (mk_word16 (mk_byte8 x0 x0) (mk_byte8 x0 x0)) with
 [ true ⇒ mk_word32 (pred_w16 (w32h w)) (pred_w16 (w32l w))
 | false ⇒ mk_word32 (w32h w) (pred_w16 (w32l w)) ].

(* operatore successore *)
definition succ_w32 ≝
λw:word32.match eq_w16 (w32l w) (mk_word16 (mk_byte8 xF xF) (mk_byte8 xF xF)) with
 [ true ⇒ mk_word32 (succ_w16 (w32h w)) (succ_w16 (w32l w))
 | false ⇒ mk_word32 (w32h w) (succ_w16 (w32l w)) ].

(* operatore neg/complemento a 2 *)
definition compl_w32 ≝
λw:word32.match MSB_w32 w with
 [ true ⇒ succ_w32 (not_w32 w)
 | false ⇒ not_w32 (pred_w32 w) ].

(* 
   operatore moltiplicazione senza segno: b*b=[0x00000000,0xFFFE0001]
   ... in pratica (〈a:b〉*〈c:d〉) = (a*c)<<16+(a*d)<<8+(b*c)<<8+(b*d)
*)
definition mul_w16 ≝
λb1,b2:word16.match b1 with
[ mk_word16 b1h b1l ⇒ match b2 with
[ mk_word16 b2h b2l ⇒ match mul_b8 b1l b2l with
[ mk_word16 t1_h t1_l ⇒ match mul_b8 b1h b2l with
[ mk_word16 t2_h t2_l ⇒ match mul_b8 b2h b1l with
[ mk_word16 t3_h t3_l ⇒ match mul_b8 b1h b2h with
[ mk_word16 t4_h t4_l ⇒
 plus_w32nc
  (plus_w32nc
   (plus_w32nc 〈〈t4_h:t4_l〉.〈〈x0,x0〉:〈x0,x0〉〉〉 〈〈〈x0,x0〉:t3_h〉.〈t3_l:〈x0,x0〉〉〉) 〈〈〈x0,x0〉:t2_h〉.〈t2_l:〈x0,x0〉〉〉)〈〈〈x0,x0〉:〈x0,x0〉〉.〈t1_h:t1_l〉〉
]]]]]].

(* divisione senza segno (secondo la logica delle ALU): (quoziente resto) overflow *)
definition div_w16 ≝
λw:word32.λb:word16.match eq_w16 b 〈〈x0,x0〉:〈x0,x0〉〉 with
(* 
   la combinazione n/0 e' illegale, segnala solo overflow senza dare risultato
*)
 [ true ⇒ tripleT ??? 〈〈xF,xF〉:〈xF,xF〉〉 (w32l w) true
 | false ⇒ match eq_w32 w 〈〈〈x0,x0〉:〈x0,x0〉〉.〈〈x0,x0〉:〈x0,x0〉〉〉 with
(* 0 diviso qualsiasi cosa diverso da 0 da' q=0 r=0 o=false *)
  [ true ⇒ tripleT ??? 〈〈x0,x0〉:〈x0,x0〉〉 〈〈x0,x0〉:〈x0,x0〉〉 false
(* 1) e' una divisione sensata che produrra' overflow/risultato *)
(* 2) parametri: dividendo, divisore, moltiplicatore, quoziente, contatore *)
(* 3) ad ogni ciclo il divisore e il moltiplicatore vengono scalati di 1 a dx *)
(* 4) il moltiplicatore e' la quantita' aggiunta al quoziente se il divisore *)
(*    puo' essere sottratto al dividendo *) 
  | false ⇒ let rec aux (divd:word32) (divs:word32) (molt:word16) (q:word16) (c:nat) on c ≝
  let w' ≝ plus_w32nc divd (compl_w32 divs) in
   match c with
   [ O ⇒ match le_w32 divs divd with
    [ true ⇒ tripleT ??? (or_w16 molt q) (w32l w') (⊖ (eq_w16 (w32h w') 〈〈x0,x0〉:〈x0,x0〉〉))
    | false ⇒ tripleT ??? q (w32l divd) (⊖ (eq_w16 (w32h divd) 〈〈x0,x0〉:〈x0,x0〉〉)) ]
   | S c' ⇒ match le_w32 divs divd with
    [ true ⇒ aux w' (ror_w32 divs) (ror_w16 molt) (or_w16 molt q) c'
    | false ⇒ aux divd (ror_w32 divs) (ror_w16 molt) q c' ]]
  in aux w (rol_w32_n 〈〈〈x0,x0〉:〈x0,x0〉〉.b〉 15) 〈〈x8,x0〉:〈x0,x0〉〉 〈〈x0,x0〉:〈x0,x0〉〉 15 ]].

(* operatore x in [inf,sup] *)
definition in_range ≝
λx,inf,sup:word32.(le_w32 inf sup) ⊗ (ge_w32 x inf) ⊗ (le_w32 x sup).

(* iteratore sulle word *)
definition forall_word32 ≝
 λP.
  forall_word16 (λbh.
  forall_word16 (λbl.
   P (mk_word32 bh bl ))).
