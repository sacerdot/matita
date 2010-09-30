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

include "freescale/byte8.ma".

(* ********************** *)
(* DEFINIZIONE DELLE WORD *)
(* ********************** *)

record word16 : Type ≝
 {
 w16h: byte8;
 w16l: byte8
 }.

(* \langle \rangle *)
notation "〈x:y〉" non associative with precedence 80
 for @{ 'mk_word16 $x $y }.
interpretation "mk_word16" 'mk_word16 x y = (mk_word16 x y).

(* operatore = *)
definition eq_w16 ≝ λw1,w2.(eq_b8 (w16h w1) (w16h w2)) ⊗ (eq_b8 (w16l w1) (w16l w2)).

(* operatore < *)
definition lt_w16 ≝
λw1,w2:word16.match lt_b8 (w16h w1) (w16h w2) with
 [ true ⇒ true
 | false ⇒ match gt_b8 (w16h w1) (w16h w2) with
  [ true ⇒ false
  | false ⇒ lt_b8 (w16l w1) (w16l w2) ]].

(* operatore ≤ *)
definition le_w16 ≝ λw1,w2:word16.(eq_w16 w1 w2) ⊕ (lt_w16 w1 w2).

(* operatore > *)
definition gt_w16 ≝ λw1,w2:word16.⊖ (le_w16 w1 w2).

(* operatore ≥ *)
definition ge_w16 ≝ λw1,w2:word16.⊖ (lt_w16 w1 w2).

(* operatore and *)
definition and_w16 ≝
λw1,w2:word16.mk_word16 (and_b8 (w16h w1) (w16h w2)) (and_b8 (w16l w1) (w16l w2)).

(* operatore or *)
definition or_w16 ≝
λw1,w2:word16.mk_word16 (or_b8 (w16h w1) (w16h w2)) (or_b8 (w16l w1) (w16l w2)).

(* operatore xor *)
definition xor_w16 ≝
λw1,w2:word16.mk_word16 (xor_b8 (w16h w1) (w16h w2)) (xor_b8 (w16l w1) (w16l w2)).

(* operatore rotazione destra con carry *)
definition rcr_w16 ≝
λw:word16.λc:bool.match rcr_b8 (w16h w) c with
 [ pair wh' c' ⇒ match rcr_b8 (w16l w) c' with
  [ pair wl' c'' ⇒ pair ?? (mk_word16 wh' wl') c'' ]]. 

(* operatore shift destro *)
definition shr_w16 ≝
λw:word16.match rcr_b8 (w16h w) false with
 [ pair wh' c' ⇒ match rcr_b8 (w16l w) c' with
  [ pair wl' c'' ⇒ pair ?? (mk_word16 wh' wl') c'' ]].

(* operatore rotazione destra *)
definition ror_w16 ≝
λw:word16.match rcr_b8 (w16h w) false with
 [ pair wh' c' ⇒ match rcr_b8 (w16l w) c' with
  [ pair wl' c'' ⇒ match c'' with
   [ true ⇒ mk_word16 (or_b8 (mk_byte8 x8 x0) wh') wl'
   | false ⇒ mk_word16 wh' wl' ]]].

(* operatore rotazione destra n-volte *)
let rec ror_w16_n (w:word16) (n:nat) on n ≝
 match n with
  [ O ⇒ w
  | S n' ⇒ ror_w16_n (ror_w16 w) n' ].

(* operatore rotazione sinistra con carry *)
definition rcl_w16 ≝
λw:word16.λc:bool.match rcl_b8 (w16l w) c with
 [ pair wl' c' ⇒ match rcl_b8 (w16h w) c' with
  [ pair wh' c'' ⇒ pair ?? (mk_word16 wh' wl') c'' ]]. 

(* operatore shift sinistro *)
definition shl_w16 ≝
λw:word16.match rcl_b8 (w16l w) false with
 [ pair wl' c' ⇒ match rcl_b8 (w16h w) c' with
  [ pair wh' c'' ⇒ pair ?? (mk_word16 wh' wl') c'' ]].

(* operatore rotazione sinistra *)
definition rol_w16 ≝
λw:word16.match rcl_b8 (w16l w) false with
 [ pair wl' c' ⇒ match rcl_b8 (w16h w) c' with
  [ pair wh' c'' ⇒ match c'' with
   [ true ⇒ mk_word16 wh' (or_b8 (mk_byte8 x0 x1) wl')
   | false ⇒ mk_word16 wh' wl' ]]].

(* operatore rotazione sinistra n-volte *)
let rec rol_w16_n (w:word16) (n:nat) on n ≝
 match n with
  [ O ⇒ w
  | S n' ⇒ rol_w16_n (rol_w16 w) n' ].

(* operatore not/complemento a 1 *)
definition not_w16 ≝
λw:word16.mk_word16 (not_b8 (w16h w)) (not_b8 (w16l w)).

(* operatore somma con carry *)
definition plus_w16 ≝
λw1,w2:word16.λc:bool.
 match plus_b8 (w16l w1) (w16l w2) c with
  [ pair l c' ⇒ match plus_b8 (w16h w1) (w16h w2) c' with
   [ pair h c'' ⇒ pair ?? (mk_word16 h l) c'' ]].

(* operatore somma senza carry *)
definition plus_w16nc ≝
λw1,w2:word16.fst ?? (plus_w16 w1 w2 false).

(* operatore carry della somma *)
definition plus_w16c ≝
λw1,w2:word16.snd ?? (plus_w16 w1 w2 false).

(* operatore Most Significant Bit *)
definition MSB_w16 ≝ λw:word16.eq_ex x8 (and_ex x8 (b8h (w16h w))).

(* word → naturali *)
definition nat_of_word16 ≝ λw:word16. 256 * (w16h w) + (nat_of_byte8 (w16l w)).

coercion nat_of_word16.

(* naturali → word *)
definition word16_of_nat ≝
 λn.mk_word16 (byte8_of_nat (n / 256)) (byte8_of_nat n).

(* operatore predecessore *)
definition pred_w16 ≝
λw:word16.match eq_b8 (w16l w) (mk_byte8 x0 x0) with
 [ true ⇒ mk_word16 (pred_b8 (w16h w)) (pred_b8 (w16l w))
 | false ⇒ mk_word16 (w16h w) (pred_b8 (w16l w)) ].

(* operatore successore *)
definition succ_w16 ≝
λw:word16.match eq_b8 (w16l w) (mk_byte8 xF xF) with
 [ true ⇒ mk_word16 (succ_b8 (w16h w)) (succ_b8 (w16l w))
 | false ⇒ mk_word16 (w16h w) (succ_b8 (w16l w)) ].

(* operatore neg/complemento a 2 *)
definition compl_w16 ≝
λw:word16.match MSB_w16 w with
 [ true ⇒ succ_w16 (not_w16 w)
 | false ⇒ not_w16 (pred_w16 w) ].

(* 
   operatore moltiplicazione senza segno: b*b=[0x0000,0xFE01]
   ... in pratica (〈a,b〉*〈c,d〉) = (a*c)<<8+(a*d)<<4+(b*c)<<4+(b*d)
*)
definition mul_b8 ≝
λb1,b2:byte8.match b1 with
[ mk_byte8 b1h b1l ⇒ match b2 with
[ mk_byte8 b2h b2l ⇒ match mul_ex b1l b2l with
[ mk_byte8 t1_h t1_l ⇒ match mul_ex b1h b2l with
[ mk_byte8 t2_h t2_l ⇒ match mul_ex b2h b1l with
[ mk_byte8 t3_h t3_l ⇒ match mul_ex b1h b2h with
[ mk_byte8 t4_h t4_l ⇒
 plus_w16nc
  (plus_w16nc
   (plus_w16nc 〈〈t4_h,t4_l〉:〈x0,x0〉〉 〈〈x0,t3_h〉:〈t3_l,x0〉〉) 〈〈x0,t2_h〉:〈t2_l,x0〉〉)〈〈x0,x0〉:〈t1_h,t1_l〉〉
]]]]]].

(* divisione senza segno (secondo la logica delle ALU): (quoziente resto) overflow *)
definition div_b8 ≝
λw:word16.λb:byte8.match eq_b8 b 〈x0,x0〉 with
(* 
   la combinazione n/0 e' illegale, segnala solo overflow senza dare risultato
*)
 [ true ⇒ tripleT ??? 〈xF,xF〉 (w16l w) true
 | false ⇒ match eq_w16 w 〈〈x0,x0〉:〈x0,x0〉〉 with
(* 0 diviso qualsiasi cosa diverso da 0 da' q=0 r=0 o=false *)
  [ true ⇒ tripleT ??? 〈x0,x0〉 〈x0,x0〉 false
(* 1) e' una divisione sensata che produrra' overflow/risultato *)
(* 2) parametri: dividendo, divisore, moltiplicatore, quoziente, contatore *)
(* 3) ad ogni ciclo il divisore e il moltiplicatore vengono scalati di 1 a dx *)
(* 4) il moltiplicatore e' la quantita' aggiunta al quoziente se il divisore *)
(*    puo' essere sottratto al dividendo *) 
  | false ⇒ let rec aux (divd:word16) (divs:word16) (molt:byte8) (q:byte8) (c:nat) on c ≝
  let w' ≝ plus_w16nc divd (compl_w16 divs) in
   match c with
   [ O ⇒ match le_w16 divs divd with
    [ true ⇒ tripleT ??? (or_b8 molt q) (w16l w') (⊖ (eq_b8 (w16h w') 〈x0,x0〉))
    | false ⇒ tripleT ??? q (w16l divd) (⊖ (eq_b8 (w16h divd) 〈x0,x0〉)) ]
   | S c' ⇒ match le_w16 divs divd with
    [ true ⇒ aux w' (ror_w16 divs) (ror_b8 molt) (or_b8 molt q) c'
    | false ⇒ aux divd (ror_w16 divs) (ror_b8 molt) q c' ]]
  in aux w (rol_w16_n 〈〈x0,x0〉:b〉 7) 〈x8,x0〉 〈x0,x0〉 7 ]].

(* operatore x in [inf,sup] *)
definition in_range ≝
λx,inf,sup:word16.(le_w16 inf sup) ⊗ (ge_w16 x inf) ⊗ (le_w16 x sup).

(* iteratore sulle word *)
definition forall_word16 ≝
 λP.
  forall_byte8 (λbh.
  forall_byte8 (λbl.
   P (mk_word16 bh bl ))).

(* ********************** *)
(* TEOREMI/LEMMMI/ASSIOMI *)
(* ********************** *)

(* TODO: dimostrare diversamente *)
axiom word16_of_nat_nat_of_word16: ∀b. word16_of_nat (nat_of_word16 b) = b.

(* TODO: dimostrare diversamente *)
axiom lt_nat_of_word16_65536: ∀b. nat_of_word16 b < (256 * 256).

(* TODO: dimostrare diversamente *)
axiom nat_of_word16_word16_of_nat: ∀n. nat_of_word16 (word16_of_nat n) = n \mod (256 * 256).

(* TODO: dimostrare diversamente *)
axiom eq_nat_of_word16_n_nat_of_word16_mod_n_65536:
 ∀n. word16_of_nat n = word16_of_nat (n \mod (256 * 256)).

lemma plusw16_ok:
 ∀b1,b2,c.
  match plus_w16 b1 b2 c with
   [ pair r c' ⇒ b1 + b2 + nat_of_bool c = nat_of_word16 r + nat_of_bool c' * (256 * 256)
   ].
 intros; elim daemon.
qed.

(* TODO: dimostrare diversamente *)
axiom plusw16_O_x:
 ∀b. plus_w16 (mk_word16 (mk_byte8 x0 x0) (mk_byte8 x0 x0)) b false = pair ?? b false.

lemma plusw16nc_O_x:
 ∀x. plus_w16nc (mk_word16 (mk_byte8 x0 x0) (mk_byte8 x0 x0)) x = x.
 intros;
 unfold plus_w16nc;
 rewrite > plusw16_O_x;
 reflexivity.
qed.

(* TODO: dimostrare diversamente *)
axiom eq_nat_of_word16_mod: ∀b. nat_of_word16 b = nat_of_word16 b \mod (256 * 256).

(* TODO: dimostrare diversamente *)
axiom plusw16nc_ok:
 ∀b1,b2:word16. nat_of_word16 (plus_w16nc b1 b2) = (b1 + b2) \mod (256 * 256).

(* TODO: dimostrare diversamente *)
axiom eq_eqw16_x0_x0_x0_x0_word16_of_nat_S_false:
 ∀b. b < (256 * 256 - 1) → eq_w16 (mk_word16 (mk_byte8 x0 x0) (mk_byte8 x0 x0)) (word16_of_nat (S b)) = false.

axiom eq_mod_O_to_exists: ∀n,m. n \mod m = 0 → ∃z. n = z*m.

(* TODO: dimostrare diversamente *)
axiom eq_w16pred_S_a_a:
 ∀a. a < (256 * 256 - 1) → pred_w16 (word16_of_nat (S a)) = word16_of_nat a.

(* TODO: dimostrare diversamente *)
axiom plusw16nc_S:
 ∀x:word16.∀n.plus_w16nc (word16_of_nat (x*n)) x = word16_of_nat (x * S n).

(* TODO: dimostrare diversamente *)
axiom eq_plusw16c_x0_x0_x0_x0_x_false:
 ∀x.plus_w16c (mk_word16 (mk_byte8 x0 x0) (mk_byte8 x0 x0)) x = false.

(* TODO: dimostrare diversamente *)
axiom eqw16_true_to_eq: ∀b,b'. eq_w16 b b' = true → b=b'.

(* TODO: dimostrare diversamente *)
axiom eqw16_false_to_not_eq: ∀b,b'. eq_w16 b b' = false → b ≠ b'.

(* TODO: dimostrare diversamente *)
axiom word16_of_nat_mod: ∀n.word16_of_nat n = word16_of_nat (n \mod (256 * 256)).

(* nuovi *)

(*
lemma ok_mul_b8: ∀b1,b2:byte8. nat_of_word16 (mul_b8 b1 b2) = b1 * b2.
 intros;
 cases b1 (b1h b1l);
 cases b2 (b2h b2l);
 change in ⊢ (? ? (? %) ?) with
  (match mul_ex b1l b2l with
[ mk_byte8 t1_h t1_l ⇒ match mul_ex b1h b2l with
[ mk_byte8 t2_h t2_l ⇒ match mul_ex b2h b1l with
[ mk_byte8 t3_h t3_l ⇒ match mul_ex b1h b2h with
[ mk_byte8 t4_h t4_l ⇒
 plus_w16nc
  (plus_w16nc
   (plus_w16nc 〈〈t4_h,t4_l〉:〈x0,x0〉〉 〈〈x0,t3_h〉:〈t3_l,x0〉〉) 〈〈x0,t2_h〉:〈t2_l,x0〉〉)〈〈x0,x0〉:〈t1_h,t1_l〉〉
]]]]);
 lapply (ok_mul_ex b1l b2l) as ll;
 lapply (ok_mul_ex b1h b2l) as hl;
 lapply (ok_mul_ex b2h b1l) as lh;
 lapply (ok_mul_ex b1h b2h) as hh;
 elim (mul_ex b1l b2l) (t1_h t1_l);
 change in ⊢ (? ? (? %) ?) with
  (match mul_ex b1h b2l with
[ mk_byte8 t2_h t2_l ⇒ match mul_ex b2h b1l with
[ mk_byte8 t3_h t3_l ⇒ match mul_ex b1h b2h with
[ mk_byte8 t4_h t4_l ⇒
 plus_w16nc
  (plus_w16nc
   (plus_w16nc 〈〈t4_h,t4_l〉:〈x0,x0〉〉 〈〈x0,t3_h〉:〈t3_l,x0〉〉) 〈〈x0,t2_h〉:〈t2_l,x0〉〉)〈〈x0,x0〉:〈t1_h,t1_l〉〉
]]]);
 elim (mul_ex b1h b2l) (t2_h t2_l);
 change in ⊢ (? ? (? %) ?) with
  (match mul_ex b2h b1l with
[ mk_byte8 t3_h t3_l ⇒ match mul_ex b1h b2h with
[ mk_byte8 t4_h t4_l ⇒
 plus_w16nc
  (plus_w16nc
   (plus_w16nc 〈〈t4_h,t4_l〉:〈x0,x0〉〉 〈〈x0,t3_h〉:〈t3_l,x0〉〉) 〈〈x0,t2_h〉:〈t2_l,x0〉〉)〈〈x0,x0〉:〈t1_h,t1_l〉〉
]]);
 elim (mul_ex b2h b1l) (t3_h t3_l);
 change in ⊢ (? ? (? %) ?) with
  (match mul_ex b1h b2h with
[ mk_byte8 t4_h t4_l ⇒
 plus_w16nc
  (plus_w16nc
   (plus_w16nc 〈〈t4_h,t4_l〉:〈x0,x0〉〉 〈〈x0,t3_h〉:〈t3_l,x0〉〉) 〈〈x0,t2_h〉:〈t2_l,x0〉〉)〈〈x0,x0〉:〈t1_h,t1_l〉〉
]);
 elim (mul_ex b1h b2h) (t4_h t4_l);
 change in ⊢ (? ? (? %) ?) with
  (plus_w16nc
  (plus_w16nc
   (plus_w16nc 〈〈t4_h,t4_l〉:〈x0,x0〉〉 〈〈x0,t3_h〉:〈t3_l,x0〉〉) 〈〈x0,t2_h〉:〈t2_l,x0〉〉)〈〈x0,x0〉:〈t1_h,t1_l〉〉);
 do 3 (rewrite > plusw16nc_ok);
 unfold nat_of_word16;
 unfold nat_of_byte8;
simplify in ⊢ (? ? (? (? (? (? (? (? (? (? ? (? (? ? (? (? %))) ?)) ?) ?) ?) ?) ?) ?) ?) ?);
simplify in ⊢ (? ? (? (? (? (? (? (? (? ? (? (? ? (? (? %))) ?)) ?) ?) ?) ?) ?) ?) ?);
simplify in ⊢ (? ? (? (? (? (? (? (? (? ? (? ? (? (? %)))) ?) ?) ?) ?) ?) ?) ?);
whd in ⊢ (? ? (? (? (? (? (? (? (? ? (? ? %)) ?) ?) ?) ?) ?) ?) ?);
whd in ⊢ (? ? (? (? (? (? (? (? (? ? %) ?) ?) ?) ?) ?) ?) ?);
simplify in ⊢ (? ? (? (? ? (? (? ? (? (? ? (? %)) ?)) ?)) ?) ?);
simplify in ⊢ (? ? (? (? ? (? (? ? (? ? (? (? %)))) ?)) ?) ?);
simplify in ⊢ (? ? (? (? ? (? (? ? (? ? %)) ?)) ?) ?);
whd in ⊢ (? ? (? (? ? (? % ?)) ?) ?);
simplify in ⊢ (? ? (? (? ? (? ? (? (? ? (? (? %))) ?))) ?) ?);
simplify in ⊢ (? ? (? (? ? (? ? (? ? (? (? %))))) ?) ?);
simplify in ⊢ (? ? ? (? (? (? ? (? %)) ?) ?));
simplify in ⊢ (? ? ? (? (? ? (? %)) ?));
simplify in ⊢ (? ? ? (? ? (? (? ? (? %)) ?)));
simplify in ⊢ (? ? ? (? ? (? ? (? %))));
simplify in ⊢ (? ? (? (? ? (? ? (? (? ? (? %)) ?))) ?) ?);
simplify in ⊢ (? ? (? (? ? (? ? (? ? (? %)))) ?) ?);
simplify in ⊢ (? ? (? (? (? (? ? (? ? (? ? (? %)))) ?) ?) ?) ?);
simplify in ⊢ (? ? (? (? (? (? ? (? ? (? (? ? (? %)) ?))) ?) ?) ?) ?);
simplify in ⊢ (? ? (? (? (? (? ? (? (? ? (? ? (? %))) ?)) ?) ?) ?) ?);
simplify in ⊢ (? ? (? (? (? (? ? (? (? ? (? (? ? (? %)) ?)) ?)) ?) ?) ?) ?);
simplify in ⊢ (? ? (? (? (? (? (? (? ? (? ? (? ? (? %)))) ?) ?) ?) ?) ?) ?);
simplify in ⊢ (? ? (? (? (? (? (? (? ? (? (? ? (? ? (? %))) ?)) ?) ?) ?) ?) ?) ?);
simplify in ⊢ (? ? (? (? (? (? (? (? (? (? ? (? (? ? (? %)) ?)) ?) ?) ?) ?) ?) ?) ?) ?);
simplify in ⊢ (? ? (? (? (? (? (? (? (? (? ? (? ? (? %))) ?) ?) ?) ?) ?) ?) ?) ?);
simplify in ⊢ (? ? (? (? (? (? (? (? ? (? ? (? (? ? (? %)) ?))) ?) ?) ?) ?) ?) ?);
simplify in ⊢ (? ? (? (? (? (? (? (? ? (? (? ? (? (? ? (? %)) ?)) ?)) ?) ?) ?) ?) ?) ?);
rewrite < plus_n_O;
change in ⊢ (? ? (? (? ? %) ?) ?) with (16*nat_of_exadecim t1_h+nat_of_exadecim t1_l);
unfold nat_of_byte8 in H H1 H2 H3;
simplify in ⊢ (? ? (? (? (? (? (? (? ? (? (? ? (? (? ? %) ?)) ?)) ?) ?) ?) ?) ?) ?);
simplify in ⊢ (? ? (? (? (? (? (? (? ? (? ? (? ? %))) ?) ?) ?) ?) ?) ?);
simplify in ⊢ (? ? (? (? (? (? ? (? (? ? (? (? ? %) ?)) ?)) ?) ?) ?) ?);
simplify in ⊢ (? ? (? (? (? (? ? (? ? (? ? %))) ?) ?) ?) ?);
rewrite < plus_n_O;
rewrite < plus_n_O;
simplify in ⊢ (? ? (? (? (? (? (? (? ? (? (? ? %) ?)) ?) ?) ?) ?) ?) ?);
simplify in ⊢ (? ? (? (? (? (? ? (? (? ? %) ?)) ?) ?) ?) ?);
elim daemon.
qed.
*)
