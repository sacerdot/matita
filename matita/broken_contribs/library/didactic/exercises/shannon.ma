(**************************************************************************)
(*       ___	                                                          *)
(*      ||M||                                                             *)
(*      ||A||       A project by Andrea Asperti                           *)
(*      ||T||                                                             *)
(*      ||I||       Developers:                                           *)
(*      ||T||       A.Asperti, C.Sacerdoti Coen,                          *)
(*      ||A||       E.Tassi, S.Zacchiroli                                 *)
(*      \   /                                                             *)
(*       \ /        This file is distributed under the terms of the       *)
(*        v         GNU Lesser General Public License Version 2.1         *)
(*                                                                        *)
(**************************************************************************)

(* Esercizio 0
   ===========

   Compilare i seguenti campi:

   Nome1: ...
   Cognome1: ...
   Matricola1: ...
   Account1: ...

   Nome2: ...
   Cognome2: ...
   Matricola2: ...
   Account2: ...

*)

(* ATTENZIONE
   ==========
   
   Non modificare quanto segue 
*)
include "nat/minus.ma".
definition if_then_else ≝ λT:Type.λe,t,f.match e return λ_.T with [ true ⇒ t | false ⇒ f].
notation > "'if' term 19 e 'then' term 19 t 'else' term 90 f" non associative with precedence 19 for @{ 'if_then_else $e $t $f }.
notation < "'if' \nbsp term 19 e \nbsp 'then' \nbsp term 19 t \nbsp 'else' \nbsp term 90 f \nbsp" non associative with precedence 19 for @{ 'if_then_else $e $t $f }.
interpretation "Formula if_then_else" 'if_then_else e t f = (if_then_else ? e t f).
definition max ≝ λn,m. if eqb (n - m) 0 then m else n. 
definition min ≝ λn,m. if eqb (n - m) 0 then n else m. 

(* Ripasso 1
   =========
   
   Il linguaggio delle formule, dove gli atomi sono
   rapperesentati da un numero naturale
*)
inductive Formula : Type ≝
| FBot: Formula
| FTop: Formula
| FAtom: nat → Formula
| FAnd: Formula → Formula → Formula
| FOr: Formula → Formula → Formula
| FImpl: Formula → Formula → Formula
| FNot: Formula → Formula
.

(* Ripasso 2
   =========
   
   La semantica di una formula `F` in un mondo `v`: `[[ F ]]v` 
*)
let rec sem (v: nat → nat) (F: Formula) on F : nat ≝
 match F with
  [ FBot ⇒ 0
  | FTop ⇒ 1
  | FAtom n ⇒ min (v n) 1
  | FAnd F1 F2 ⇒ min (sem v F1) (sem v F2)
  | FOr F1 F2 ⇒ max (sem v F1) (sem v F2)
  | FImpl F1 F2 ⇒ max (1 - sem v F1) (sem v F2)
  | FNot F1 ⇒ 1 - (sem v F1)
  ]
.

(* ATTENZIONE
   ==========
   
   Non modificare quanto segue.
*)
notation < "[[ \nbsp term 19 a \nbsp ]] \nbsp \sub term 90 v" non associative with precedence 90 for @{ 'semantics $v $a }.
notation > "[[ term 19 a ]] \sub term 90 v" non associative with precedence 90 for @{ 'semantics $v $a }.
notation > "[[ term 19 a ]] term 90 v" non associative with precedence 90 for @{ sem $v $a }.
interpretation "Semantic of Formula" 'semantics v a = (sem v a).
lemma sem_bool : ∀F,v. [[ F ]]v = 0 ∨ [[ F ]]v = 1.  intros; elim F; simplify; [left;reflexivity; |right;reflexivity; |cases (v n);[left;|cases n1;right;]reflexivity; |4,5,6: cases H; cases H1; rewrite > H2; rewrite > H3; simplify; first [ left;reflexivity | right; reflexivity ].  |cases H; rewrite > H1; simplify;[right|left]reflexivity;] qed.

(* Ripasso 3
   =========
   
   L'operazione di sostituzione di una formula `G` al posto dell'atomo
   `x` in una formula `F`: `F[G/x]` 
*)

let rec subst (x:nat) (G: Formula) (F: Formula) on F ≝
 match F with
  [ FBot ⇒ FBot
  | FTop ⇒ FTop
  | FAtom n ⇒ if eqb n x then G else (FAtom n)
  | FAnd F1 F2 ⇒ FAnd (subst x G F1) (subst x G F2)
  | FOr F1 F2 ⇒ FOr (subst x G F1) (subst x G F2)
  | FImpl F1 F2 ⇒ FImpl (subst x G F1) (subst x G F2)
  | FNot F ⇒ FNot (subst x G F)
  ].

(* ATTENZIONE
   ==========
   
   Non modificare quanto segue.
*)  
notation < "t [ \nbsp term 19 a / term 19 b \nbsp ]" non associative with precedence 19 for @{ 'substitution $b $a $t }.
notation > "t [ term 90 a / term 90 b]" non associative with precedence 19 for @{ 'substitution $b $a $t }.
interpretation "Substitution for Formula" 'substitution b a t = (subst b a t).
definition equiv ≝ λF1,F2. ∀v.[[ F1 ]]v = [[ F2 ]]v.
notation "hvbox(a \nbsp break mstyle color #0000ff (≡) \nbsp b)"  non associative with precedence 45 for @{ 'equivF $a $b }.
notation > "a ≡ b" non associative with precedence 55 for @{ equiv $a $b }.
interpretation "equivalence for Formulas" 'equivF a b = (equiv a b).
lemma min_1_sem: ∀F,v.min 1 [[ F ]]v = [[ F ]]v. intros; cases (sem_bool F v); rewrite > H; reflexivity; qed.
lemma max_0_sem: ∀F,v.max [[ F ]]v 0 = [[ F ]]v. intros; cases (sem_bool F v); rewrite > H; reflexivity; qed.
definition IFTE := λA,B,C:Formula. FOr (FAnd A B) (FAnd (FNot A) C).

(*DOCBEGIN

La libreria di Matita
=====================

Per portare a termine l'esercitazione sono necessari i seguenti lemmi:

* lemma `decidable_eq_nat` : `∀x,y.x = y ∨ x ≠ y`
* lemma `sem_bool` : `∀F,v. [[ F ]]v = 0 ∨ [[ F ]]v = 1`
* lemma `not_eq_to_eqb_false` : `∀x,y.x ≠ y → eqb x y = false`
* lemma `eq_to_eqb_true` : `∀x,y.x = y → eqb x y = true`
* lemma `min_1_sem` : `∀F,v.min 1 [[ F ]]v = [[ F ]]v`
* lemma `max_0_sem` : `∀F,v.max [[ F ]]v 0 = [[ F ]]v`

Nota su `x = y` e `eqb x y`
---------------------------

Se vi siete mai chiesti la differenza tra `x = y` ed `eqb x y`
quanto segue prova a chiarirla.

Presi due numeri `x` e `y` in ℕ, dire che `x = y` significa i due numeri 
sono lo stesso numero, ovvero che se `x` è il numero `3`,
anche `y` è il numero `3`.

`eqb` è un funzione, un programma, che confronta due numeri naturali
e restituisce `true` se sono uguali, `false` se sono diversi. L'utilizzo
di tale programma è necessario per usare il costrutto (che è a sua volta 
un programma) `if E then A else B`, che lancia il programma `E`, 
e se il suo
risultato è `true` si comporta come `A` altrimenti come `B`. Come
ben sapete i programmi possono contenere errori. In particolare anche
`eqb` potrebbe essere sbagliato, e per esempio restituire sempre `true`. 
I teoremi `eq_to_eqb_true` e 
`not_eq_to_eqb_false` sono la dimostrazione che il programma `eqb` è 
corretto, ovvero che che se `x = y` allora `eqb x y` restituisce `true`,
se `x ≠ y` allora `eqb x y` restituisce `false`.  

Il teorema di espansione di Shannon
===================================

Si definisce un connettivo logico `IFTE A B C` come
 
        FOr (FAnd A B) (FAnd (FNot A) C)

Il teorema dice che data una formula `F`, e preso un atomo `x`, la seguente 
formula è equivalente a `F`:

        IFTE (FAtom x) (F[FTop/x]) (F[FBot/x])
        
Ovvero, fissato un mondo `v`, sostituisco l'atomo `x` con `FBot` se tale 
atomo è falso, lo sostituisco con `FTop` se è vero.

La dimostrazione è composta da due lemmi, `shannon_false` e `shannon_true`.

Vediamo solo la dimostrazione del primo, essendo il secondo del tutto analogo.
Il lemma asserisce quanto segue:

        ∀F,x,v. [[ FAtom x ]]v = 0 → [[ F[FBot/x] ]]v = [[ F ]]v
        
Una volta assunte la formula `F`, l'atomo `x`, il mondo `v` e aver 
supposto che `[[ FAtom x ]]v = 0` si procede per induzione su `F`.
I casi `FTop` e `FBot` sono banali. Nei casi `FAnd/FOr/FImpl/FNot`,
una volta assunte le sottoformule e le relative ipotesi induttive, 
si conclude con una catena di uguaglianze.

Il caso `FAtom` richiede maggiore cura. Assunto l'indice dell'atomo `n`,
occorre utilizzare il lemma `decidable_eq_nat` per ottenere l'ipotesi
aggiuntiva `n = x ∨ n ≠ x` (dove `x` è l'atomo su cui predica il teorema).
Si procede per casi sull'ipotesi appena ottenuta.
In entrambi i casi, usando i lemmi `eq_to_eqb_true` oppure `not_eq_to_eqb_false`
si ottengolo le ipotesi aggiuntive `(eqb n x = true)` oppure `(eqb n x = false)`.
Entrambi i casi si concludono con una catena di uguaglianze.

Il teorema principale si dimostra utilizzando il lemma `sem_bool` per 
ottenre l'ipotesi `[[ FAtom x ]]v = 0 ∨ [[ FAtom x ]]v = 1` su cui
si procede poi per casi. Entrambi i casi si concludono con
una catena di uguaglianze che utilizza i lemmi dimostrati in precedenza 
e i lemmi `min_1_sem` oppure `max_0_sem`.

DOCEND*)

lemma shannon_false: 
  ∀F,x,v. [[ FAtom x ]]v = 0 → [[ F[FBot/x] ]]v = [[ F ]]v.
(*BEGIN*)
assume F : Formula.
assume x : ℕ.
assume v : (ℕ → ℕ).
suppose ([[ FAtom x ]]v = 0) (H).
we proceed by induction on F to prove ([[ F[FBot/x] ]]v = [[ F ]]v).
case FBot.
  the thesis becomes ([[ FBot[FBot/x] ]]v = [[ FBot ]]v).
  the thesis becomes ([[ FBot ]]v = [[ FBot ]]v).
  done. 
case FTop.
  the thesis becomes ([[ FTop[FBot/x] ]]v = [[ FTop ]]v).
  the thesis becomes ([[ FTop ]]v = [[ FTop ]]v).
  done.
case FAtom.
  assume n : ℕ.
  the thesis becomes ([[ (FAtom n)[FBot/x] ]]v = [[ FAtom n ]]v).
  the thesis becomes ([[ if eqb n x then FBot else (FAtom n) ]]v = [[ FAtom n ]]v).
  by decidable_eq_nat we proved (n = x ∨ n ≠ x) (H1).
  we proceed by cases on H1 to prove ([[ if eqb n x then FBot else (FAtom n) ]]v = [[ FAtom n ]]v).
    case Left.
      by H2, eq_to_eqb_true we proved (eqb n x = true) (H3).
      conclude
          ([[ if eqb n x then FBot else (FAtom n) ]]v)
        = ([[ if true then FBot else (FAtom n) ]]v) by H3.
        = ([[ FBot ]]v). 
        = 0.
        = ([[ FAtom x ]]v) by H.
        = ([[ FAtom n ]]v) by H2.
    done.
    case Right.
      by H2, not_eq_to_eqb_false we proved (eqb n x = false) (H3).
      conclude
          ([[ if eqb n x then FBot else (FAtom n) ]]v)
        = ([[ if false then FBot else (FAtom n) ]]v) by H3.
        = ([[ FAtom n ]]v). 
    done.
case FAnd.
  assume f1 : Formula.
  by induction hypothesis we know ([[ f1[FBot/x] ]]v = [[ f1 ]]v) (H1).
  assume f2 : Formula. 
  by induction hypothesis we know ([[ f2[FBot/x] ]]v = [[ f2 ]]v) (H2).
  the thesis becomes ([[ (FAnd f1 f2)[FBot/x] ]]v = [[ FAnd f1 f2 ]]v).
  conclude 
      ([[ (FAnd f1 f2)[FBot/x] ]]v)
    = ([[ FAnd (f1[FBot/x]) (f2[FBot/x]) ]]v).
    = (min [[ f1[FBot/x] ]]v [[ f2[FBot/x] ]]v).
    = (min [[ f1 ]]v [[ f2[FBot/x] ]]v) by H1.
    = (min [[ f1 ]]v [[ f2 ]]v) by H2.
    = ([[ FAnd f1 f2 ]]v).
  done. 
case FOr.
  assume f1 : Formula.
  by induction hypothesis we know ([[ f1[FBot/x] ]]v = [[ f1 ]]v) (H1).
  assume f2 : Formula. 
  by induction hypothesis we know ([[ f2[FBot/x] ]]v = [[ f2 ]]v) (H2).
  the thesis becomes ([[ (FOr f1 f2)[FBot/x] ]]v = [[ FOr f1 f2 ]]v).
  conclude 
      ([[ (FOr f1 f2)[FBot/x] ]]v)
    = ([[ FOr (f1[FBot/x]) (f2[FBot/x]) ]]v).
    = (max [[ f1[FBot/x] ]]v  [[ f2[FBot/x] ]]v).
    = (max [[ f1 ]]v  [[ f2[FBot/x] ]]v) by H1.
    = (max [[ f1 ]]v  [[ f2 ]]v) by H2.
    = ([[ FOr f1 f2 ]]v).
  done.
case FImpl.
  assume f1 : Formula.
  by induction hypothesis we know ([[ f1[FBot/x] ]]v = [[ f1 ]]v) (H1).
  assume f2 : Formula. 
  by induction hypothesis we know ([[ f2[FBot/x] ]]v = [[ f2 ]]v) (H2).
  the thesis becomes ([[ (FImpl f1 f2)[FBot/x] ]]v = [[ FImpl f1 f2 ]]v).
  conclude
      ([[ (FImpl f1 f2)[FBot/x] ]]v)
    = ([[ FImpl (f1[FBot/x]) (f2[FBot/x]) ]]v).
    = (max (1 - [[ f1[FBot/x] ]]v) [[ f2[FBot/x] ]]v).
    = (max (1 - [[ f1 ]]v) [[ f2[FBot/x] ]]v) by H1.
    = (max (1 - [[ f1 ]]v) [[ f2 ]]v) by H2.
    = ([[ FImpl f1 f2 ]]v).
  done.
case FNot.
  assume f : Formula.
  by induction hypothesis we know ([[ f[FBot/x] ]]v = [[ f ]]v) (H1).
  the thesis becomes ([[ (FNot f)[FBot/x] ]]v = [[ FNot f ]]v).
  conclude 
      ([[ (FNot f)[FBot/x] ]]v)
    = ([[ FNot (f[FBot/x]) ]]v).
    = (1 - [[ f[FBot/x] ]]v).
    = (1 - [[ f ]]v) by H1.
    = ([[ FNot f ]]v).
  done.
(*END*)
qed. 

lemma shannon_true: 
  ∀F,x,v. [[ FAtom x ]]v = 1 → [[ F[FTop/x] ]]v = [[ F ]]v.
(*BEGIN*)
assume F : Formula.
assume x : ℕ.
assume v : (ℕ → ℕ).
suppose ([[ FAtom x ]]v = 1) (H).
we proceed by induction on F to prove ([[ F[FTop/x] ]]v = [[ F ]]v).
case FBot.
  the thesis becomes ([[ FBot[FTop/x] ]]v = [[ FBot ]]v).
  the thesis becomes ([[ FBot ]]v = [[ FBot ]]v).
  done. 
case FTop.
  the thesis becomes ([[ FTop[FTop/x] ]]v = [[ FTop ]]v).
  the thesis becomes ([[ FTop ]]v = [[ FTop ]]v).
  done.
case FAtom.
  assume n : ℕ.
  the thesis becomes ([[ (FAtom n)[FTop/x] ]]v = [[ FAtom n ]]v).
  the thesis becomes ([[ if eqb n x then FTop else (FAtom n) ]]v = [[ FAtom n ]]v).
  by decidable_eq_nat we proved (n = x ∨ n ≠ x) (H1).
  we proceed by cases on H1 to prove ([[ if eqb n x then FTop else (FAtom n) ]]v = [[ FAtom n ]]v).
    case Left.
      by H2, eq_to_eqb_true we proved (eqb n x = true) (H3).
      conclude
          ([[ if eqb n x then FTop else (FAtom n) ]]v)
        = ([[ if true then FTop else (FAtom n) ]]v) by H3.
        = ([[ FTop ]]v). 
        = 1.
        = ([[ FAtom x ]]v) by H.
        = ([[ FAtom n ]]v) by H2.
    done.
    case Right.
      by H2, not_eq_to_eqb_false we proved (eqb n x = false) (H3).
      conclude
          ([[ if eqb n x then FTop else (FAtom n) ]]v)
        = ([[ if false then FTop else (FAtom n) ]]v) by H3.
        = ([[ FAtom n ]]v). 
    done.
case FAnd.
  assume f1 : Formula.
  by induction hypothesis we know ([[ f1[FTop/x] ]]v = [[ f1 ]]v) (H1).
  assume f2 : Formula. 
  by induction hypothesis we know ([[ f2[FTop/x] ]]v = [[ f2 ]]v) (H2).
  the thesis becomes ([[ (FAnd f1 f2)[FTop/x] ]]v = [[ FAnd f1 f2 ]]v).
  conclude 
      ([[ (FAnd f1 f2)[FTop/x] ]]v)
    = ([[ FAnd (f1[FTop/x]) (f2[FTop/x]) ]]v).
    = (min [[ f1[FTop/x] ]]v [[ f2[FTop/x] ]]v).
    = (min [[ f1 ]]v [[ f2[FTop/x] ]]v) by H1.
    = (min [[ f1 ]]v [[ f2 ]]v) by H2.
    = ([[ FAnd f1 f2 ]]v).
  done. 
case FOr.
  assume f1 : Formula.
  by induction hypothesis we know ([[ f1[FTop/x] ]]v = [[ f1 ]]v) (H1).
  assume f2 : Formula. 
  by induction hypothesis we know ([[ f2[FTop/x] ]]v = [[ f2 ]]v) (H2).
  the thesis becomes ([[ (FOr f1 f2)[FTop/x] ]]v = [[ FOr f1 f2 ]]v).
  conclude 
      ([[ (FOr f1 f2)[FTop/x] ]]v)
    = ([[ FOr (f1[FTop/x]) (f2[FTop/x]) ]]v).
    = (max [[ f1[FTop/x] ]]v  [[ f2[FTop/x] ]]v).
    = (max [[ f1 ]]v  [[ f2[FTop/x] ]]v) by H1.
    = (max [[ f1 ]]v  [[ f2 ]]v) by H2.
    = ([[ FOr f1 f2 ]]v).
  done.
case FImpl.
  assume f1 : Formula.
  by induction hypothesis we know ([[ f1[FTop/x] ]]v = [[ f1 ]]v) (H1).
  assume f2 : Formula. 
  by induction hypothesis we know ([[ f2[FTop/x] ]]v = [[ f2 ]]v) (H2).
  the thesis becomes ([[ (FImpl f1 f2)[FTop/x] ]]v = [[ FImpl f1 f2 ]]v).
  conclude
      ([[ (FImpl f1 f2)[FTop/x] ]]v)
    = ([[ FImpl (f1[FTop/x]) (f2[FTop/x]) ]]v).
    = (max (1 - [[ f1[FTop/x] ]]v) [[ f2[FTop/x] ]]v).
    = (max (1 - [[ f1 ]]v) [[ f2[FTop/x] ]]v) by H1.
    = (max (1 - [[ f1 ]]v) [[ f2 ]]v) by H2.
    = ([[ FImpl f1 f2 ]]v).
  done.
case FNot.
  assume f : Formula.
  by induction hypothesis we know ([[ f[FTop/x] ]]v = [[ f ]]v) (H1).
  the thesis becomes ([[ (FNot f)[FTop/x] ]]v = [[ FNot f ]]v).
  conclude 
      ([[ (FNot f)[FTop/x] ]]v)
    = ([[ FNot (f[FTop/x]) ]]v).
    = (1 - [[ f[FTop/x] ]]v).
    = (1 - [[ f ]]v) by H1.
    = ([[ FNot f ]]v).
  done.
(*END*)
qed. 

theorem shannon : 
  ∀F,x. IFTE (FAtom x) (F[FTop/x]) (F[FBot/x]) ≡ F.
(*BEGIN*)
assume F : Formula.
assume x : ℕ.
assume v : (ℕ → ℕ).
the thesis becomes ([[ IFTE (FAtom x) (F[FTop/x]) (F[FBot/x])]]v = [[ F ]]v).
by sem_bool we proved ([[ FAtom x]]v = 0 ∨ [[ FAtom x]]v = 1) (H).
we proceed by cases on H to prove ([[ IFTE (FAtom x) (F[FTop/x]) (F[FBot/x])]]v = [[ F ]]v).
case Left.
  conclude 
      ([[ IFTE (FAtom x) (F[FTop/x]) (F[FBot/x])]]v)
    = ([[ FOr (FAnd (FAtom x) (F[FTop/x])) (FAnd (FNot (FAtom x)) (F[FBot/x]))]]v).
    = (max [[ (FAnd (FAtom x) (F[FTop/x])) ]]v [[ (FAnd (FNot (FAtom x)) (F[FBot/x]))]]v).
    = (max (min  [[ FAtom x ]]v [[ F[FTop/x] ]]v) (min (1 - [[ FAtom x ]]v) [[ F[FBot/x] ]]v)).
    = (max (min  0 [[ F[FTop/x] ]]v) (min (1 - 0) [[ F[FBot/x] ]]v)) by H1.    
    = (max 0 (min 1 [[ F[FBot/x] ]]v)).
    = (max 0 [[ F[FBot/x] ]]v) by min_1_sem.
    = ([[ F[FBot/x] ]]v).
    = ([[ F ]]v) by H1, shannon_false.
  done.
case Right.
  conclude 
      ([[ IFTE (FAtom x) (F[FTop/x]) (F[FBot/x])]]v)
    = ([[ FOr (FAnd (FAtom x) (F[FTop/x])) (FAnd (FNot (FAtom x)) (F[FBot/x]))]]v).
    = (max [[ (FAnd (FAtom x) (F[FTop/x])) ]]v [[ (FAnd (FNot (FAtom x)) (F[FBot/x]))]]v).
    = (max (min  [[ FAtom x ]]v [[ F[FTop/x] ]]v) (min (1 - [[ FAtom x ]]v) [[ F[FBot/x] ]]v)).
    = (max (min  1 [[ F[FTop/x] ]]v) (min (1 - 1) [[ F[FBot/x] ]]v)) by H1.    
    = (max (min  1 [[ F[FTop/x] ]]v) (min 0 [[ F[FBot/x] ]]v)).
    = (max [[ F[FTop/x] ]]v (min 0 [[ F[FBot/x] ]]v)) by min_1_sem.
    = (max [[ F[FTop/x] ]]v 0).
    = ([[ F[FTop/x] ]]v) by max_0_sem.
    = ([[ F ]]v) by H1, shannon_true.
  done.
(*END*)
qed.

(*DOCBEGIN

Note generali
=============

Si ricorda che:

1. Ogni volta che nella finestra di destra compare un simbolo `∀` oppure un 
   simbolo `→` è opportuno usare il comando `assume` oppure `suppose` 
   oppure (se si è in un caso di una dimostrazione per induzione) il comando
   `by induction hypothesis we know` (che vengono nuovamente spiegati in seguito).
   
2. Ogni caso (o sotto caso) della dimostrazione:

   1. Inizia con una sequenza di comandi `assume` o `suppose` oppure 
      `by induction hypothesis we know`. Tale sequenza di comandi può anche 
      essere vuota.
       
   2. Continua poi con almeno un comando `the thesis becomes`.
   
   3. Eventualmente seguono vari comandi `by ... we proved` per 
      utilizzare i teoremi già disponibili per generare nuove
      ipotesi.
      
   4. Eventualmente uno o più comandi `we proceed by cases on (...) to prove (...)`.
      
   5. Se necessario un comando `conclude` seguito da un numero anche
      molto lungo di passi `= (...) by ... .` per rendere la parte 
      sinistra della vostra tesi uguale alla parte destra.
      
   6. Ogni caso termina con `done`.

3. Ogni caso corrispondente a un nodo con sottoformule (FAnd/For/FNot)
   avrà tante ipotesi induttive quante sono le sue sottoformule e tali
   ipotesi sono necessarie per portare a termine la dimostrazione.

I comandi da utilizzare
=======================

* `the thesis becomes (...).`

  Afferma quale sia la tesi da dimostrare. Se ripetuto
  permette di espandere le definizioni.
        
* `we proceed by cases on (...) to prove (...).`

  Permette di andare per casi su una ipotesi (quando essa è della forma
  `A ∨ B`).
   
  Esempio: `we proceed by cases on H to prove Q.`
        
* `case ... .`

  Nelle dimostrazioni per casi o per induzioni si utulizza tale comando
  per inizia la sotto prova relativa a un caso. Esempio: `case Fbot.`
  
* `done.`

  Ogni caso di una dimostrazione deve essere terminato con il comando
  `done.`  

* `assume ... : (...) .`
        
  Assume una formula o un numero, ad esempio `assume n : (ℕ).` assume
  un numero naturale `n`.
        
* `by ..., ..., ..., we proved (...) (...).`

  Permette di comporre lemmi e ipotesi per ottenere nuove ipotesi.
  Ad esempio `by H, H1 we prove (F ≡ G) (H2).` ottiene una nuova ipotesi
  `H2` che dice che `F ≡ G` componendo insieme `H` e `H1`.
        
* `conclude (...) = (...) by ... .`

  Il comando conclude lavora SOLO sulla parte sinistra della tesi. È il comando
  con cui si inizia una catena di uguaglianze. La prima formula che si
  scrive deve essere esattamente uguale alla parte sinistra della conclusione
  originale. Esempio `conclude ([[ FAtom x ]]v) = ([[ FAtom n ]]v) by H.`
  Se la giustificazione non è un lemma o una ipotesi ma la semplice espansione
  di una definizione, la parte `by ...` deve essere omessa.
          
* `= (...) by ... .`

  Continua un comando `conclude`, lavorando sempre sulla parte sinistra della
  tesi.

DOCEND*)
