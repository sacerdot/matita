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

   Prima di abbandonare la postazione:

   * salvare il file (menu `File ▹ Save as ...`) nella directory (cartella)
     /public/ con nome linguaggi_Account1.ma, ad esempio Mario Rossi, il cui
     account è mrossi, deve salvare il file in /public/linguaggi_mrossi.ma

   * mandatevi via email o stampate il file. Per stampare potete usare
     usare l'editor gedit che offre la funzionalità di stampa
*)

(*DOCBEGIN

Il teorema di dualità
=====================

Il teorema di dualizzazione dice che date due formule `F1` ed `F2`,
se le due formule sono equivalenti (`F1 ≡ F2`) allora anche le 
loro dualizzate lo sono (`dualize F1 ≡ dualize F2`).

L'ingrediente principale è la funzione di dualizzazione di una formula `F`:
   
   * Scambia FTop con FBot e viceversa
   
   * Scambia il connettivo FAnd con FOr e viceversa
   
   * Sostituisce il connettivo FImpl con FAnd e nega la
     prima sottoformula.
   
   Ad esempio la formula `A → (B ∧ ⊥)` viene dualizzata in
   `¬A ∧ (B ∨ ⊤)`.

Per dimostrare il teorema di dualizzazione in modo agevole è necessario
definire altre nozioni:

* La funzione `negate` che presa una formula `F` ne nega gli atomi.
  Ad esempio la formula `(A ∨ (⊤ → B))` deve diventare `¬A ∨ (⊤ → ¬B)`.
   
* La funzione `invert` permette di invertire un mondo `v`.
  Ovvero, per ogni indice di atomo `i`, se `v i` restituisce
  `1` allora `(invert v) i` restituisce `0` e viceversa.
   
DOCEND*)

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

(* Ripasso
   =======
   
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

(* Esercizio 1
   ===========
   
   Modificare la funzione `sem` scritta nella precedente
   esercitazione in modo che valga solo 0 oppure 1 nel caso degli
   atomi, anche nel caso in cui il mondo `v` restituisca un numero
   maggiore di 1.
   
   Suggerimento: non è necessario usare il costrutto if_then_else
   e tantomento il predicato di maggiore o uguale. È invece possibile
   usare la funzione `min`.
*) 
let rec sem (v: nat → nat) (F: Formula) on F : nat ≝
 match F with
  [ FBot ⇒ 0
  | FTop ⇒ 1
  | FAtom n ⇒ (*BEGIN*)min (v n) 1(*END*)
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

definition v20 ≝ λx.
       if eqb x 0 then 2
  else if eqb x 1 then 1
  else                 0.
  
(* Test 1
   ======
   
   La semantica della formula `(A ∨ C)` nel mondo `v20` in cui 
   `A` vale `2` e `C` vale `0` deve valere `1`.
   
   Decommenta ed esegui.
*)    

(* eval normalize on [[FOr (FAtom 0) (FAtom 2)]]v20. *) 

(*DOCBEGIN

La libreria di Matita
=====================

Gli strumenti per la dimostrazione assistita sono corredati da
librerie di teoremi già dimostrati. Per portare a termine l'esercitazione
sono necessari i seguenti lemmi:

* lemma `sem_le_1` : `∀F,v. [[ F ]]v ≤ 1`
* lemma `min_1_1` : `∀x. x ≤ 1 → 1 - (1 - x) = x`
* lemma `min_bool` : `∀n. min n 1 = 0 ∨ min n 1 = 1`
* lemma `min_max` : `∀F,G,v.min (1 - [[F]]v) (1 - [[G]]v) = 1 - max [[F]]v [[G]]v`
* lemma `max_min` : `∀F,G,v.max (1 - [[F]]v) (1 - [[G]]v) = 1 - min [[F]]v [[G]]v`
* lemma `equiv_rewrite` : `∀F1,F2,F3. F1 ≡ F2 → F1 ≡ F3 → F2 ≡ F3`
* lemma `equiv_sym` : `∀F1,F2. F1 ≡ F2 → F2 ≡ F1`

DOCEND*)

(* ATTENZIONE
   ==========
   
   Non modificare quanto segue.
*)
lemma sem_bool : ∀F,v. [[ F ]]v = 0 ∨ [[ F ]]v = 1.  intros; elim F; simplify; [left;reflexivity; |right;reflexivity; |cases (v n);[left;|cases n1;right;]reflexivity; |4,5,6: cases H; cases H1; rewrite > H2; rewrite > H3; simplify; first [ left;reflexivity | right; reflexivity ].  |cases H; rewrite > H1; simplify;[right|left]reflexivity;] qed.
lemma min_bool : ∀n. min n 1 = 0 ∨ min n 1 = 1.  intros; cases n; [left;reflexivity] cases n1; right; reflexivity; qed.  
lemma min_max : ∀F,G,v.  min (1 - [[F]]v) (1 - [[G]]v) = 1 - max [[F]]v [[G]]v.  intros; cases (sem_bool F v);cases (sem_bool G v); rewrite > H; rewrite >H1; simplify; reflexivity; qed.
lemma max_min : ∀F,G,v.  max (1 - [[F]]v) (1 - [[G]]v) = 1 - min [[F]]v [[G]]v.  intros; cases (sem_bool F v);cases (sem_bool G v); rewrite > H; rewrite >H1; simplify; reflexivity; qed.
lemma min_1_1 : ∀x.x ≤ 1 → 1 - (1 - x) = x. intros; inversion H; intros; destruct; [reflexivity;] rewrite < (le_n_O_to_eq ? H1); reflexivity;qed.
lemma sem_le_1 : ∀F,v.[[F]]v ≤ 1. intros; cases (sem_bool F v); rewrite > H; [apply le_O_n|apply le_n]qed.

(* Esercizio 2
   ===========
   
   Definire per ricorsione strutturale la funzione `negate`
   che presa una formula `F` ne nega gli atomi.
   
   Ad esempio la formula `(A ∨ (⊤ → B))` deve diventare
   `¬A ∨ (⊤ → ¬B)`.
*)
let rec negate (F: Formula) on F : Formula ≝
 match F with
  [ (*BEGIN*)FBot ⇒ FBot
  | FTop ⇒ FTop
  | FAtom n ⇒ FNot (FAtom n)
  | FAnd F1 F2 ⇒ FAnd (negate F1) (negate F2)
  | FOr F1 F2 ⇒ FOr (negate F1) (negate F2)
  | FImpl F1 F2 ⇒ FImpl (negate F1) (negate F2)
  | FNot F ⇒ FNot (negate F)(*END*)
  ].

(* Test 2
   ======
  
   Testare la funzione `negate`. Il risultato atteso è:
   
       FOr (FNot (FAtom O)) (FImpl FTop (FNot (FAtom 1)))
       
   Decommenta ed esegui 
*)

(* eval normalize on (negate (FOr (FAtom 0) (FImpl FTop (FAtom 1)))). *)

(* ATTENZIONE
   ==========
   
   Non modificare quanto segue
*)
definition equiv ≝ λF1,F2. ∀v.[[ F1 ]]v = [[ F2 ]]v.
notation "hvbox(a \nbsp break mstyle color #0000ff (≡) \nbsp b)"  non associative with precedence 45 for @{ 'equivF $a $b }.
notation > "a ≡ b" non associative with precedence 55 for @{ equiv $a $b }.
interpretation "equivalence for Formulas" 'equivF a b = (equiv a b).
lemma equiv_rewrite : ∀F1,F2,F3. F1 ≡ F2 → F1 ≡ F3 → F2 ≡ F3. intros; intro; rewrite < H; rewrite < H1; reflexivity. qed.
lemma equiv_sym : ∀a,b.a ≡ b → b ≡ a. intros 4;symmetry;apply H;qed.

(* Esercizio 3
   ===========
   
   Definire per ricorsione strutturale la funzione di
   dualizzazione di una formula `F`. Tale funzione:
   
   * Scambia FTop con FBot e viceversa
   
   * Scambia il connettivo FAnd con FOr e viceversa
   
   * Sostituisce il connettivo FImpl con FAnd e nega la
     prima sottoformula. Il razionale è che `FImpl A B`
     è semanticamente equivalente a `FOr (FNot A) B` il
     cui duale è `FAnd (FNot A) B`.
   
   Ad esempio la formula `A → (B ∧ ⊥)` viene dualizzata in
   `¬A ∧ (B ∨ ⊤)`. 
*)  
let rec dualize (F : Formula) on F : Formula ≝
  match F with
  [ (*BEGIN*)FBot ⇒ FTop
  | FTop ⇒ FBot
  | FAtom n ⇒ FAtom n
  | FAnd F1 F2 ⇒ FOr (dualize F1) (dualize F2)
  | FOr F1 F2 ⇒ FAnd (dualize F1) (dualize F2)
  | FImpl F1 F2 ⇒ FAnd (FNot (dualize F1)) (dualize F2)
  | FNot F ⇒ FNot (dualize F)(*END*)
  ].

(* Test 3
   ======
   
   Testare la funzione `dualize`. Il risultato atteso è:
   
       FAnd (FNot (FAtom O)) (FOr (FAtom 1) FTop) 
       
   Decommenta ed esegui.
*)

(* eval normalize on (dualize (FImpl (FAtom 0) (FAnd (FAtom 1) FBot))). *)

(* Spiegazione
   ===========
   
   La funzione `invert` permette di invertire un mondo `v`.
   Ovvero, per ogni indice di atomo `i`, se `v i` restituisce
   `1` allora `(invert v) i` restituisce `0` e viceversa.
   
*)
definition invert ≝
 λv:ℕ → ℕ. λx. if eqb (min (v x) 1) 0 then 1 else 0.
 
interpretation "Inversione del mondo" 'invert v = (invert v).
 
(*DOCBEGIN

Il linguaggio di dimostrazione di Matita
========================================

Per dimostrare il lemma `negate_invert` in modo agevole è necessario 
utilizzare il seguente comando:

* by H1, H2 we proved P (H)

  Il comando `by ... we proved` visto nella scorsa esercitazione
  permette di utilizzare più ipotesi o lemmi alla volta
  separandoli con una virgola.

DOCEND*)

(* Esercizio 4
   ===========
   
   Dimostrare il lemma `negate_invert` che asserisce che
   la semantica in un mondo `v` associato alla formula
   negata di `F` e uguale alla semantica associata
   a `F` in un mondo invertito.
*) 
lemma negate_invert:
  ∀F:Formula.∀v:ℕ→ℕ.[[ negate F ]]v=[[ F ]](invert v).
assume F:Formula.
assume v:(ℕ→ℕ).
we proceed by induction on F to prove ([[ negate F ]]v=[[ F ]](invert v)).
  case FBot.
    (*BEGIN*)
    the thesis becomes ([[ negate FBot ]]v=[[ FBot ]](invert v)).
    (*END*)
  done.
  case FTop.
    (*BEGIN*)
    the thesis becomes ([[ negate FTop ]]v=[[ FTop ]](invert v)).
    (*END*)
  done.
  case FAtom.
    assume n : ℕ.
    the thesis becomes ((*BEGIN*)[[ negate (FAtom n) ]]v=[[ FAtom n ]](invert v)(*END*)).
    the thesis becomes ((*BEGIN*)1 - (min (v n) 1)= min (invert v n) 1(*END*)).
    the thesis becomes (1 - (min (v n) 1)= min (if eqb (min (v n) 1) 0 then 1 else 0) 1).
    by min_bool we proved (min (v n) 1 = 0 ∨ min (v n) 1 = 1) (H1);
    we proceed by cases on (H1) to prove (1 - (min (v n) 1)= min (if eqb (min (v n) 1) 0 then 1 else 0) 1).
      case Left.
        conclude 
            (1 - (min (v n) 1)) 
          = (1 - 0) by H.
          = 1.
          = (min 1 1).
          = (min (if true then 1 else O) 1).
          = (min (if eqb 0 0 then 1 else O) 1).
          = (min (if eqb (min (v n) 1) O then 1 else O) 1) by H.
      done.
      case Right.
        (*BEGIN*)
        conclude 
            (1 - (min (v n) 1)) 
          = (1 - 1) by H.
          = 0.
          = (min 0 1).
          = (min (if eqb 1 0 then 1 else O) 1).
          = (min (if eqb (min (v n) 1) O then 1 else O) 1) by H.
        (*END*)
      done.
  case FAnd.
    assume f : Formula.
    by induction hypothesis we know
      ((*BEGIN*)[[ negate f ]]v=[[ f ]](invert v)(*END*)) (H).
    assume f1 : Formula.
    by induction hypothesis we know
     ((*BEGIN*)[[ negate f1 ]]v=[[ f1 ]](invert v)(*END*)) (H1).
    the thesis becomes
     ([[ negate (FAnd f f1) ]]v=[[ FAnd f f1 ]](invert v)).
    the thesis becomes
     (min [[ negate f ]]v [[ negate f1]]v = [[ FAnd f f1 ]](invert v)).
    conclude 
        (min [[ negate f ]]v [[ negate f1]]v)
      = (min [[ f ]](invert v) [[ negate f1]]v) by (*BEGIN*)H(*END*).
      = (min [[ f ]](invert v) [[ f1]](invert v)) by (*BEGIN*)H1(*END*).
  done.
  case FOr.
    (*BEGIN*)
    assume f : Formula.
    by induction hypothesis we know
      ([[ negate f ]]v=[[ f ]](invert v)) (H).
    assume f1 : Formula.
    by induction hypothesis we know
     ([[ negate f1 ]]v=[[ f1 ]](invert v)) (H1).
    the thesis becomes
     ([[ negate (FOr f f1) ]]v=[[ FOr f f1 ]](invert v)).
    the thesis becomes
     (max [[ negate f ]]v [[ negate f1]]v = [[ FOr f f1 ]](invert v)).
    conclude 
        (max [[ negate f ]]v [[ negate f1]]v)
      = (max [[ f ]](invert v) [[ negate f1]]v) by H.
      = (max [[ f ]](invert v) [[ f1]](invert v)) by H1.
    (*END*)
  done.
  case FImpl.
    (*BEGIN*)
    assume f : Formula.
    by induction hypothesis we know
      ([[ negate f ]]v=[[ f ]](invert v)) (H).
    assume f1 : Formula.
    by induction hypothesis we know
     ([[ negate f1 ]]v=[[ f1 ]](invert v)) (H1).
    the thesis becomes
     ([[ negate (FImpl f f1) ]]v=[[ FImpl f f1 ]](invert v)).
    the thesis becomes
     (max (1 - [[ negate f ]]v) [[ negate f1]]v = [[ FImpl f f1 ]](invert v)).
    conclude 
        (max (1 - [[ negate f ]]v) [[ negate f1]]v)
      = (max (1 - [[ f ]](invert v)) [[ negate f1]]v) by H.
      = (max (1 - [[ f ]](invert v)) [[ f1]](invert v)) by H1.
    (*END*)
  done.
  case FNot.
    (*BEGIN*)
    assume f : Formula.
    by induction hypothesis we know
      ([[ negate f ]]v=[[ f ]](invert v)) (H).
    the thesis becomes
      ([[ negate (FNot f) ]]v=[[ FNot f ]](invert v)).
    the thesis becomes
      (1 - [[ negate f ]]v=[[ FNot f ]](invert v)).
    conclude (1 - [[ negate f ]]v) = (1 - [[f]](invert v)) by H.
    (*END*)
  done.  
qed.   

(* Esercizio 5
   ===========
   
   Dimostrare che la funzione negate rispetta l'equivalenza.
*)
lemma negate_fun:
 ∀F:Formula.∀G:Formula.F ≡ G → negate F ≡ negate G.
 assume (*BEGIN*)F:Formula(*END*).
 assume (*BEGIN*)G:Formula(*END*).
 suppose (*BEGIN*)(F ≡ G) (H)(*END*).
 the thesis becomes (*BEGIN*)(negate F ≡ negate G)(*END*).
 the thesis becomes (*BEGIN*)(∀v:ℕ→ℕ.[[ negate F ]]v=[[ negate G ]]v)(*END*).
 assume v:(ℕ→ℕ).
 conclude 
     [[ negate F ]]v
   = [[ F ]](invert v) by (*BEGIN*)negate_invert(*END*).
   = [[ G ]]((*BEGIN*)invert v(*BEGIN*)) by (*BEGIN*)H(*BEGIN*).
   = [[ negate G ]](*BEGIN*)v(*BEGIN*) by (*BEGIN*)negate_invert(*END*).
 done.  
qed.

(* Esercizio 6
   ===========
   
   Dimostrare che per ogni formula `F`, `(negate F)` equivale a 
   dualizzarla e negarla.
*)
lemma not_dualize_eq_negate:
 ∀F:Formula.negate F ≡ FNot (dualize F).
 (*BEGIN*)
 assume F:Formula.
 the thesis becomes (∀v:ℕ→ℕ.[[negate F]]v=[[FNot (dualize F)]]v).
 (*END*)
 assume v:(ℕ→ℕ).
 we proceed by induction on F to prove ([[negate F]]v=[[FNot (dualize F)]]v).
 case FBot.
   (*BEGIN*)
   the thesis becomes ([[ negate FBot ]]v=[[ FNot (dualize FBot) ]]v).
   (*END*)
 done.
 case FTop.
   (*BEGIN*)
   the thesis becomes ([[ negate FTop ]]v=[[ FNot (dualize FTop) ]]v).
   (*END*)
 done.
 case FAtom.
   (*BEGIN*)
   assume n : ℕ.
   the thesis becomes ([[ negate (FAtom n) ]]v=[[ FNot (dualize (FAtom n)) ]]v).
   (*END*)
 done.
 case FAnd.
   assume f : Formula.
   by induction hypothesis we know
     ([[ negate f ]]v=[[ FNot (dualize f) ]]v) (H).
   assume f1 : Formula.
   by induction hypothesis we know
    ([[ negate f1 ]]v=[[ FNot (dualize f1) ]]v) (H1).
   the thesis becomes
    ([[ negate (FAnd f f1) ]]v=[[ FNot (dualize (FAnd f f1)) ]]v).
   the thesis becomes
    (min [[ negate f ]]v [[ negate f1 ]]v=[[ FNot (dualize (FAnd f f1)) ]]v).
   conclude 
       (min (*BEGIN*)[[ negate f ]]v(*END*) (*BEGIN*)[[ negate f1 ]]v(*END*))
     = (min (*BEGIN*)[[ FNot (dualize f) ]]v(*END*) (*BEGIN*)[[ negate f1 ]]v(*END*)) by H.    
     = (min (*BEGIN*)[[ FNot (dualize f) ]]v(*END*) (*BEGIN*)[[ FNot (dualize f1) ]]v(*END*)) by H1.
     = (min (1 - [[ dualize f ]]v) (1 - [[ dualize f1 ]]v)).
     = (1 - (max [[ dualize f ]]v [[ dualize f1 ]]v)) by min_max.
 done.
 case FOr.
   (*BEGIN*)
   assume f : Formula.
   by induction hypothesis we know
     ([[ negate f ]]v=[[ FNot (dualize f) ]]v) (H).
   assume f1 : Formula.
   by induction hypothesis we know
    ([[ negate f1 ]]v=[[ FNot (dualize f1) ]]v) (H1).
   the thesis becomes
    ([[ negate (FOr f f1) ]]v=[[ FNot (dualize (FOr f f1)) ]]v).
   the thesis becomes
    (max [[ negate f ]]v [[ negate f1 ]]v=[[ FNot (dualize (FOr f f1)) ]]v).
   conclude 
       (max [[ negate f ]]v [[ negate f1 ]]v)
     = (max [[ FNot (dualize f) ]]v [[ negate f1 ]]v) by H.    
     = (max [[ FNot (dualize f) ]]v [[ FNot (dualize f1) ]]v) by H1.
     = (max (1 - [[ dualize f ]]v) (1 - [[ dualize f1 ]]v)).
     = (1 - (min [[ dualize f ]]v [[ dualize f1 ]]v)) by max_min.
   (*END*)
 done.
 case FImpl.
   (*BEGIN*)
   assume f : Formula.
   by induction hypothesis we know
     ([[ negate f ]]v=[[ FNot (dualize f) ]]v) (H).
   assume f1 : Formula.
   by induction hypothesis we know
    ([[ negate f1 ]]v=[[ FNot (dualize f1) ]]v) (H1).
   the thesis becomes
    ([[ negate (FImpl f f1) ]]v=[[ FNot (dualize (FImpl f f1)) ]]v).
   the thesis becomes
    (max (1 - [[ negate f ]]v) [[ negate f1 ]]v=[[ FNot (dualize (FImpl f f1)) ]]v).
   conclude 
       (max (1-[[ negate f ]]v) [[ negate f1 ]]v)
     = (max (1-[[ FNot (dualize f) ]]v) [[ negate f1 ]]v) by H.    
     = (max (1-[[ FNot (dualize f) ]]v) [[ FNot (dualize f1) ]]v) by H1.
     = (max (1 - [[ FNot (dualize f) ]]v) (1 - [[ dualize f1 ]]v)).
     = (1 - (min [[ FNot (dualize f) ]]v [[ dualize f1 ]]v)) by max_min.
   (*END*)
 done.
 case FNot.
   (*BEGIN*) 
   assume f : Formula.
   by induction hypothesis we know
     ([[ negate f ]]v=[[ FNot (dualize f) ]]v) (H).
   the thesis becomes
      ([[ negate (FNot f) ]]v=[[ FNot (dualize (FNot f)) ]]v).
   the thesis becomes
      (1 - [[ negate f ]]v=[[ FNot (dualize (FNot f)) ]]v).
   conclude (1 - [[ negate f ]]v) = (1 - [[ FNot (dualize f) ]]v) by H.
   (*END*)
 done.
qed.

(* Esercizio 7
   ===========
   
   Dimostrare che la negazione è iniettiva
*)
theorem not_inj:
 ∀F,G:Formula.FNot F ≡ FNot G→F ≡ G.
 (*BEGIN*)
 assume F:Formula.
 assume G:Formula.
 suppose (FNot F ≡ FNot G) (H).
 the thesis becomes (F ≡ G).
 the thesis becomes (∀v:ℕ→ℕ.[[ F ]]v=[[ G ]]v).
 (*END*)
 assume v:(ℕ→ℕ).
 by sem_le_1 we proved ([[F]]v ≤ 1) (H1).
 by (*BEGIN*)sem_le_1(*END*) we proved ([[G]]v ≤ 1) (H2).
 by min_1_1, H1 we proved (1 - (1 - [[F]]v) = [[F]]v) (H3).
 by (*BEGIN*)min_1_1, H2(*END*) we proved ((*BEGIN*)1 - (1 - [[G]]v)(*END*) = [[G]]v) (H4).
 conclude 
     ([[F]]v)
   = (1 - (1 - [[F]]v)) by (*BEGIN*)H3(*END*).
   = (1 - [[(*BEGIN*)FNot F(*END*)]]v).
   = (1 - [[ FNot G]]v) by H.
   = (1 - (*BEGIN*)(1 - [[G]]v)(*END*)).
   = [[G]]v by (*BEGIN*)H4(*END*).
 done.
qed.

(*DOCBEGIN

La prova del teorema di dualità
===============================

Il teorema di dualità accennato a lezione dice che se due formule 
`F1` ed `F2` sono equivalenti, allora anche le formule duali lo sono.
        
    ∀F1,F2:Formula. F1 ≡ F2 → dualize F1 ≡ dualize F2.
        
Per dimostrare tale teorema è bene suddividere la prova in lemmi intermedi

1. lemma `negate_invert`, dimostrato per induzione su F, utilizzando
   `min_bool`
   
        ∀F:Formula.∀v:ℕ→ℕ.[[ negate F ]]v=[[ F ]]_(invert v).

2. lemma `negate_fun`, conseguenza di `negate_invert`

        ∀F,G:Formula. F ≡ G → negate F ≡ negate G.
        
2. lemma `not_dualize_eq_negate`, dimostrato per induzione su F,
   utilizzando `max_min` e `min_max`

        ∀F:Formula. negate F ≡ FNot (dualize F)
        
4. lemma `not_inj`, conseguenza di `sem_bool`
 
        ∀F,G:Formula. FNot F ≡ FNot G → F ≡ G

Una volta dimostrati tali lemmi la prova del teorema di dualità 
procede come di seguito:

1. Assume l'ipotesi  

        F1 ≡ F2

2. Utilizza `negate_fun` per ottenere 

        negate F1 ≡ negate F2

3. Utilizzando due volte il lemma `not_dualize_eq_negate` e il lemma
   `equiv_rewrite` ottiene 

        FNot (dualize F1) ≡ FNot (dualize F2)

4. Conclude utilizzando il lemma `not_inj` per ottenere la tesi 

        dualize F1 ≡ dualize F2

DOCEND*)

(* Esercizio 8
   ===========
   
   Dimostrare il teorema di dualità
*)
theorem duality: ∀F1,F2:Formula.F1 ≡ F2 → dualize F1 ≡ dualize F2.
 assume F1:Formula.
 assume F2:Formula.
 suppose (F1 ≡ F2) (H).
 the thesis becomes (dualize F1 ≡ dualize F2).
 by (*BEGIN*)negate_fun(*END*), H we proved (negate F1 ≡ negate F2) (H1).
 by (*BEGIN*)not_dualize_eq_negate(*END*), (*BEGIN*)equiv_rewrite(*END*), H1 we proved (FNot (dualize F1) ≡ negate F2) (H2).
 by (*BEGIN*)not_dualize_eq_negate(*END*), (*BEGIN*)equiv_rewrite(*END*), H2, equiv_sym we proved (FNot (dualize F1) ≡ FNot (dualize F2)) (H3).
 by (*BEGIN*)not_inj(*END*), H3 we proved (dualize F1 ≡ dualize F2) (H4).
 by H4 done.
qed.
