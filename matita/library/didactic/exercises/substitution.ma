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

   * compilare il questionario in fondo al file
   
   * salvare il file (menu `File ▹ Save as ...`) nella directory (cartella)
     /public/ con nome linguaggi_Account1.ma, ad esempio Mario Rossi, il cui
     account è mrossi, deve salvare il file in /public/linguaggi_mrossi.ma

   * mandatevi via email o stampate il file. Per stampare potete usare
     usare l'editor gedit che offre la funzionalità di stampa
*)

(*DOCBEGIN

Come scrivere i simboli
=======================

Per inserire i simboli matematici è necessario digitare il loro nome
e poi premere ALT-L. In generale i nomi dei simboli sono della forma
`\nome`, ad esempio `\equiv`. Alcuni simboli molto frequenti hanno
dei sinonimi più comodi da digitare, per esemio `⇒` ha sia il nome
`\Rightarrow` sia `=>`.

Segue un elenco dei simboli più comuni e i loro nomi separati da virgola,
Se sono necessari dei simboli non riportati di seguito si può visualizzare
l'intera lista dal menù a tendina `View ▹ TeX/UTF8 table`.
 
* `→` : `\to`, `->`
* `⇒` : `\Rightarrow`, `=>`
* `ℕ` : `\naturals`
* `≝` : `\def`, `:=`
* `≡` : `\equiv`
* `∀` : `\forall`

La sintassi `∀x.P` significa "per tutti gli `x` vale `P`".

La sintassi `F → G` dove `F` e `G` sono proposizioni nel metalinguaggio
significa "`F` implica `G`". Attenzione, il simbolo `⇒` (usato a lezione)
non ha lo stesso significato in Matita.

La sintassi `ℕ → ℕ` è il tipo delle funzioni che preso un numero naturale
restituiscono un numero naturale. 

La sintassi di Matita
=====================

Il linguaggio di Matita si basa sul λ-calcolo CIC, la cui sintassi si 
differenzia in vari aspetti da quella che solitamente viene utilizzata
per fare matematica, e ricorda quella di Scheme che state vedendo nel corso
di programmazione. 

* applicazione

  Se `f` è una funzione che si aspetta due argomenti, l'applucazione di `f`
  agli argomenti `x` e `y` si scrive `(f x y)` e non `f(x,y)`. Le parentesi
  possono essere omesse se il senso è chiaro dal contesto. In particolare
  vengono omesse quando l'applicazione è argomento di un operatore binario.
  Esempio: `f x y + f y x` si legge `(f x y) + (f y x)`.  
 
* minimo e massimo

  Le funzioni `min` e `max` non fanno eccezione, per calcolare il 
  massimo tra `x` e `y` si scrive `(max x y)` e non `max{x,y}`

* Le funzioni definite per ricorsione strutturale utilizzano il costrutto 
  `let rec` (ricorsione) e il costrutto `match` (analisi per casi).

  Ad esempio la funzione count definita a lezione come
  
        count ⊤ ≝ 1
        count (F1 ∧ F2) ≝ 1 + count F1 + count F2 
        ...
     
  la si esprime come
  
        let rec count F on F ≝ 
          match F with 
          [ ⊤ ⇒ 1 
          | F1 ∧ F2 ⇒ 1 + count F1 + count F2 
          ...
          ].
       
* Per dare la definizione ricorsiva (di un linguaggio) si usa una sintassi 
  simile a BNF. Per esempio per definire 
  
        <A> ::= <A> "+" <A> | <A> "*" <A> | "0" | "1"
    
  si usa il seguente comando
  
        inductive A : Type ≝
        | Plus : A → A → A    
        | Times : A → A → A   
        | Zero : A
        | One : A
        .
     
La ratio è che `Plus` prende due argomenti di tipo `A` per darmi un `A`,
mentre `Zero` non prende nessun argomento per darmi un `A`. Al posto di usare
operatori infissi `(0 + 0)` la definizione crea operatori prefissi (funzioni).
Quindi `(0+0)` si scriverà come `(Plus Zero Zero)`.

DOCEND*)

(* ATTENZIONE
   ==========
   
   Non modificare le seguenti tre righe 
*)
include "nat/minus.ma".
definition max : nat → nat → nat ≝ λa,b:nat.let rec max n m on n ≝ match n with [ O ⇒ b | S n ⇒ match m with [ O ⇒ a | S m ⇒ max n m]] in max a b.
definition min : nat → nat → nat ≝ λa,b:nat.let rec min n m on n ≝ match n with [ O ⇒ a | S n ⇒ match m with [ O ⇒ b | S m ⇒ min n m]] in min a b.


(* Esercizio 1 
   ===========
   
   Definire il linguaggio delle formule riempiendo gli spazi 
*)
inductive Formula : Type ≝
| FBot: Formula
| FTop: (*BEGIN*)Formula(*END*)
| FAtom: nat → Formula (* usiamo i naturali al posto delle lettere *)
| FAnd: Formula → Formula → Formula
| FOr: (*BEGIN*)Formula → Formula → Formula(*END*)
| FImpl: (*BEGIN*)Formula → Formula → Formula(*END*)
| FNot: (*BEGIN*)Formula → Formula(*END*)
.


(* Esercizio 2 
   ===========

   Data la funzione di valutazione per gli atomi `v`, definire la 
   funzione `sem` per una generica formula `F` che vi associa la semantica
   (o denotazione) 
*)
let rec sem (v: nat → nat) (F: Formula) on F ≝
 match F with
  [ FBot ⇒ 0
  | FTop ⇒ (*BEGIN*)1(*END*)
  (*BEGIN*)
  | FAtom n ⇒ v n
  (*END*)
  | FAnd F1 F2 ⇒ (*BEGIN*)min (sem v F1) (sem v F2)(*END*)
  (*BEGIN*)
  | FOr F1 F2 ⇒ max (sem v F1) (sem v F2)
  | FImpl F1 F2 ⇒ max (1 - sem v F1) (sem v F2)
  (*END*)
  | FNot F1 ⇒ 1 - (sem v F1)
  ]
.

(* NOTA
   ====
   
   I comandi che seguono definiscono la seguente notazione:

   if e then risultato1 else risultato2
   
   Questa notazione permette di valutare l'espressione `e`. Se questa
   è vera restituisce `risultato1`, altrimenti restituisce `risultato2`.
   
   Un esempio di espressione è `eqb n m`, che confronta i due numeri naturali
   `n` ed `m`. 
   
   * [[ formula ]]v
   
   Questa notazione utilizza la funzione `sem` precedentemente definita, in 
   particolare `[[ f ]]v` è una abbreviazione per `sem v f`.


   ATTENZIONE
   ==========
   
   Non modificare le linee seguenti 
*)
definition if_then_else ≝ λT:Type.λe,t,f.match e return λ_.T with [ true ⇒ t | false ⇒ f].
notation > "'if' term 19 e 'then' term 19 t 'else' term 90 f" non associative with precedence 90 for @{ 'if_then_else $e $t $f }.
notation < "'if' \nbsp term 19 e \nbsp 'then' \nbsp term 19 t \nbsp 'else' \nbsp term 90 f \nbsp" non associative with precedence 90 for @{ 'if_then_else $e $t $f }.
interpretation "Formula if_then_else" 'if_then_else e t f = (if_then_else ? e t f).
notation < "[[ \nbsp term 19 a \nbsp ]] \nbsp \sub term 90 v" non associative with precedence 90 for @{ 'semantics $v $a }.
notation > "[[ term 19 a ]] \sub term 90 v" non associative with precedence 90 for @{ 'semantics $v $a }.
notation > "[[ term 19 a ]] term 90 v" non associative with precedence 90 for @{ sem $v $a }.
interpretation "Semantic of Formula" 'semantics v a = (sem v a).


(* Test 1
   ======
   
   Viene fornita una funzione di valutazione di esempio chiamata `v1101`. 
   Tale funzione associa agli atomi 0, 1 e 3 un valore pari a 1,
   invece a 2,4,5,6... un valore pari a 0. 
   
   Viene fornita una formula di esempio chiamata `esempio1` che rappresenta
   la formula 
    
       D => (C ∨ (B ∧ A))
       
   Dove A è rappresentato con l'atomo 0, B con l'atomo 1, ...
   
   Tale formula è valida per la funzione di valutazione `v1101`. 
   
   Il comando `eval normalize [[ esempio1 ]]v1101` permette di calcolare
   la funzione `sem` che avete appena definito. Tale funzione deve 
   computare a 1 (verrà mostrata una finestra col risultato).
   Se così non fosse significa che avete commesso un errore nella 
   definizione di `sem` e prima di continuare è necessario che la sistemiate.   
*)
definition v1101 ≝ λx.
      if eqb x 0 then 1  (* FAtom 0 ↦ 1 *)
 else if eqb x 1 then 1  (* FAtom 1 ↦ 1 *)
 else if eqb x 2 then 0  (* FAtom 2 ↦ 0 *)
 else if eqb x 3 then 1  (* FAtom 3 ↦ 1 *)
 else                 0. (* FAtom _ ↦ 0 *) 


definition esempio1 ≝ 
  (FImpl (FNot (FAtom 3)) (FOr (FAtom 2) (FAnd (FAtom 1) (FAtom 0)))).

(* Decommenta ed esegui. *)

(* eval normalize on [[ esempio1 ]]v1101. *)


(* Esercizio 3
   ===========
   
   Definire la funzione di sostituzione di una formula `G` al posto
   degli atomi uguali a `x` in una formula `F`. 
*)
let rec subst (x:nat) (G: Formula) (F: Formula) on F ≝
 match F with
  [ FBot ⇒ FBot
  | FTop ⇒ (*BEGIN*)FTop(*END*)
  | FAtom n ⇒ if (*BEGIN*)eqb n x(*END*) then (*BEGIN*)G(*END*) else ((*BEGIN*)FAtom n(*END*))
  (*BEGIN*)
  | FAnd F1 F2 ⇒ FAnd (subst x G F1) (subst x G F2)
  | FOr F1 F2 ⇒ FOr (subst x G F1) (subst x G F2)
  | FImpl F1 F2 ⇒ FImpl (subst x G F1) (subst x G F2)
  (*END*)
  | FNot F ⇒ FNot (subst x G F)
  ].


(* NOTA
   ====
   
   I comandi che seguono definiscono la seguente notazione:

  * F [ G / x ]
  
  Questa notazione utilizza la funzione `subst` appena definita, in particolare
  la scrittura `F [ G /x ]` è una abbreviazione per `subst x G F`. 
  
  * F ≡ G
  
  Questa notazione è una abbreviazione per `∀v.[[ f ]]v = [[ g ]]v`. 
  Asserisce che for ogni funzione di valutazione `v`, la semantica di `f`
  in `v` è uguale alla semantica di `g` in `v`.


  ATTENZIONE
  ==========
  
  Non modificare le linee seguenti 
*)
notation < "t [ \nbsp term 19 a / term 19 b \nbsp ]" non associative with precedence 90 for @{ 'substitution $b $a $t }.
notation > "t [ term 90 a / term 90 b]" non associative with precedence 90 for @{ 'substitution $b $a $t }.
interpretation "Substitution for Formula" 'substitution b a t = (subst b a t).
definition equiv ≝ λF1,F2. ∀v.[[ F1 ]]v = [[ F2 ]]v.
notation "hvbox(a \nbsp break mstyle color #0000ff (≡) \nbsp b)"  non associative with precedence 45 for @{ 'equivF $a $b }.
notation > "a ≡ b" non associative with precedence 55 for @{ equiv $a $b }.
interpretation "equivalence for Formulas" 'equivF a b = (equiv a b).

(* Test 2
   ======
   
   Viene fornita una formula di esempio `esempio2`,
   e una formula `esempio3` che rimpiazzerà gli atomi
   `FAtom 2` di `esempio2`.
   
   Il risultato atteso è la formula:
   
        FAnd (FImpl (FOr (FAtom O) (FAtom 1)) (FAtom 1)) 
             (FOr (FAtom O) (FAtom 1))
   
*)

definition esempio2 ≝ (FAnd (FImpl (FAtom 2) (FAtom 1)) (FAtom 2)). 
   
definition esempio3 ≝ (FOr (FAtom 0) (FAtom 1)).

(* Decommenta ed esegui *)

(* eval normalize on (esempio2 [ esempio3 / 2]). *)

(*DOCBEGIN
   
Il linguaggio di dimostrazione di Matita
========================================

L'ultimo esercizio richiede di scrivere una dimostrazione. Tale dimostrazione
deve essere scritta utilizzando il linguaggio di dimostrazione di Matita.
Tale linguaggio è composto dai seguenti comandi:

* `assume nome : tipo`

  Quando si deve dimostrare un tesi come `∀F : Formula.P`, il comando
  `assume F : Formula` fissa una generica `Formula` `F` e la tesi
  diventa `P` dove `F` è fissata. 

* `suppose P (nome)`

  Quando si deve dimostrare una tesi come `P → Q`, il comando
  `suppose P (Ipotesi1)` da il nome `Ipotesi1` a `P` e cambia la tesi
  `Q`, che ora può essere dimostrata facendo riferimento all'assunzione 
  `P` tramite il nome `Ipotesi1`. 

* `we procede by induction on F to prove Q`

  Se `F` è il nome di una (ad esempio) `Formula` precedentemente
  assunta tramite il comando `assume`, inizia una prova per induzione su `F`.  

* `case name`

  Nelle prove per induzione o per casi, ogni caso deve iniziare con il
  comando `case nome`, ad esempio se si procede per induzione di una
  formula uno dei casi sarà quello in cui la formula è `⊥`, si deve quindi
  iniziare la sotto dimostrazione per tale caso con `case ⊥`. 

* `we procede by cases on x to prove Q`

  Analogo a `we procede by induction on F to prove Q`

* `by induction hypothesis we know P (name)`

  Nei casi non base di una prova per induzione sono disponibili delle ipotesi
  induttive, quindi la tesi è della forma `P → Q`, ed è possibile 
  dare un nome a `P` e procedere a dimostrare `Q`. Simile a `suppose`. 

* `the thesis becomes P` 

  Permette di modificare la tesi, utilizzando le definizioni (eventualmente 
  ricorsive) che vi compaiono. Ad esempio se la tesi fosse `min 3 5 = max 1 3`
  si potrebbe usare il comando `the thesis becomes (3 = max 1 3)` in quanto
  per definizione di minimo, il minimo tra `3` e `5` è `3`. 

* `by name1 we proved P (name2)`

  Permette di ottenere una nuova ipotesi `P` chiamandola `name2` utilizzando 
  l'ipotesi `name1`. 

* `conclude (P) = (Q) by name`

  Quando la tesi è della forma `P = Q`, si possono utilizzare delle ipotesi
  della forma `A = B` riscrivendo `A` in `B` (o viceversa) in `P`. Per esempio
  se la tesi fosse `sin π + 3 = 7 - 4` e si avesse una ipotesi `sin π = 0` dal
  nome `H`, si potrebbe usare il comando `conclude (sin π + 3) = (0 + 3) by H`
  per cambiare la conclusione in `0 + 3 = 7 - 4`.

* `= (P) by name`

  Da utilizzare in seguito a un comando `conclude` per riscrivere con altre
  ipotesi. 

* `done`

  Termina un caso della dimostrazione, è possibile utilizzarlo quando la tesi
  è della forma `t = t`, ad esempio `0 = 0` oppure `v x = v x`.
      
DOCEND*)

(* Esercizio 4
   ===========
   
   Dimostra il teorema di sostituzione visto a lezione
*)
theorem sostituzione: ∀G1,G2,F,x. G1 ≡ G2 → F[G1/x] ≡ F[G2/x].
assume G1 : Formula.
assume G2 : Formula.
(*BEGIN*)
assume F : Formula.
assume x : ℕ.
(*END*)
suppose (G1 ≡ G2) (H).
we proceed by induction on F to prove (F[ G1/x ] ≡ F[ G2/x ]). 
case FBot.
  the thesis becomes (FBot[ G1/x ] ≡ FBot[ G2/x ]).
  the thesis becomes (FBot ≡ FBot[ G2/x ]).
  the thesis becomes (FBot ≡ FBot).
  the thesis becomes (∀v.[[FBot]]v = [[FBot]]v).
  assume v : (ℕ → ℕ).
  the thesis becomes (0 = [[FBot]]v).
  the thesis becomes (0 = 0).
  done.  
case FTop.
  (*BEGIN*)
  the thesis becomes (FTop[ G1/x ] ≡ FTop[ G2/x ]).
  the thesis becomes (FTop ≡ FTop).
  the thesis becomes (∀v. [[FTop]]v = [[FTop]]v).
  assume v : (ℕ → ℕ).
  the thesis becomes (1 = 1).
  (*END*)
  done.
case FAtom.
  assume n : ℕ.
  the thesis becomes ((FAtom n)[ G1/x ] ≡ (FAtom n)[ G2/x ]).
  the thesis becomes 
    (if eqb n x then G1 else (FAtom n) ≡ (FAtom n)[ G2/x ]).    
  the thesis becomes
    (if eqb n x then G1 else (FAtom n) ≡
     if eqb n x then G2 else (FAtom n)).
  we proceed by cases on (eqb n x) to prove 
    (if eqb n x then G1 else (FAtom n) ≡
     if eqb n x then G2 else (FAtom n)).
  case true.
    the thesis becomes (G1 ≡ G2).
    by H done.
  case false.
    (*BEGIN*)
    the thesis becomes (FAtom n ≡ FAtom n).
    the thesis becomes (∀v. [[FAtom n]]v = [[FAtom n]]v).
    assume v : (ℕ → ℕ).
    the thesis becomes (v n = v n).
    (*END*)
    done.
case FAnd.
  assume F1 : Formula.
  by induction hypothesis we know (F1[ G1/x ] ≡ F1[ G2/x ]) (IH1).    
  assume F2 : Formula.
  by induction hypothesis we know (F2[ G1/x ] ≡ F2[ G2/x ]) (IH2).    
  the thesis becomes 
    (∀v.[[ (FAnd F1 F2)[ G1/x ] ]]v = [[ (FAnd F1 F2)[ G2/x ] ]]v).
  assume v : (ℕ → ℕ). 
  the thesis becomes 
    (min ([[ F1[ G1/x ] ]]v) ([[ F2[ G1/x ] ]]v) = 
     min ([[ F1[ G2/x ] ]]v) ([[ F2[ G2/x ] ]]v)).
  by IH1 we proved (∀v1.[[ F1[ G1/x ] ]]v1 = [[ F1[ G2/x ] ]]v1) (IH11).
  by (*BEGIN*)IH2(*END*) we proved (∀v2.[[ F2[ G1/x ] ]]v2 = [[ F2[ G2/x ] ]]v2) (IH22).
  by IH11 we proved ([[ F1[ G1/x ] ]]v = [[ F1[ G2/x ] ]]v) (IH111).
  by (*BEGIN*)IH22(*END*) we proved ([[ F2[ G1/x ] ]]v = [[ F2[ G2/x ] ]]v) (IH222).
  conclude 
      (min ([[ F1[ G1/x ] ]]v) ([[ F2[ G1/x ] ]]v)) 
    = (min ([[ F1[ G2/x ] ]]v) ([[ F2[ G1/x ] ]]v)) by IH111.
    = (min ([[(F1[ G2/x ])]]v) ([[(F2[ G2/x ])]]v)) by (*BEGIN*)IH222(*END*).
  (*END*)
  done.
case FOr.
  (*BEGIN*) 
  assume F1 : Formula.
  by induction hypothesis we know (F1[ G1/x ] ≡ F1[ G2/x ]) (IH1).    
  assume F2 : Formula.
  by induction hypothesis we know (F2[ G1/x ] ≡ F2[ G2/x ]) (IH2).    
  the thesis becomes 
    (∀v.[[ (FOr F1 F2)[ G1/x ] ]]v = [[ (FOr F1 F2)[ G2/x ] ]]v).
  assume v : (ℕ → ℕ). 
  the thesis becomes 
    (max ([[ F1[ G1/x ] ]]v) ([[ F2[ G1/x ] ]]v) = 
     max ([[ F1[ G2/x ] ]]v) ([[ F2[ G2/x ] ]]v)).
  by IH1 we proved (∀v1.[[ F1[ G1/x ] ]]v1 = [[ F1[ G2/x ] ]]v1) (IH11).
  by IH2 we proved (∀v2.[[ F2[ G1/x ] ]]v2 = [[ F2[ G2/x ] ]]v2) (IH22).
  by IH11 we proved ([[ F1[ G1/x ] ]]v = [[ F1[ G2/x ] ]]v) (IH111).
  by IH22 we proved ([[ F2[ G1/x ] ]]v = [[ F2[ G2/x ] ]]v) (IH222).
  conclude 
      (max ([[ F1[ G1/x ] ]]v) ([[ F2[ G1/x ] ]]v)) 
    = (max ([[ F1[ G2/x ] ]]v) ([[ F2[ G1/x ] ]]v)) by IH111.
    = (max ([[(F1[ G2/x ])]]v) ([[(F2[ G2/x ])]]v)) by IH222.
  (*END*)
  done.
case FImpl.
  (*BEGIN*)
  assume F1 : Formula.
  by induction hypothesis we know (F1[ G1/x ] ≡ F1[ G2/x ]) (IH1).
  assume F2 : Formula.
  by induction hypothesis we know (F2[ G1/x ] ≡ F2[ G2/x ]) (IH2).
  the thesis becomes 
    (∀v.max (1 - [[ F1[ G1/x ] ]]v) ([[ F2[ G1/x ] ]]v) =
        max (1 - [[ F1[ G2/x ] ]]v) ([[ F2[ G2/x ] ]]v)).
  assume v : (ℕ → ℕ).       
  by IH1 we proved ([[ F1[ G1/x ] ]]v = [[ F1[ G2/x ] ]]v) (IH11).
  by IH2 we proved ([[ F2[ G1/x ] ]]v = [[ F2[ G2/x ] ]]v) (IH22).
  conclude 
      (max (1-[[ F1[ G1/x ] ]]v) ([[ F2[ G1/x ] ]]v))
    = (max (1-[[ F1[ G2/x ] ]]v) ([[ F2[ G1/x ] ]]v)) by IH11.  
    = (max (1-[[ F1[ G2/x ] ]]v) ([[ F2[ G2/x ] ]]v)) by IH22.
  done. 
case FNot.
  (*BEGIN*)
  assume F1 : Formula.
  by induction hypothesis we know (F1[ G1/x ] ≡ F1[ G2/x ]) (IH).   
  the thesis becomes (FNot (F1[ G1/x ]) ≡ FNot (F1[ G2/x ])).
  the thesis becomes (∀v.[[FNot (F1[ G1/x ])]]v = [[FNot (F1[ G2/x ])]]v).
  assume v : (ℕ → ℕ).
  the thesis becomes (1 - [[F1[ G1/x ]]]v = [[FNot (F1[ G2/x ])]]v).
  the thesis becomes (1 - [[ F1[ G1/x ] ]]v = 1 - [[ F1[ G2/x ] ]]v).
  by IH we proved (∀v1.[[ F1[	 G1/x ] ]]v1 = [[ F1[ G2/x ] ]]v1) (IH1).
  by IH1 we proved ([[ F1[ G1/x ] ]]v = [[ F1[ G2/x ] ]]v) (IH2).
  conclude 
      (1-[[ F1[ G1/x ] ]]v) 
    = (1-[[ F1[ G2/x ] ]]v) by IH2.
  (*END*)
  done.
qed.
    
(* Questionario

   Compilare mettendo una X nella risposta scelta.

   1) Pensi che sia utile l'integrazione del corso con una attività di 
      laboratorio?
   
      [ ] per niente        [ ] poco     [ ] molto       
     
     
   2) Pensi che gli esercizi proposti ti siano stati utili a capire meglio
      quanto visto a lezione?
   
      [ ] per niente        [ ] poco     [ ] molto       


   3) Gli esercizi erano
    
      [ ] troppo facili     [ ] alla tua portata      [ ] impossibili       

     
   4) Il tempo a disposizione è stato     
   
      [ ] poco              [ ] giusto          [ ] troppo       

     
   5) Cose che miglioreresti nel software Matita
     
      .........

      
   6) Suggerimenti sullo svolgimento delle attività in laboratorio
   
        .........

   
*) 
   
         
