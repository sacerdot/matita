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

(*DOCBEGIN

I connettivi logici
===================

Per digitare i connettivi logici:

* `∧` : `\land`
* `∨` : `\lor`
* `¬` : `\lnot`
* `⇒` : `=>`, `\Rightarrow` 
* `⊥` : `\bot`
* `⊤` : `\top`

Per digitare i quantificatori:

* `∀` : `\forall`
* `∃` : `\exists`

I termini, le formule e i nomi delle ipotesi
============================================

* I termini quantificati da `∀` e `∃`, quando argomenti di
  una regola, vengono scritti tra `{` e `}`.

* Le formule, quando argomenti di
  una regola, vengono scritte tra `(` e `)`.

* I nomi delle ipotesi, quando argomenti di
  una regola, vengono scritti tra `[` e `]`.

Le regole di deduzione naturale
===============================

Per digitare le regole di deduzione naturale
è possibile utilizzare la palette che compare
sulla sinistra dopo aver premuto `F2`.

L'albero si descrive partendo dalla radice. Le regole
con premesse multiple sono seguite da `[`, `|` e `]`.
Ad esempio: 

        apply rule (∧#i (A∨B) ⊥);
          [ …continua qui il sottoalbero per (A∨B)
          | …continua qui il sottoalbero per ⊥
          ] 

Le regole vengono applicate alle loro premesse, ovvero
gli argomenti delle regole sono le formule che normalmente 
scrivete sopra la linea che rappresenta l'applicazione della
regola stessa. Ad esempio:

        apply rule (∨#e (A∨B) [h1] C [h2] C);
          [ …prova di (A∨B)
          | …prova di C sotto l'ipotesi A (di nome h1)  
          | …prova di C sotto l'ipotesi B (di nome h2)
          ]

Le regole che hanno una sola premessa non vengono seguite 
da parentesi quadre.

L'albero di deduzione
=====================

Per visualizzare l'albero man mano che viene costruito
dai comandi impartiti al sistema, premere `F3` e poi
premere sul bottome home (in genere contraddistinto da
una icona rappresentate una casa).

Si suggerisce di marcare tale finestra come `always on top`
utilizzando il menu a tendina che nella maggior parte degli
ambienti grafici si apre cliccando nel suo angolo in 
alto a sinistra.

Applicazioni di regole errate vengono contrassegnate con
il colore rosso.

Usare i lemmi dimostrati in precedenza
======================================

Una volta dimostrati alcuni utili lemmi come `A ∨ ¬A` è possibile
riutilizzarli in altre dimostrazioni utilizzando la "regola" `lem`.

La "regola" `lem` prende come argomenti:

- Il numero delle ipotesi del lemma che si vuole utilizzare, nel
  caso del terzo escluso `0`, nel caso di `¬¬A⇒A` le ipotesi sono `1`.

- Dopo il numero di ipotesi, è necessario digitare il nome del lemma.

- Infine, le formule che devono essere scritte come premesse per la 
  "regola".

Ad esempio, per usare il lemma EM (terzo escluso) basta digitare
`lem 0 EM`, mentre per usare il lemma NNAA (`¬¬A⇒A`) bisogna digitare
`lem 1 NNAA (¬¬A)`. Ai lemmi con più di una premessa è necessario 
far seguire le parentesi quadre come spiegato in precedenza.

Si noti che "regola" `lem` non è una vera regola, ma una forma compatta
per rappresentare l'albero di prova del lemma che si sta riutilizzando.

Per motivi che saranno più chiari una volta studiate logiche del 
primo ordine o di ordine superiore, i lemmi che si intende 
riutilizzare è bene che siano dimostrati astratti sugli atomi. 
Ovvero per ogni atomo `A`...`Z` che compare nella formula, 
è bene aggiungere una quantificazione all'inizio della formula stessa.
Ad esempio scrivendo `∀A:CProp.` prima della formula `A ∨ ¬A`.
La dimostrazione deve poi iniziare con il comando `assume`. 

In tale modo il lemma EM può essere utilizzato sia per dimostrare 
`A ∨ ¬A`, sia `B ∨ ¬B`, sia `(A∨C) ∨ ¬(A∨C)`, etc ...

DOCEND*)

include "nat/plus.ma".

lemma ex0: ∀n. n + O = n.
 assume n: nat.
 we proceed by induction on n to prove (n + O = n).
  case O.
   the thesis becomes (O + O = O).
    conclude
        (O + O)
      = O
    done.
  case S.
   assume n : nat.
   by induction hypothesis we know (n + O = n) (H).
   the thesis becomes (S n + O = S n).
    conclude
       (S n + O)
     = (S (n + O)).
     = (S n) by H
    done.
qed.

include "didactic/support/natural_deduction.ma".

(* Il nostro linguaggio del primo ordine prevede le seguenti 
   - costanti: O
   - funzioni: S (unaria), plus, mult (binarie)
   - predicati: eq (binari)
*)
axiom O : sort.                  (* zero *)
axiom S : sort → sort.           (* successore *)
axiom plus : sort → sort → sort. (* addizione *)
axiom mult: sort → sort → sort.  (* moltiplicazione *)
axiom eq : sort → sort → CProp.  (* uguaglianza *)

(*
notation < "+  term 90 x  term 90 y" non associative with precedence 80 for @{'plus $x $y}.
notation < "★  term 90 x  term 90 y" non associative with precedence 80 for @{'mult $x $y}.
notation < "=  term 90 x  term 90 y" non associative with precedence 80 for @{'eq $x $y}.
notation < "\S  term 90 x" non associative with precedence 80 for @{'S $x}.
notation < "\O" non associative with precedence 80 for @{'O}.
interpretation "O" 'O = O.
interpretation "S" 'S x y = (S x y).
interpretation "mult" 'mult x y = (mult x y).
interpretation "plus" 'plus x y = (plus x y).
interpretation "eq" 'eq x y = (eq x y).
*)

interpretation "+" 'my_plus x y = (plus x y). 
interpretation "*" 'my_mult x y = (mult x y).
interpretation "=" 'my_eq x y = (eq x y).
interpretation "S" 'my_S x = (S x).
interpretation "O" 'my_O = O.

notation "x + y" non associative with precedence 55 for @{'my_plus $x $y}.
notation "x * y" non associative with precedence 60 for @{'my_mult $x $y}.
notation "x = y" non associative with precedence 45 for @{'my_eq $x $y}.
notation > "'S' x" non associative with precedence 40 for @{'my_S $x}.
notation < "'S'  x" non associative with precedence 40 for @{'my_S $x}.
notation "'O'" non associative with precedence 90 for @{'my_O}.

(* Assumiamo la seguente teoria *)

(* l'uguaglianza e' una relazione d'equivalenza *)
axiom refl: ∀x. x = x.
axiom sym: ∀x.∀y. x = y ⇒ y = x.
axiom trans: ∀x.∀y.∀z. x = y ⇒ y = z ⇒ x = z.

(* assiomi di Peano *)
axiom discr: ∀x. ¬ O = (S x).
axiom inj: ∀x.∀y. (S x) = (S y) ⇒ x = y.
(* Questo è uno schema di assiomi: è come avere una regola di induzione per 
   ogni predicato unario P. Il sistema inferisce automaticamente P. *)  
axiom induct: ΠP. P O ⇒ (∀n. P n ⇒ P (S n)) ⇒ ∀x.P x.

(* definizione ricorsiva di addizione *)
axiom plus_O: ∀x. O + x = x.
axiom plus_S: ∀x.∀y. (S x) + y = S (x + y).

(* definizione ricorsiva di moltiplicazione *)
axiom mult_O: ∀x.O * x = O.
axiom mult_S: ∀x.∀y. (S x) * y = x * y + y.

(* l'uguaglianza e' una congruenza rispetto a tutte le funzioni e predicati *)
axiom eq_S: ∀x.∀x'. x = x' ⇒ (S x) = (S x').
axiom eq_plus: ∀x.∀x'.∀y.∀y'. x = x' ⇒ y = y' ⇒ x + y = x' + y'.
axiom eq_mult: ∀x.∀x'.∀y.∀y'. x = x' ⇒ y = y' ⇒ x * y = x' * y'.

(* intuizionista *)
lemma ex1: ∀x.x + O = x.
apply rule (prove (∀x.x + O = x));
(* poichè tutti gli assiomi della teoria sono assiomi e non dimostrazioni,
   l'unica forma di `apply rule lem` che potete usare è 
   `apply rule (lem 0 nome_assioma)` *)
(*BEGIN*)
apply rule (⇒#e ((∀n.(n + O) = n ⇒ ((S n) + O) = (S n)) ⇒ (∀x.(x + O) = x)) (∀n.(n + O) = n ⇒ ((S n) + O) = (S n)));
	[ apply rule (⇒#e ((O + O) = O ⇒ (∀n.n + O = n ⇒ ((S n) + O) = (S n)) ⇒ (∀x.(x + O) = x)) (O + O = O));
	   [ apply rule (lem 0 induct);
	   | apply rule (∀#e {O} (∀y.(O + y) =y));
	     apply rule (lem 0 plus_O);
	   ]
	| apply rule (∀#i {n} (n + O = n ⇒ ((S n) + O) = (S n)));
    apply rule (⇒#i [H] (((S n) + O) = (S n)));
    apply rule (⇒#e ((S (n + O)) = (S n) ⇒ ((S n) + O) = (S n)) ((S (n + O)) = (S n)));
	   [ apply rule (⇒#e (((S n) + O) =(S (n + O)) ⇒ (S (n + O)) = (S n)⇒((S n) + O) =(S n)) (((S n) + O) =(S (n + O))));
	      [ apply rule (∀#e {S n} (∀z.((S n) + O) =(S (n + O))⇒(S (n + O))= z⇒((S n) + O) =z));
	        apply rule (∀#e {(S (n + O))} (∀y.∀z.((S n) + O) =y ⇒ y = z ⇒ ((S n) + O) =z));
          apply rule (∀#e {(S n) + O} (∀x.∀y.∀z.x = y ⇒ y = z ⇒ x = z));
          apply rule (lem 0 trans);
	      | apply rule (∀#e {O} (∀m.(S n) + m = (S (n + m))));
          apply rule (∀#e {n} (∀n.∀m.(S n) + m = (S (n + m))));
          apply rule (lem 0 plus_S);
	      ]
	   | apply rule (⇒#e (n + O = n ⇒ (S (n + O)) = (S n)) (n + O = n));
	      [ apply rule (∀#e {n} (∀w.n + O = w ⇒ (S (n + O)) = (S w)));
          apply rule (∀#e {(n + O)} (∀y.∀w.y = w ⇒ (S y) = (S w)));
          apply rule (lem 0 eq_S);
	      | apply rule (discharge [H]);
	      ]
	   ]
	]
(*END*)
qed.
