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

        aply rule (∨#e (A∨B) [h1] C [h2] C);
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


include "didactic/support/natural_deduction.ma".

(* Il nostro linguaggio del primo ordine prevede le seguenti 
   - costanti: c
   - funzioni: f, g (unarie), h (binaria)
   - predicati: P, Q (unari), R, S (binari) 
*)
axiom c : sort.
axiom f : sort → sort.
axiom g : sort → sort.
axiom h : sort → sort → sort.
axiom P : sort → CProp.
axiom Q : sort → CProp.
axiom R : sort →sort → CProp.
axiom S : sort →sort → CProp.

(* assumiamo il terzo escluso *)
theorem EM: ∀A:CProp. A ∨ ¬ A.
assume A: CProp.
apply rule (prove (A ∨ ¬A));
apply rule (RAA [H] (⊥)).
apply rule (¬#e (¬(A ∨ ¬A)) (A ∨ ¬A));
        [ apply rule (discharge [H]).
        | apply rule (⊥#e (⊥));
          apply rule (¬#e (¬¬A) (¬A));
           [ apply rule (¬#i [K] (⊥)).
       apply rule (¬#e (¬(A ∨ ¬A)) (A ∨ ¬A));
              [ apply rule (discharge [H]).
              | apply rule (∨#i_r (¬A)).
          apply rule (discharge [K]).
              ]
           | apply rule (¬#i [K] (⊥)).
       apply rule (¬#e (¬(A ∨ ¬A)) (A ∨ ¬A));
              [ apply rule (discharge [H]).
              | apply rule (∨#i_l (A)).
          apply rule (discharge [K]).
              ]
           ]
        ]
qed.

(* intuizionista *)
lemma ex1: ¬(∃x.P x) ⇒ ∀x.¬ P x.
apply rule (prove (¬(∃x.P x) ⇒ ∀x.¬ P x));
(*BEGIN*)
apply rule (⇒#i [h1] (∀x.¬ P x));
apply rule (∀#i {l} (¬P l));
apply rule (¬#i [h2] (⊥));
apply rule (¬#e (¬(∃x.P x)) (∃x.P x));
	[ apply rule (discharge [h1]);
	| apply rule (∃#i {l} (P l));
	  apply rule (discharge [h2]);
	]
(*END*)
qed.

(* classico *)
lemma ex2: ¬(∀x.P x) ⇒ ∃x.¬ P x.
apply rule (prove (¬(∀x.P x) ⇒ ∃x.¬ P x));
(*BEGIN*)
apply rule (⇒#i [h1] (∃x.¬ P x));
apply rule (RAA [h2] (⊥));
apply rule (¬#e (¬(∀x.P x)) (∀x.P x));
	[ apply rule (discharge [h2]);
	| apply rule (∀#i {y} (P y));
    apply rule (RAA [h3] (⊥));
    apply rule (¬#e (¬∃x.¬ P x) (∃x.¬ P x));
	   [ apply rule (discharge [h2]);
	   | apply rule (∃#i {y} (¬P y));
       apply rule (discharge [h3]);
	   ]
	]
(*END*)
qed.

(* intuizionista *)
lemma ex3: ((∃x.P x) ⇒ Q c) ⇒ ∀x.P x ⇒ Q c.
apply rule (prove (((∃x.P x) ⇒ Q c) ⇒ ∀x.P x ⇒ Q c));
(*BEGIN*)
apply rule (⇒#i [h1] (∀x.P x ⇒ Q c));
apply rule (∀#i {l} (P l ⇒ Q c));
apply rule (⇒#i [h2] (Q c));
apply rule (⇒#e ((∃x.P x) ⇒ Q c) (∃x.P x));
	[ apply rule (discharge [h1]);
	| apply rule (∃#i {l} (P l));
	  apply rule (discharge [h2]);
	]
(*END*)
qed.

(* classico *)
lemma ex4: ((∀x.P x) ⇒ Q c) ⇒ ∃x.P x ⇒ Q c.
apply rule (prove (((∀x.P x) ⇒ Q c) ⇒ ∃x.P x ⇒ Q c));
(*BEGIN*)
apply rule (⇒#i [h1] (∃x.P x ⇒ Q c));
apply rule (∨#e ((∀x.P x) ∨ ¬(∀x.P x)) [h3] (?) [h3] (?));
	[ apply rule (lem 0 EM);
	| apply rule (∃#i {y} (P y ⇒ Q c));
       apply rule (⇒#i [h4] (Q c));
       apply rule (⇒#e ((∀x.P x) ⇒ Q c) ((∀x.P x)));
	       [ apply rule (discharge [h1]);
         | apply rule (discharge [h3]);
	       ]
  | apply rule (∃#e (∃x.¬P x) {y} [h4] (∃x.P x ⇒ Q c));
	   [ apply rule (lem 1 ex2 (¬(∀x.P x)));
	     apply rule (discharge [h3]);
     | apply rule (∃#i {y} (P y ⇒ Q c));
       apply rule (⇒#i [h5] (Q c));
       apply rule (⊥#e (⊥));
       apply rule (¬#e (¬P y) (P y));
	       [ apply rule (discharge [h4]);
	       | apply rule (discharge [h5]);
	       ]
	   ]
  ]
(*END*)
qed.
