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

(* Istruzioni: 

     http://mowgli.cs.unibo.it/~tassi/exercise-natural_deduction.html 

*)

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

Scopo della lezione
===================

Lo scopo della lezione è di farvi imparare ad usare Matita
per auto-correggervi gli esercizi di deduzione naturale, che
saranno parte dell'esame scritto. Il consiglio è di 
fare prima gli esercizi su carta e poi digitarli in Matita
per verificarne la correttezza. Fare direttamente gli esercizi
con Matita è difficile e richiede molto più tempo.

I connettivi logici
===================

Per digitare i connettivi logici:

* `∧` : `\land`
* `∨` : `\lor`
* `¬` : `\lnot`
* `⇒` : `=>`, `\Rightarrow` 
* `⊥` : `\bot`
* `⊤` : `\top`

I termini, le formule e i nomi delle ipotesi
============================================

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

theorem EM: ∀A:CProp. A ∨ ¬ A.
(* Il comando assume è necessario perchè dimostriamo A∨¬A
   per una A generica. *)
assume A: CProp.
(* Questo comando inizia a disegnare l'albero *)
apply rule (prove (A ∨ ¬A));
(* qui inizia l'albero, eseguite passo passo osservando come
   si modifica l'albero. *)
apply rule (RAA [H] (⊥)).
apply rule (¬#e (¬(A ∨ ¬A)) (A ∨ ¬A));
	[ apply rule (discharge [H]).
	| apply rule (⊥#e (⊥));
	  apply rule (¬#e (¬¬A) (¬A));
	   [ apply rule (¬#i [K] (⊥)).
       apply rule (¬#e (¬(A ∨ ¬A)) (A ∨ ¬A));
	      [ (*BEGIN*)apply rule (discharge [H]).(*END*)
	      | (*BEGIN*)apply rule (∨#i_r (¬A)).
          apply rule (discharge [K]).(*END*)
	      ]
	   | (*BEGIN*)apply rule (¬#i [K] (⊥)).
       apply rule (¬#e (¬(A ∨ ¬A)) (A ∨ ¬A));
	      [ apply rule (discharge [H]).
	      | apply rule (∨#i_l (A)).
          apply rule (discharge [K]).
	      ](*END*)
	   ]
	]
qed.

theorem ex1 : (C∧G ⇒ E) ⇒ (¬L ⇒ E∨C) ⇒ G ∨ L ⇒ ¬L ⇒ E.
apply rule (prove ((C∧G ⇒ E) ⇒ (¬L ⇒ E∨C) ⇒ G ∨ L ⇒ ¬L ⇒ E));
(*BEGIN*)
apply rule (⇒#i [h1] ((¬L ⇒ E∨C) ⇒ G ∨ L ⇒ ¬L ⇒ E));
apply rule (⇒#i [h2] (G ∨ L ⇒ ¬L ⇒ E));
apply rule (⇒#i [h3] (¬L ⇒ E));
apply rule (⇒#i [h4] (E));
apply rule (∨#e (G∨L) [h5] (E) [h6] (E));
	[ apply rule (discharge [h3]);
	| apply rule (∨#e (E∨C) [h6] (E) [h7] (E));
	    [ apply rule (⇒#e (¬L ⇒ E∨C) (¬L));
	        [ apply rule (discharge [h2]);
	        | apply rule (discharge [h4]);
	        ]
	    | apply rule (discharge [h6]);
	    | apply rule (⇒#e (C∧G ⇒ E) (C∧G));
	        [ apply rule (discharge [h1]);
	        | apply rule (∧#i (C) (G));
	            [ apply rule (discharge [h7]);
	            | apply rule (discharge [h5]);
             	]
	        ]
	    ]
	| apply rule (⊥#e (⊥));
	  apply rule (¬#e (¬L) (L));
	    [ apply rule (discharge [h4]);
	    | apply rule (discharge [h6]);
	    ]
	]
(*END*)
qed.

theorem ex2 : (A∧¬B ⇒ C) ⇒ (B∧D ⇒ C) ⇒ (D ⇒ A) ⇒ D ⇒ C.
apply rule (prove ((A∧¬B ⇒ C) ⇒ (B∧D ⇒ C) ⇒ (D ⇒ A) ⇒ D ⇒ C));
(*BEGIN*)
apply rule (⇒#i [h1] ((B∧D ⇒ C) ⇒ (D ⇒ A) ⇒ D ⇒ C));
apply rule (⇒#i [h2] ((D ⇒ A) ⇒ D ⇒ C));
apply rule (⇒#i [h3] (D ⇒ C));
apply rule (⇒#i [h4] (C));
apply rule (∨#e (B∨¬B) [h5] (C) [h6] (C));
	[ apply rule (lem 0 EM);
	| apply rule (⇒#e (B∧D⇒C) (B∧D));
	    [ apply rule (discharge [h2]);
    	| apply rule (∧#i (B) (D));
	        [ apply rule (discharge [h5]);
	        | apply rule (discharge [h4]);
	        ]
	    ] 
	| apply rule (⇒#e (A∧¬B⇒C) (A∧¬B));
	    [ apply rule (discharge [h1]);
	    | apply rule (∧#i (A) (¬B));
	        [ apply rule (⇒#e (D⇒A) (D));
	            [ apply rule (discharge [h3]);
	            | apply rule (discharge [h4]);
	            ]
	        | apply rule (discharge [h6]);
	        ]
	    ]
	]
(*END*)
qed.

(* Per dimostrare questo teorema torna comodo il lemma EM
   dimostrato in precedenza. *)
theorem ex3: (F ⇒ G∨E) ⇒ (G ⇒ ¬L∨E) ⇒ (L⇒F) ⇒ L ⇒ E.
apply rule (prove ((F ⇒ G∨E) ⇒ (G ⇒ ¬L∨E) ⇒ (L⇒F) ⇒ L ⇒ E));
(*BEGIN*)
apply rule (⇒#i [h1] ((G ⇒ ¬L∨E) ⇒ (L⇒F) ⇒ L ⇒ E));
apply rule (⇒#i [h2] ((L⇒F) ⇒ L ⇒ E));
apply rule (⇒#i [h3] (L ⇒ E));
apply rule (⇒#i [h4] (E));
apply rule (∨#e (G∨E) [h5] (E) [h6] (E));
	[ apply rule (⇒#e (F ⇒ G∨E) (F));
	    [ apply rule (discharge [h1]);
	    | apply rule (⇒#e (L⇒F) (L));
	        [ apply rule (discharge [h3]);
	        | apply rule (discharge [h4]);
	        ]
	    ]
	|apply rule (∨#e (¬L∨E) [h7] (E) [h8] (E));
	    [ apply rule (⇒#e (G⇒¬L∨E) (G));
	        [ apply rule (discharge [h2]);
	        | apply rule (discharge [h5]);
	        ]
	    | apply rule (⊥#e (⊥));
        apply rule (¬#e (¬L) (L));
	        [ apply rule (discharge [h7]);
	        | apply rule (discharge [h4]);
	        ]
	    | apply rule (discharge [h8]);
	    ]
	| apply rule (discharge [h6]);
	]
(*END*)
qed.

theorem ex4: ¬(A∧B) ⇒ ¬A∨¬B.
apply rule (prove (¬(A∧B) ⇒ ¬A∨¬B));
(*BEGIN*)
apply rule (⇒#i [h1] (¬A∨¬B));
apply rule (∨#e (A ∨ ¬A) [h2] ((¬A∨¬B)) [h3] ((¬A∨¬B)));
	[ apply rule (lem 0 EM);
	| apply rule (∨#e (B ∨ ¬B) [h4] ((¬A∨¬B)) [h5] ((¬A∨¬B)));
	    [ apply rule (lem 0 EM);
	    | apply rule (⊥#e (⊥));
	      apply rule (¬#e (¬(A∧B)) (A∧B));
	        [ apply rule (discharge [h1]);
	        | apply rule (∧#i (A) (B));
	            [ apply rule (discharge [h2]);
	            | apply rule (discharge [h4]);
	            ]
	        ]
	    | apply rule (∨#i_r (¬B));
        apply rule (discharge [h5]);
	    ]
	| apply rule (∨#i_l (¬A));
    apply rule (discharge [h3]);
	]
(*END*)
qed.

theorem ex5: ¬(A∨B) ⇒ (¬A ∧ ¬B).
apply rule (prove (¬(A∨B) ⇒ (¬A ∧ ¬B)));
(*BEGIN*)
apply rule (⇒#i [h1] (¬A ∧ ¬B));
apply rule (∨#e (A∨¬A) [h2] (¬A ∧ ¬B) [h3] (¬A ∧ ¬B));
	[ apply rule (lem 0 EM);
	| apply rule (⊥#e (⊥));
    apply rule (¬#e (¬(A∨B)) (A∨B));
	    [ apply rule (discharge [h1]);
	    | apply rule (∨#i_l (A));
        apply rule (discharge [h2]);
	    ]
	| apply rule (∨#e (B∨¬B) [h10] (¬A ∧ ¬B) [h11] (¬A ∧ ¬B));
	    [ apply rule (lem 0 EM);
	    | apply rule (⊥#e (⊥));
        apply rule (¬#e (¬(A∨B)) (A∨B));
	        [ apply rule (discharge [h1]);
	        | apply rule (∨#i_r (B));
            apply rule (discharge [h10]);
	        ] 
	    | apply rule (∧#i (¬A) (¬B));
	        [ apply rule (discharge [h3]);
	        |apply rule (discharge [h11]);
	        ]
	    ]
	]
(*END*)
qed.

theorem ex6: ¬A ∧ ¬B ⇒ ¬(A∨B).
apply rule (prove (¬A ∧ ¬B ⇒ ¬(A∨B)));
(*BEGIN*)
apply rule (⇒#i [h1] (¬(A∨B)));
apply rule (¬#i [h2] (⊥));
apply rule (∨#e (A∨B) [h3] (⊥) [h3] (⊥));
	[ apply rule (discharge [h2]);
	| apply rule (¬#e (¬A) (A));
	    [ apply rule (∧#e_l (¬A∧¬B));
        apply rule (discharge [h1]);
	    | apply rule (discharge [h3]);
	    ]
	| apply rule (¬#e (¬B) (B));
	    [ apply rule (∧#e_r (¬A∧¬B));
        apply rule (discharge [h1]);
	    | apply rule (discharge [h3]);
	    ]
	]
(*END*)
qed.

theorem ex7: ((A ⇒ ⊥) ⇒ ⊥) ⇒ A.
apply rule (prove (((A ⇒ ⊥) ⇒ ⊥) ⇒ A));
(*BEGIN*)
apply rule (⇒#i [h1] (A));
apply rule (RAA [h2] (⊥));
apply rule (⇒#e ((A⇒⊥)⇒⊥) (A⇒⊥));
	[ apply rule (discharge [h1]);
	| apply rule (⇒#i [h3] (⊥));
	  apply rule (¬#e (¬A) (A));
	    [ apply rule (discharge [h2]);
	    | apply rule (discharge [h3]);
	    ]
	]
(*END*)
qed.

