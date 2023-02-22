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

include "didactic/support/natural_deduction.ma".

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

theorem ex0 : (F∧¬G ⇒ L ⇒ E) ⇒ (G ∧ L ⇒ E) ⇒ F ∧ L ⇒ E.
apply rule (prove ((F∧¬G ⇒ L ⇒ E) ⇒ (G ∧ L ⇒ E) ⇒ F ∧ L ⇒ E));
(*BEGIN*)
apply rule (⇒#i [h1] ((G ∧ L ⇒ E) ⇒ F ∧ L ⇒ E));
apply rule (⇒#i [h2] (F ∧ L ⇒ E));
apply rule (⇒#i [h3] (E));
apply rule (∨#e (G∨¬G) [h4] (E) [h4] (E));
	[ apply rule (lem 0 EM);
	| apply rule (⇒#e (G∧L⇒E) (G∧L));
	    [ apply rule (discharge [h2]);
	    | apply rule (∧#i (G) (L));
	        [ apply rule (discharge [h4]);
	        | apply rule (∧#e_r (F∧L));
	          apply rule (discharge [h3]);
	        ]
	    ]
	| apply rule (⇒#e (L⇒E) (L));
	    [ apply rule (⇒#e (F∧¬G ⇒ L ⇒ E) (F∧¬G));
	        [ apply rule (discharge [h1]);
	        | apply rule (∧#i (F) (¬G));
	            [ apply rule (∧#e_l (F∧L));
	              apply rule (discharge [h3]);
	            | apply rule (discharge [h4]);
	            ]
	        ]  
	    | apply rule (∧#e_r (F∧L));
	      apply rule (discharge [h3]);
	    ]
	]
(*END*)
qed.

theorem ex1 : (F ⇒ G∨E) ⇒ (G ⇒ ¬ (L ∧ ¬E)) ⇒ (¬L ∨ F) ⇒ L ⇒ E.
apply rule (prove (F ⇒ G∨E) ⇒ (G ⇒ ¬ (L ∧ ¬E)) ⇒ (¬L ∨ F) ⇒ L ⇒ E);
(*BEGIN*)
apply rule (⇒#i [h1] ((G ⇒ ¬ (L ∧ ¬E)) ⇒ (¬L ∨ F) ⇒ L ⇒ E));
apply rule (⇒#i [h2] ((¬L ∨ F) ⇒ L ⇒ E));
apply rule (⇒#i [h3] (L ⇒ E));
apply rule (⇒#i [h4] (E));
apply rule (∨#e (¬L∨F) [h5] (E) [h5] (E));
	[ apply rule (discharge [h3]);
	| apply rule (⊥#e (⊥));
    apply rule (¬#e (¬L) (L));
	    [ apply rule (discharge [h5]);
	    | apply rule (discharge [h4]);
	    ]
	| apply rule (∨#e (G∨E) [h6] (E) [h6] (E));
	   [ apply rule (⇒#e (F⇒G∨E) (F));
	      [ apply rule (discharge [h1]);
	      | apply rule (discharge [h5]);
	      ]
	   | apply rule (RAA [h7] (⊥));
       apply rule (¬#e (¬ (L ∧ ¬E)) (L ∧ ¬E));
	       [ apply rule (⇒#e (G ⇒ ¬ (L ∧ ¬E)) (G));
	           [apply rule (discharge [h2]);
	           |apply rule (discharge [h6]);
	           ]
	       | apply rule (∧#i (L) (¬E));
	           [ apply rule (discharge [h4]);
	           | apply rule (discharge [h7]);
	           ]
	       ]
	   | apply rule (discharge [h6]);
	   ]
	]
(*END*)
qed.

theorem ex2 : (F∧G ⇒ E) ⇒ (H ⇒ E∨F) ⇒ (¬G ⇒ ¬H) ⇒ H ⇒ E.
apply rule (prove ((F∧G ⇒ E) ⇒ (H ⇒ E∨F) ⇒ (¬G ⇒ ¬H) ⇒ H ⇒ E));
(*BEGIN*)
apply rule (⇒#i [h1] ((H ⇒ E∨F) ⇒ (¬G ⇒ ¬H) ⇒ H ⇒ E));
apply rule (⇒#i [h2] ((¬G ⇒ ¬H) ⇒ H ⇒ E));
apply rule (⇒#i [h3] (H ⇒ E));
apply rule (⇒#i [h4] (E));
apply rule (∨#e (G∨¬G) [h5] (E) [h5] (E));
	[apply rule (lem 0 EM);
	| apply rule (∨#e (E∨F) [h6] (E) [h6] (E));
	   [ apply rule (⇒#e (H ⇒ E∨F) (H));
	       [ apply rule (discharge [h2]);
	       | apply rule (discharge [h4]);
	       ]
	   | apply rule (discharge [h6]);
	   | apply rule (⇒#e (F∧G ⇒ E) (F∧G));
	      [apply rule (discharge [h1]);
	      |apply rule (∧#i (F) (G));
	        [ apply rule (discharge [h6]);
	        | apply rule (discharge [h5]);
	        ]
	      ]
	   ]
	| apply rule (⊥#e (⊥));
    apply rule (¬#e (¬H) (H));
    	[ apply rule (⇒#e (¬G ⇒ ¬H) (¬G));
	       [ apply rule (discharge [h3]);
	       | apply rule (discharge [h5]);
	       ]
	    | apply rule (discharge [h4]);
	    ]
	]
(*END*)
qed.

theorem ex3 : (F∧G ⇒ E) ⇒ (¬E ⇒ G∨¬L) ⇒ (L ⇒ F) ⇒ L ⇒ E.
apply rule (prove ((F∧G ⇒ E) ⇒ (¬E ⇒ G∨¬L) ⇒ (L ⇒ F) ⇒ L ⇒ E)).
(*BEGIN*)
apply rule (⇒#i [h1] ((¬E ⇒ G∨¬L) ⇒ (L ⇒ F) ⇒ L ⇒ E));
apply rule (⇒#i [h2] ((L ⇒ F) ⇒ L ⇒ E));
apply rule (⇒#i [h3] (L ⇒ E));
apply rule (⇒#i [h4] (E));
apply rule (RAA [h5] (⊥));
apply rule (∨#e (G∨¬L) [h6] (⊥) [h6] (⊥));
	[ apply rule (⇒#e (¬E ⇒ G∨¬L) (¬E));
	    [ apply rule (discharge [h2]);
	    | apply rule (discharge [h5]);
	    ]
	| apply rule (¬#e (¬E) (E));
    	[ apply rule (discharge [h5]);
	    | apply rule (⇒#e (F∧G ⇒ E) (F∧G));
	       [ apply rule (discharge [h1]);
	       | apply rule (∧#i (F) (G));
	           [ apply rule (⇒#e (L⇒F) (L));
	              [ apply rule (discharge [h3]);
	              | apply rule (discharge [h4]);
	              ]
	           | apply rule (discharge [h6]);
	           ]
	       ]
	    ]
	| apply rule (¬#e (¬L) (L));
	    [ apply rule (discharge [h6]);
	    | apply rule (discharge [h4]);
	    ]
	]
(*END*)
qed.
