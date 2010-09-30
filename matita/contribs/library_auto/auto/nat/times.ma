(**************************************************************************)
(*       __                                                               *)
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

set "baseuri" "cic:/matita/library_autobatch/nat/times".

include "auto/nat/plus.ma".

let rec times n m \def 
 match n with 
 [ O \Rightarrow O
 | (S p) \Rightarrow m+(times p m) ].

interpretation "natural times" 'times x y = (times x y).

theorem times_n_O: \forall n:nat. O = n*O.
intros.elim n
[ autobatch
  (*simplify.
  reflexivity.*)
| simplify.  (* qui autobatch non funziona: Uncaught exception: Invalid_argument ("List.map2")*)
  assumption.
]
qed.

theorem times_n_Sm : 
\forall n,m:nat. n+(n*m) = n*(S m).
intros.elim n
[ autobatch.
  (*simplify.reflexivity.*)
| simplify.
  autobatch
  (*apply eq_f.
  rewrite < H.
  transitivity ((n1+m)+n1*m)
 [ symmetry.                    
   apply assoc_plus.            
 | transitivity ((m+n1)+n1*m)
   [ apply eq_f2.
     apply sym_plus.
     reflexivity.
   | apply assoc_plus.
   ]
 ]*)
]
qed.

(* NOTA:
   se non avessi semplificato con autobatch tutto il secondo ramo della tattica
   elim n, avrei comunque potuto risolvere direttamente con autobatch entrambi
   i rami generati dalla prima applicazione della tattica transitivity
   (precisamente transitivity ((n1+m)+n1*m)
 *)

theorem times_n_SO : \forall n:nat. n = n * S O.
intros.
rewrite < times_n_Sm.
autobatch paramodulation. (*termina la dim anche solo con autobatch*)
(*rewrite < times_n_O.
rewrite < plus_n_O.
reflexivity.*)
qed.

theorem times_SSO_n : \forall n:nat. n + n = S (S O) * n.
intros.
simplify.
autobatch paramodulation. (* termina la dim anche solo con autobatch*)
(*rewrite < plus_n_O.
reflexivity.*)
qed.

theorem symmetric_times : symmetric nat times. 
unfold symmetric.
intros.elim x
[ autobatch
  (*simplify.apply times_n_O.*)
| simplify.
  autobatch
  (*rewrite > H.apply times_n_Sm.*)
]
qed.

variant sym_times : \forall n,m:nat. n*m = m*n \def
symmetric_times.

theorem distributive_times_plus : distributive nat times plus.
unfold distributive.
intros.elim x;simplify
[ reflexivity.
| autobatch
  (*rewrite > H.
  rewrite > assoc_plus.
  rewrite > assoc_plus.
  apply eq_f.
  rewrite < assoc_plus. 
  rewrite < (sym_plus ? z).
  rewrite > assoc_plus.
  reflexivity.*)
]
qed.

variant distr_times_plus: \forall n,m,p:nat. n*(m+p) = n*m + n*p
\def distributive_times_plus.

theorem associative_times: associative nat times.
unfold associative.intros.
elim x;simplify
[ apply refl_eq
| autobatch
  (*rewrite < sym_times.
  rewrite > distr_times_plus.
  rewrite < sym_times.
  rewrite < (sym_times (times n y) z).
  rewrite < H.
  apply refl_eq.*)
]
qed.

variant assoc_times: \forall n,m,p:nat. (n*m)*p = n*(m*p) \def
associative_times.
