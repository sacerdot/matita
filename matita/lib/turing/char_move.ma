include "turing/turing.ma".

(* 
Simboli:
0 1 *0 *1 # | ,

[lista di simboli] fa match su un simbolo qualunque nella lista
ad esempio [#|,] fa match con la gratella "#", la barra verticale "|" e la virgola ","

Convenzione variabili:
- x,y,z,D     = bit (non marcati)
- *x,*y,*z,*D = bit marcati
- c,d,e = caratteri (bit marcati e non marcati e separatori)

Convenzioni mosse:
c/D --> Q : leggo c, scrivo c, mi sposto a D e passo allo stato Q
c/d/D --> Q : leggo c, scrivo d, mi sposto a D e passo allo stato Q

*)

inductive alpha_uni : Type[0] ≝ 
| bit : bool → alpha_uni
| mark : bool → alpha_uni
| grid : alpha_uni | bar : alpha_uni | comma : alpha_uni.

inductive Qmatch : Type[0] ≝
| qm0 : Qmatch | qm1 : Qmatch | qm2 : bool → Qmatch | qm3 : bool → Qmatch
| qm4 : Qmatch | qm5 : Qmatch | qm6 : Qmatch | qm7 : Qmatch 
| qm8 : Qmatch | qm9 : Qmatch 
| qmsuccess : Qmatch | qmfailure : Qmatch | qmsink : Qmatch.

definition bool_eqb ≝ λb1,b2:bool.¬ (xorb b1 b2).

(*
==================================
MACCHINE PER SPOSTARE LA "TESTINA"
================================

Lo spostamento a sx si ottiene mediante

ls x # current y # macchina # rs
----C--->
ls x # current # y macchina # rs
----B--->
ls x # current # macchina # y rs
----B--->
ls # x current # macchina # y rs
----C--->
ls # current x # macchina # y rs


Lo spostamento a dx si ottiene mediante

ls # current x # macchina # y rs
----A--->
ls x # current # macchina # y rs
----A--->
ls x # current # macchina y # rs
----A--->
ls x # current y # macchina # rs


MACCHINA A
----------
Sposta il carattere binario su cui si trova la testina oltre il primo # alla sua sinistra.

Input:
  
  ls # cs x rs
          ^
          0

Output:
  ls x # cs rs
     ^
     4

STATO 0:
  \forall x.x/L --> 1(x)

STATO 1(x):
  \forall c != #. c/x/R --> 2(c)
  #/x/R --> 3

STATO 2(c):
  \forall d. d/c/L --> 0

STATO 3:
  \forall c. c/#/L --> 4

STATO 4:
  stato finale
*)

(* struttura generica della semantica *) 
lemma move_char_sem: ∀inc. prec inc → ∃i. ∃outc. loop i step inc = Some outc 
∧ postc outc inc. 

lemma sequential : ∀M1,M2. 

definition pre c ≝ 
  let s ≝ state c in
  let tp ≝ tape c in
  let left ≝ 
  
definition post c1 c2 ≝
  let s1 ≝ state c1 in
  let tp1 ≝ tape c1 in
  let leftt ≝ left tp1 in
  let rightt ≝ right tp1 in
  c2 = mk_config finals 
  


match s with
 [ q0 ⇒ match c with
   [ bit x ⇒ 〈q1 x,〈c,L〉〉
   | _ ⇒ 〈qsink,〈c,N〉〉 ]
 | q1 x ⇒ match c with
   [ grid ⇒ 〈q3,〈bit x,R〉〉
   | _ ⇒ 〈q2 c,〈bit x,R〉〉 ]
 | q2 d ⇒ 〈q0,〈d,L〉〉
 | q3 ⇒ 〈q4,〈grid,L〉〉
 | q4 ⇒ (* finale *) ].

(*
MACCHINA B
----------
Sposta il carattere binario su cui si trova la testina oltre il primo # alla sua destra.

Input:

  ls x cs # rs
     ^
     0

Output:
  ls cs # x rs
          ^
          4

STATO 0:
  \forall x.x/R --> 1(x)

STATO 1(x):
  \forall c != #. c/x/L --> 2(c)
  #/x/L --> 3

STATO 2(c):
  \forall d. d/c/R --> 0

STATO 3:
  \forall c. c/#/L --> 4

STATO 4:
  stato finale
*)

match s with
[ q0 ⇒ match c with
  [ bit x ⇒ 〈q1 x,〈c,R〉〉
  | _ ⇒ 〈qsink,〈c,N〉〉]
| q1 x ⇒ match c with
  [ grid ⇒ 〈q3,〈bit x,L〉〉
  | _ ⇒ 〈q2 c,〈bit x,L〉〉 ]
| q2 d ⇒ 〈q0,〈d,R〉〉
| q3 ⇒ 〈q4,〈grid,L〉〉 
| q4 ⇒ (* finale *) ].

(*
MACCHINA C
----------
Sposta il carattere binario su cui si trova la testina appena prima del primo # alla sua destra.

Input:
  ls x cs # rs
     ^
     0

Output:
  ls cs x # rs
        ^
        3

STATO 0:
  \forall x. x/R --> 1(x)

STATO 1(x):
  \forall c != #. c/x/L --> 2(c)
  #/#/L --> 3

STATO 2(c):
  \forall d. d/c/R --> 0

STATO 3:
  stato finale

*)

match s with 
[ q0 ⇒ match c with
  [ bit x ⇒ 〈q1 x,〈c,R〉〉
  | _ ⇒ 〈qsink,〈c,N〉〉 ]
| q1 x ⇒ match c with
  [ grid ⇒ 〈q3,〈grid,L〉〉
  | _ ⇒ 〈q2 c,〈bit x,L〉〉
| q2 d ⇒ 〈q0,〈c,R〉〉
| q3 ⇒ (* finale *) ].
