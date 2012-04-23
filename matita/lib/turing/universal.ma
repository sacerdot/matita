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

MACCHINA per confronto tuple:
=============================
Input:
      *               *
 ls # current # ... | input , output , D | ... # rs
    ^
    0

Output:

 ls # current # ... | input , output , D | ... # rs  (rimuove le marcature)
    ^
 SUCCESS

      *                                    *
 ls # current # ... | input , output , D | ... # rs (sposta la marcatura alla tupla successiva)
    ^
 FAILURE

STATO 0:
  #/R --> 1

STATO 1:
  \forall c != *z. c/L --> 1
  \forall x. *x/x/R --> 2(x)

STATO 2(x):
  \forall y. y/*y/R --> 2
  #/R --> 2

STATO 3(x):
  \forall y.\forall c != *y. c/R --> 3(x)
  *x/x/R --> 4
  *~x/~x/R --> 5

STATO 4:
  \forall x. x/*x/L --> 1
  ,/R --> SUCCESS
  
STATO 5:
  \forall c != |. c/R --> 5
  |/R --> 6

STATO 6:
  \forall x. x/*x/L --> 7

STATO 7:
  \forall c != #. c/L --> 7
  #/L

STATO 8:
  \forall c != #. c/L --> 8
  \forall x. *x/x/L --> 8
  #/R --> 9

STATO 9:
  \forall x. x/*x/L --> FAILURE


==============================
MACCHINA PER COPIA NUOVO STATO IN CURRENT
==============================

Input:
  
  ls # current # ... | in_state , out_state , D | ... # rs
                                  ^
                                  0

Output:
  ls # out_state # ... | in_state , out_state , D | ... # rs
                                              ^
                                              9

STATO 0:
  \forall x. x/*x/L --> 1

STATO 1:
  [01,|]/L --> 1
  #/L --> 2

STATO 2:
  [01]/L --> 2
  #/R -> 3

STATO 3:
  \forall x. x/*x/R --> 4
  #/R --> 8

STATO 4:
  [01,|#]/R --> 4
  \forall x. *x/x/R --> 5(x)

STATO 5(x):
  #/R --> 6(x)
  \forall y. y/*y/L --> 7(x)

STATO 6(x):
  \forall D. D/*D/L --> 7(x)

STATO 7(x):
  [01,|#]/l --> 7(x)
  \forall y. *y/x/R --> 3

STATO 8:
  [01,|#]/R --> 8
  \forall D. *D/D/L --> 9

STATO 9:
  stato finale


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
