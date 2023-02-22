
include "logic/equality.ma".

theorem an_1:
∀ Univ:Set.
∀ a:Univ.
∀ is_a_theorem:Univ → Prop.
∀ not:Univ → Univ.
∀ or:Univ → Univ → Univ.
∀ H0:∀ U:Univ.∀ V:Univ.∀ X:Univ.∀ Y:Univ.∀ Z:Univ.
  is_a_theorem 
    (or (not (or (not (or (not X) Y)) (or Z (or U V)))) 
        (or (not (or (not U) X)) (or Z (or V X)))).
∀ H1:∀ X:Univ.∀ Y:Univ.
  is_a_theorem (or (not X) Y) → is_a_theorem X → is_a_theorem Y.
∀ ABS:∀ X.is_a_theorem X.
True.
.
intros 5.
intros (H H1 ABS).

(* H1 o H *)
compose (H) with (H1) (primo secondo).
letin verifica_primo ≝ (primo ? ? ? ? ? ? = H1 ? ? ? (H ? ? ? ? ?)); 
try assumption; [1,2: apply ABS]
letin verifica_secondo ≝ (secondo ? ? ? ? ? ? ? = H1 ? ? (H ? ? ? ? ?) ?);
try assumption; [1,2: apply ABS]
clear verifica_primo verifica_secondo.
compose (H) with (primo) (terzo).
compose (H) with (secondo) (quarto).
letin verifica_terzo_quarto ≝ (terzo ? ? ? ? ? = quarto ? ? ? ? ?);
try assumption.
clear verifica_terzo_quarto.
clear primo secondo terzo quarto.

(* H1 o H1 *)
compose (H1) with (H1) (primo secondo).
letin verifica_primo ≝ (primo ? ? ? ? ? ? = H1 ? ? ? (H1 ? ? ? ?));
try assumption; [1,2,3,4,5,6: apply ABS]
letin verifica_secondo ≝ (secondo ? ? ? ? ? ? = H1 ? ? (H1 ? ? ? ?) ?);
try assumption; [1,2,3,4,5,6: apply ABS]
clear verifica_primo verifica_secondo.
clear primo secondo.

(* close H1 o H1 with H *)
compose H1 with H1 0. 
(* 
leaving the result under the sequent line and calling compose without 
the with parameter, will compose H with all the stuff under the sequent line
*)
compose 3 (H) (i1 i2 p1 p2 p3 p4 p5 p6 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12).
exact I.
qed.
