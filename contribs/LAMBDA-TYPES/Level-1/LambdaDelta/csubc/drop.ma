(**************************************************************************)
(*       ___                                                              *)
(*      ||M||                                                             *)
(*      ||A||       A project by Andrea Asperti                           *)
(*      ||T||                                                             *)
(*      ||I||       Developers:                                           *)
(*      ||T||         The HELM team.                                      *)
(*      ||A||         http://helm.cs.unibo.it                             *)
(*      \   /                                                             *)
(*       \ /        This file is distributed under the terms of the       *)
(*        v         GNU General Public License Version 2                  *)
(*                                                                        *)
(**************************************************************************)

(* This file was automatically generated: do not edit *********************)

set "baseuri" "cic:/matita/LAMBDA-TYPES/LambdaDelta-1/csubc/drop".

include "csubc/defs.ma".

include "sc3/props.ma".

theorem csubc_drop_conf_O:
 \forall (g: G).(\forall (c1: C).(\forall (e1: C).(\forall (h: nat).((drop h 
O c1 e1) \to (\forall (c2: C).((csubc g c1 c2) \to (ex2 C (\lambda (e2: 
C).(drop h O c2 e2)) (\lambda (e2: C).(csubc g e1 e2)))))))))
\def
 \lambda (g: G).(\lambda (c1: C).(C_ind (\lambda (c: C).(\forall (e1: 
C).(\forall (h: nat).((drop h O c e1) \to (\forall (c2: C).((csubc g c c2) 
\to (ex2 C (\lambda (e2: C).(drop h O c2 e2)) (\lambda (e2: C).(csubc g e1 
e2))))))))) (\lambda (n: nat).(\lambda (e1: C).(\lambda (h: nat).(\lambda (H: 
(drop h O (CSort n) e1)).(\lambda (c2: C).(\lambda (H0: (csubc g (CSort n) 
c2)).(and3_ind (eq C e1 (CSort n)) (eq nat h O) (eq nat O O) (ex2 C (\lambda 
(e2: C).(drop h O c2 e2)) (\lambda (e2: C).(csubc g e1 e2))) (\lambda (H1: 
(eq C e1 (CSort n))).(\lambda (H2: (eq nat h O)).(\lambda (_: (eq nat O 
O)).(eq_ind_r nat O (\lambda (n0: nat).(ex2 C (\lambda (e2: C).(drop n0 O c2 
e2)) (\lambda (e2: C).(csubc g e1 e2)))) (eq_ind_r C (CSort n) (\lambda (c: 
C).(ex2 C (\lambda (e2: C).(drop O O c2 e2)) (\lambda (e2: C).(csubc g c 
e2)))) (ex_intro2 C (\lambda (e2: C).(drop O O c2 e2)) (\lambda (e2: 
C).(csubc g (CSort n) e2)) c2 (drop_refl c2) H0) e1 H1) h H2)))) 
(drop_gen_sort n h O e1 H)))))))) (\lambda (c: C).(\lambda (H: ((\forall (e1: 
C).(\forall (h: nat).((drop h O c e1) \to (\forall (c2: C).((csubc g c c2) 
\to (ex2 C (\lambda (e2: C).(drop h O c2 e2)) (\lambda (e2: C).(csubc g e1 
e2)))))))))).(\lambda (k: K).(\lambda (t: T).(\lambda (e1: C).(\lambda (h: 
nat).(nat_ind (\lambda (n: nat).((drop n O (CHead c k t) e1) \to (\forall 
(c2: C).((csubc g (CHead c k t) c2) \to (ex2 C (\lambda (e2: C).(drop n O c2 
e2)) (\lambda (e2: C).(csubc g e1 e2))))))) (\lambda (H0: (drop O O (CHead c 
k t) e1)).(\lambda (c2: C).(\lambda (H1: (csubc g (CHead c k t) c2)).(eq_ind 
C (CHead c k t) (\lambda (c0: C).(ex2 C (\lambda (e2: C).(drop O O c2 e2)) 
(\lambda (e2: C).(csubc g c0 e2)))) (ex_intro2 C (\lambda (e2: C).(drop O O 
c2 e2)) (\lambda (e2: C).(csubc g (CHead c k t) e2)) c2 (drop_refl c2) H1) e1 
(drop_gen_refl (CHead c k t) e1 H0))))) (\lambda (n: nat).(\lambda (H0: 
(((drop n O (CHead c k t) e1) \to (\forall (c2: C).((csubc g (CHead c k t) 
c2) \to (ex2 C (\lambda (e2: C).(drop n O c2 e2)) (\lambda (e2: C).(csubc g 
e1 e2)))))))).(\lambda (H1: (drop (S n) O (CHead c k t) e1)).(\lambda (c2: 
C).(\lambda (H2: (csubc g (CHead c k t) c2)).(let H3 \def (match H2 in csubc 
return (\lambda (c0: C).(\lambda (c3: C).(\lambda (_: (csubc ? c0 c3)).((eq C 
c0 (CHead c k t)) \to ((eq C c3 c2) \to (ex2 C (\lambda (e2: C).(drop (S n) O 
c2 e2)) (\lambda (e2: C).(csubc g e1 e2)))))))) with [(csubc_sort n0) 
\Rightarrow (\lambda (H3: (eq C (CSort n0) (CHead c k t))).(\lambda (H4: (eq 
C (CSort n0) c2)).((let H5 \def (eq_ind C (CSort n0) (\lambda (e: C).(match e 
in C return (\lambda (_: C).Prop) with [(CSort _) \Rightarrow True | (CHead _ 
_ _) \Rightarrow False])) I (CHead c k t) H3) in (False_ind ((eq C (CSort n0) 
c2) \to (ex2 C (\lambda (e2: C).(drop (S n) O c2 e2)) (\lambda (e2: C).(csubc 
g e1 e2)))) H5)) H4))) | (csubc_head c0 c3 H3 k0 v) \Rightarrow (\lambda (H4: 
(eq C (CHead c0 k0 v) (CHead c k t))).(\lambda (H5: (eq C (CHead c3 k0 v) 
c2)).((let H6 \def (f_equal C T (\lambda (e: C).(match e in C return (\lambda 
(_: C).T) with [(CSort _) \Rightarrow v | (CHead _ _ t0) \Rightarrow t0])) 
(CHead c0 k0 v) (CHead c k t) H4) in ((let H7 \def (f_equal C K (\lambda (e: 
C).(match e in C return (\lambda (_: C).K) with [(CSort _) \Rightarrow k0 | 
(CHead _ k1 _) \Rightarrow k1])) (CHead c0 k0 v) (CHead c k t) H4) in ((let 
H8 \def (f_equal C C (\lambda (e: C).(match e in C return (\lambda (_: C).C) 
with [(CSort _) \Rightarrow c0 | (CHead c4 _ _) \Rightarrow c4])) (CHead c0 
k0 v) (CHead c k t) H4) in (eq_ind C c (\lambda (c4: C).((eq K k0 k) \to ((eq 
T v t) \to ((eq C (CHead c3 k0 v) c2) \to ((csubc g c4 c3) \to (ex2 C 
(\lambda (e2: C).(drop (S n) O c2 e2)) (\lambda (e2: C).(csubc g e1 
e2)))))))) (\lambda (H9: (eq K k0 k)).(eq_ind K k (\lambda (k1: K).((eq T v 
t) \to ((eq C (CHead c3 k1 v) c2) \to ((csubc g c c3) \to (ex2 C (\lambda 
(e2: C).(drop (S n) O c2 e2)) (\lambda (e2: C).(csubc g e1 e2))))))) (\lambda 
(H10: (eq T v t)).(eq_ind T t (\lambda (t0: T).((eq C (CHead c3 k t0) c2) \to 
((csubc g c c3) \to (ex2 C (\lambda (e2: C).(drop (S n) O c2 e2)) (\lambda 
(e2: C).(csubc g e1 e2)))))) (\lambda (H11: (eq C (CHead c3 k t) c2)).(eq_ind 
C (CHead c3 k t) (\lambda (c4: C).((csubc g c c3) \to (ex2 C (\lambda (e2: 
C).(drop (S n) O c4 e2)) (\lambda (e2: C).(csubc g e1 e2))))) (\lambda (H12: 
(csubc g c c3)).(let H_x \def (H e1 (r k n) (drop_gen_drop k c e1 t n H1) c3 
H12) in (let H13 \def H_x in (ex2_ind C (\lambda (e2: C).(drop (r k n) O c3 
e2)) (\lambda (e2: C).(csubc g e1 e2)) (ex2 C (\lambda (e2: C).(drop (S n) O 
(CHead c3 k t) e2)) (\lambda (e2: C).(csubc g e1 e2))) (\lambda (x: 
C).(\lambda (H14: (drop (r k n) O c3 x)).(\lambda (H15: (csubc g e1 
x)).(ex_intro2 C (\lambda (e2: C).(drop (S n) O (CHead c3 k t) e2)) (\lambda 
(e2: C).(csubc g e1 e2)) x (drop_drop k n c3 x H14 t) H15)))) H13)))) c2 
H11)) v (sym_eq T v t H10))) k0 (sym_eq K k0 k H9))) c0 (sym_eq C c0 c H8))) 
H7)) H6)) H5 H3))) | (csubc_abst c0 c3 H3 v a H4 w H5) \Rightarrow (\lambda 
(H6: (eq C (CHead c0 (Bind Abst) v) (CHead c k t))).(\lambda (H7: (eq C 
(CHead c3 (Bind Abbr) w) c2)).((let H8 \def (f_equal C T (\lambda (e: 
C).(match e in C return (\lambda (_: C).T) with [(CSort _) \Rightarrow v | 
(CHead _ _ t0) \Rightarrow t0])) (CHead c0 (Bind Abst) v) (CHead c k t) H6) 
in ((let H9 \def (f_equal C K (\lambda (e: C).(match e in C return (\lambda 
(_: C).K) with [(CSort _) \Rightarrow (Bind Abst) | (CHead _ k0 _) 
\Rightarrow k0])) (CHead c0 (Bind Abst) v) (CHead c k t) H6) in ((let H10 
\def (f_equal C C (\lambda (e: C).(match e in C return (\lambda (_: C).C) 
with [(CSort _) \Rightarrow c0 | (CHead c4 _ _) \Rightarrow c4])) (CHead c0 
(Bind Abst) v) (CHead c k t) H6) in (eq_ind C c (\lambda (c4: C).((eq K (Bind 
Abst) k) \to ((eq T v t) \to ((eq C (CHead c3 (Bind Abbr) w) c2) \to ((csubc 
g c4 c3) \to ((sc3 g (asucc g a) c4 v) \to ((sc3 g a c3 w) \to (ex2 C 
(\lambda (e2: C).(drop (S n) O c2 e2)) (\lambda (e2: C).(csubc g e1 
e2)))))))))) (\lambda (H11: (eq K (Bind Abst) k)).(eq_ind K (Bind Abst) 
(\lambda (_: K).((eq T v t) \to ((eq C (CHead c3 (Bind Abbr) w) c2) \to 
((csubc g c c3) \to ((sc3 g (asucc g a) c v) \to ((sc3 g a c3 w) \to (ex2 C 
(\lambda (e2: C).(drop (S n) O c2 e2)) (\lambda (e2: C).(csubc g e1 
e2))))))))) (\lambda (H12: (eq T v t)).(eq_ind T t (\lambda (t0: T).((eq C 
(CHead c3 (Bind Abbr) w) c2) \to ((csubc g c c3) \to ((sc3 g (asucc g a) c 
t0) \to ((sc3 g a c3 w) \to (ex2 C (\lambda (e2: C).(drop (S n) O c2 e2)) 
(\lambda (e2: C).(csubc g e1 e2)))))))) (\lambda (H13: (eq C (CHead c3 (Bind 
Abbr) w) c2)).(eq_ind C (CHead c3 (Bind Abbr) w) (\lambda (c4: C).((csubc g c 
c3) \to ((sc3 g (asucc g a) c t) \to ((sc3 g a c3 w) \to (ex2 C (\lambda (e2: 
C).(drop (S n) O c4 e2)) (\lambda (e2: C).(csubc g e1 e2))))))) (\lambda 
(H14: (csubc g c c3)).(\lambda (_: (sc3 g (asucc g a) c t)).(\lambda (_: (sc3 
g a c3 w)).(let H17 \def (eq_ind_r K k (\lambda (k0: K).(drop (r k0 n) O c 
e1)) (drop_gen_drop k c e1 t n H1) (Bind Abst) H11) in (let H18 \def 
(eq_ind_r K k (\lambda (k0: K).((drop n O (CHead c k0 t) e1) \to (\forall 
(c4: C).((csubc g (CHead c k0 t) c4) \to (ex2 C (\lambda (e2: C).(drop n O c4 
e2)) (\lambda (e2: C).(csubc g e1 e2))))))) H0 (Bind Abst) H11) in (let H_x 
\def (H e1 (r (Bind Abst) n) H17 c3 H14) in (let H19 \def H_x in (ex2_ind C 
(\lambda (e2: C).(drop (r (Bind Abst) n) O c3 e2)) (\lambda (e2: C).(csubc g 
e1 e2)) (ex2 C (\lambda (e2: C).(drop (S n) O (CHead c3 (Bind Abbr) w) e2)) 
(\lambda (e2: C).(csubc g e1 e2))) (\lambda (x: C).(\lambda (H20: (drop (r 
(Bind Abst) n) O c3 x)).(\lambda (H21: (csubc g e1 x)).(ex_intro2 C (\lambda 
(e2: C).(drop (S n) O (CHead c3 (Bind Abbr) w) e2)) (\lambda (e2: C).(csubc g 
e1 e2)) x (drop_drop (Bind Abbr) n c3 x H20 w) H21)))) H19)))))))) c2 H13)) v 
(sym_eq T v t H12))) k H11)) c0 (sym_eq C c0 c H10))) H9)) H8)) H7 H3 H4 
H5)))]) in (H3 (refl_equal C (CHead c k t)) (refl_equal C c2)))))))) h))))))) 
c1)).

theorem drop_csubc_trans:
 \forall (g: G).(\forall (c2: C).(\forall (e2: C).(\forall (d: nat).(\forall 
(h: nat).((drop h d c2 e2) \to (\forall (e1: C).((csubc g e2 e1) \to (ex2 C 
(\lambda (c1: C).(drop h d c1 e1)) (\lambda (c1: C).(csubc g c2 c1))))))))))
\def
 \lambda (g: G).(\lambda (c2: C).(C_ind (\lambda (c: C).(\forall (e2: 
C).(\forall (d: nat).(\forall (h: nat).((drop h d c e2) \to (\forall (e1: 
C).((csubc g e2 e1) \to (ex2 C (\lambda (c1: C).(drop h d c1 e1)) (\lambda 
(c1: C).(csubc g c c1)))))))))) (\lambda (n: nat).(\lambda (e2: C).(\lambda 
(d: nat).(\lambda (h: nat).(\lambda (H: (drop h d (CSort n) e2)).(\lambda 
(e1: C).(\lambda (H0: (csubc g e2 e1)).(and3_ind (eq C e2 (CSort n)) (eq nat 
h O) (eq nat d O) (ex2 C (\lambda (c1: C).(drop h d c1 e1)) (\lambda (c1: 
C).(csubc g (CSort n) c1))) (\lambda (H1: (eq C e2 (CSort n))).(\lambda (H2: 
(eq nat h O)).(\lambda (H3: (eq nat d O)).(eq_ind_r nat O (\lambda (n0: 
nat).(ex2 C (\lambda (c1: C).(drop n0 d c1 e1)) (\lambda (c1: C).(csubc g 
(CSort n) c1)))) (eq_ind_r nat O (\lambda (n0: nat).(ex2 C (\lambda (c1: 
C).(drop O n0 c1 e1)) (\lambda (c1: C).(csubc g (CSort n) c1)))) (let H4 \def 
(eq_ind C e2 (\lambda (c: C).(csubc g c e1)) H0 (CSort n) H1) in (ex_intro2 C 
(\lambda (c1: C).(drop O O c1 e1)) (\lambda (c1: C).(csubc g (CSort n) c1)) 
e1 (drop_refl e1) H4)) d H3) h H2)))) (drop_gen_sort n h d e2 H))))))))) 
(\lambda (c: C).(\lambda (H: ((\forall (e2: C).(\forall (d: nat).(\forall (h: 
nat).((drop h d c e2) \to (\forall (e1: C).((csubc g e2 e1) \to (ex2 C 
(\lambda (c1: C).(drop h d c1 e1)) (\lambda (c1: C).(csubc g c 
c1))))))))))).(\lambda (k: K).(\lambda (t: T).(\lambda (e2: C).(\lambda (d: 
nat).(nat_ind (\lambda (n: nat).(\forall (h: nat).((drop h n (CHead c k t) 
e2) \to (\forall (e1: C).((csubc g e2 e1) \to (ex2 C (\lambda (c1: C).(drop h 
n c1 e1)) (\lambda (c1: C).(csubc g (CHead c k t) c1)))))))) (\lambda (h: 
nat).(nat_ind (\lambda (n: nat).((drop n O (CHead c k t) e2) \to (\forall 
(e1: C).((csubc g e2 e1) \to (ex2 C (\lambda (c1: C).(drop n O c1 e1)) 
(\lambda (c1: C).(csubc g (CHead c k t) c1))))))) (\lambda (H0: (drop O O 
(CHead c k t) e2)).(\lambda (e1: C).(\lambda (H1: (csubc g e2 e1)).(let H2 
\def (eq_ind_r C e2 (\lambda (c0: C).(csubc g c0 e1)) H1 (CHead c k t) 
(drop_gen_refl (CHead c k t) e2 H0)) in (ex_intro2 C (\lambda (c1: C).(drop O 
O c1 e1)) (\lambda (c1: C).(csubc g (CHead c k t) c1)) e1 (drop_refl e1) 
H2))))) (\lambda (n: nat).(\lambda (_: (((drop n O (CHead c k t) e2) \to 
(\forall (e1: C).((csubc g e2 e1) \to (ex2 C (\lambda (c1: C).(drop n O c1 
e1)) (\lambda (c1: C).(csubc g (CHead c k t) c1)))))))).(\lambda (H1: (drop 
(S n) O (CHead c k t) e2)).(\lambda (e1: C).(\lambda (H2: (csubc g e2 
e1)).(let H_x \def (H e2 O (r k n) (drop_gen_drop k c e2 t n H1) e1 H2) in 
(let H3 \def H_x in (ex2_ind C (\lambda (c1: C).(drop (r k n) O c1 e1)) 
(\lambda (c1: C).(csubc g c c1)) (ex2 C (\lambda (c1: C).(drop (S n) O c1 
e1)) (\lambda (c1: C).(csubc g (CHead c k t) c1))) (\lambda (x: C).(\lambda 
(H4: (drop (r k n) O x e1)).(\lambda (H5: (csubc g c x)).(ex_intro2 C 
(\lambda (c1: C).(drop (S n) O c1 e1)) (\lambda (c1: C).(csubc g (CHead c k 
t) c1)) (CHead x k t) (drop_drop k n x e1 H4 t) (csubc_head g c x H5 k t))))) 
H3)))))))) h)) (\lambda (n: nat).(\lambda (H0: ((\forall (h: nat).((drop h n 
(CHead c k t) e2) \to (\forall (e1: C).((csubc g e2 e1) \to (ex2 C (\lambda 
(c1: C).(drop h n c1 e1)) (\lambda (c1: C).(csubc g (CHead c k t) 
c1))))))))).(\lambda (h: nat).(\lambda (H1: (drop h (S n) (CHead c k t) 
e2)).(\lambda (e1: C).(\lambda (H2: (csubc g e2 e1)).(ex3_2_ind C T (\lambda 
(e: C).(\lambda (v: T).(eq C e2 (CHead e k v)))) (\lambda (_: C).(\lambda (v: 
T).(eq T t (lift h (r k n) v)))) (\lambda (e: C).(\lambda (_: T).(drop h (r k 
n) c e))) (ex2 C (\lambda (c1: C).(drop h (S n) c1 e1)) (\lambda (c1: 
C).(csubc g (CHead c k t) c1))) (\lambda (x0: C).(\lambda (x1: T).(\lambda 
(H3: (eq C e2 (CHead x0 k x1))).(\lambda (H4: (eq T t (lift h (r k n) 
x1))).(\lambda (H5: (drop h (r k n) c x0)).(let H6 \def (eq_ind C e2 (\lambda 
(c0: C).(csubc g c0 e1)) H2 (CHead x0 k x1) H3) in (let H7 \def (eq_ind C e2 
(\lambda (c0: C).(\forall (h0: nat).((drop h0 n (CHead c k t) c0) \to 
(\forall (e3: C).((csubc g c0 e3) \to (ex2 C (\lambda (c1: C).(drop h0 n c1 
e3)) (\lambda (c1: C).(csubc g (CHead c k t) c1)))))))) H0 (CHead x0 k x1) 
H3) in (let H8 \def (eq_ind T t (\lambda (t0: T).(\forall (h0: nat).((drop h0 
n (CHead c k t0) (CHead x0 k x1)) \to (\forall (e3: C).((csubc g (CHead x0 k 
x1) e3) \to (ex2 C (\lambda (c1: C).(drop h0 n c1 e3)) (\lambda (c1: 
C).(csubc g (CHead c k t0) c1)))))))) H7 (lift h (r k n) x1) H4) in (eq_ind_r 
T (lift h (r k n) x1) (\lambda (t0: T).(ex2 C (\lambda (c1: C).(drop h (S n) 
c1 e1)) (\lambda (c1: C).(csubc g (CHead c k t0) c1)))) (let H9 \def (match 
H6 in csubc return (\lambda (c0: C).(\lambda (c1: C).(\lambda (_: (csubc ? c0 
c1)).((eq C c0 (CHead x0 k x1)) \to ((eq C c1 e1) \to (ex2 C (\lambda (c3: 
C).(drop h (S n) c3 e1)) (\lambda (c3: C).(csubc g (CHead c k (lift h (r k n) 
x1)) c3)))))))) with [(csubc_sort n0) \Rightarrow (\lambda (H9: (eq C (CSort 
n0) (CHead x0 k x1))).(\lambda (H10: (eq C (CSort n0) e1)).((let H11 \def 
(eq_ind C (CSort n0) (\lambda (e: C).(match e in C return (\lambda (_: 
C).Prop) with [(CSort _) \Rightarrow True | (CHead _ _ _) \Rightarrow 
False])) I (CHead x0 k x1) H9) in (False_ind ((eq C (CSort n0) e1) \to (ex2 C 
(\lambda (c1: C).(drop h (S n) c1 e1)) (\lambda (c1: C).(csubc g (CHead c k 
(lift h (r k n) x1)) c1)))) H11)) H10))) | (csubc_head c1 c0 H9 k0 v) 
\Rightarrow (\lambda (H10: (eq C (CHead c1 k0 v) (CHead x0 k x1))).(\lambda 
(H11: (eq C (CHead c0 k0 v) e1)).((let H12 \def (f_equal C T (\lambda (e: 
C).(match e in C return (\lambda (_: C).T) with [(CSort _) \Rightarrow v | 
(CHead _ _ t0) \Rightarrow t0])) (CHead c1 k0 v) (CHead x0 k x1) H10) in 
((let H13 \def (f_equal C K (\lambda (e: C).(match e in C return (\lambda (_: 
C).K) with [(CSort _) \Rightarrow k0 | (CHead _ k1 _) \Rightarrow k1])) 
(CHead c1 k0 v) (CHead x0 k x1) H10) in ((let H14 \def (f_equal C C (\lambda 
(e: C).(match e in C return (\lambda (_: C).C) with [(CSort _) \Rightarrow c1 
| (CHead c3 _ _) \Rightarrow c3])) (CHead c1 k0 v) (CHead x0 k x1) H10) in 
(eq_ind C x0 (\lambda (c3: C).((eq K k0 k) \to ((eq T v x1) \to ((eq C (CHead 
c0 k0 v) e1) \to ((csubc g c3 c0) \to (ex2 C (\lambda (c4: C).(drop h (S n) 
c4 e1)) (\lambda (c4: C).(csubc g (CHead c k (lift h (r k n) x1)) c4)))))))) 
(\lambda (H15: (eq K k0 k)).(eq_ind K k (\lambda (k1: K).((eq T v x1) \to 
((eq C (CHead c0 k1 v) e1) \to ((csubc g x0 c0) \to (ex2 C (\lambda (c3: 
C).(drop h (S n) c3 e1)) (\lambda (c3: C).(csubc g (CHead c k (lift h (r k n) 
x1)) c3))))))) (\lambda (H16: (eq T v x1)).(eq_ind T x1 (\lambda (t0: T).((eq 
C (CHead c0 k t0) e1) \to ((csubc g x0 c0) \to (ex2 C (\lambda (c3: C).(drop 
h (S n) c3 e1)) (\lambda (c3: C).(csubc g (CHead c k (lift h (r k n) x1)) 
c3)))))) (\lambda (H17: (eq C (CHead c0 k x1) e1)).(eq_ind C (CHead c0 k x1) 
(\lambda (c3: C).((csubc g x0 c0) \to (ex2 C (\lambda (c4: C).(drop h (S n) 
c4 c3)) (\lambda (c4: C).(csubc g (CHead c k (lift h (r k n) x1)) c4))))) 
(\lambda (H18: (csubc g x0 c0)).(let H_x \def (H x0 (r k n) h H5 c0 H18) in 
(let H19 \def H_x in (ex2_ind C (\lambda (c3: C).(drop h (r k n) c3 c0)) 
(\lambda (c3: C).(csubc g c c3)) (ex2 C (\lambda (c3: C).(drop h (S n) c3 
(CHead c0 k x1))) (\lambda (c3: C).(csubc g (CHead c k (lift h (r k n) x1)) 
c3))) (\lambda (x: C).(\lambda (H20: (drop h (r k n) x c0)).(\lambda (H21: 
(csubc g c x)).(ex_intro2 C (\lambda (c3: C).(drop h (S n) c3 (CHead c0 k 
x1))) (\lambda (c3: C).(csubc g (CHead c k (lift h (r k n) x1)) c3)) (CHead x 
k (lift h (r k n) x1)) (drop_skip k h n x c0 H20 x1) (csubc_head g c x H21 k 
(lift h (r k n) x1)))))) H19)))) e1 H17)) v (sym_eq T v x1 H16))) k0 (sym_eq 
K k0 k H15))) c1 (sym_eq C c1 x0 H14))) H13)) H12)) H11 H9))) | (csubc_abst 
c1 c0 H9 v a H10 w H11) \Rightarrow (\lambda (H12: (eq C (CHead c1 (Bind 
Abst) v) (CHead x0 k x1))).(\lambda (H13: (eq C (CHead c0 (Bind Abbr) w) 
e1)).((let H14 \def (f_equal C T (\lambda (e: C).(match e in C return 
(\lambda (_: C).T) with [(CSort _) \Rightarrow v | (CHead _ _ t0) \Rightarrow 
t0])) (CHead c1 (Bind Abst) v) (CHead x0 k x1) H12) in ((let H15 \def 
(f_equal C K (\lambda (e: C).(match e in C return (\lambda (_: C).K) with 
[(CSort _) \Rightarrow (Bind Abst) | (CHead _ k0 _) \Rightarrow k0])) (CHead 
c1 (Bind Abst) v) (CHead x0 k x1) H12) in ((let H16 \def (f_equal C C 
(\lambda (e: C).(match e in C return (\lambda (_: C).C) with [(CSort _) 
\Rightarrow c1 | (CHead c3 _ _) \Rightarrow c3])) (CHead c1 (Bind Abst) v) 
(CHead x0 k x1) H12) in (eq_ind C x0 (\lambda (c3: C).((eq K (Bind Abst) k) 
\to ((eq T v x1) \to ((eq C (CHead c0 (Bind Abbr) w) e1) \to ((csubc g c3 c0) 
\to ((sc3 g (asucc g a) c3 v) \to ((sc3 g a c0 w) \to (ex2 C (\lambda (c4: 
C).(drop h (S n) c4 e1)) (\lambda (c4: C).(csubc g (CHead c k (lift h (r k n) 
x1)) c4)))))))))) (\lambda (H17: (eq K (Bind Abst) k)).(eq_ind K (Bind Abst) 
(\lambda (k0: K).((eq T v x1) \to ((eq C (CHead c0 (Bind Abbr) w) e1) \to 
((csubc g x0 c0) \to ((sc3 g (asucc g a) x0 v) \to ((sc3 g a c0 w) \to (ex2 C 
(\lambda (c3: C).(drop h (S n) c3 e1)) (\lambda (c3: C).(csubc g (CHead c k0 
(lift h (r k0 n) x1)) c3))))))))) (\lambda (H18: (eq T v x1)).(eq_ind T x1 
(\lambda (t0: T).((eq C (CHead c0 (Bind Abbr) w) e1) \to ((csubc g x0 c0) \to 
((sc3 g (asucc g a) x0 t0) \to ((sc3 g a c0 w) \to (ex2 C (\lambda (c3: 
C).(drop h (S n) c3 e1)) (\lambda (c3: C).(csubc g (CHead c (Bind Abst) (lift 
h (r (Bind Abst) n) x1)) c3)))))))) (\lambda (H19: (eq C (CHead c0 (Bind 
Abbr) w) e1)).(eq_ind C (CHead c0 (Bind Abbr) w) (\lambda (c3: C).((csubc g 
x0 c0) \to ((sc3 g (asucc g a) x0 x1) \to ((sc3 g a c0 w) \to (ex2 C (\lambda 
(c4: C).(drop h (S n) c4 c3)) (\lambda (c4: C).(csubc g (CHead c (Bind Abst) 
(lift h (r (Bind Abst) n) x1)) c4))))))) (\lambda (H20: (csubc g x0 
c0)).(\lambda (H21: (sc3 g (asucc g a) x0 x1)).(\lambda (H22: (sc3 g a c0 
w)).(let H23 \def (eq_ind_r K k (\lambda (k0: K).(\forall (h0: nat).((drop h0 
n (CHead c k0 (lift h (r k0 n) x1)) (CHead x0 k0 x1)) \to (\forall (e3: 
C).((csubc g (CHead x0 k0 x1) e3) \to (ex2 C (\lambda (c3: C).(drop h0 n c3 
e3)) (\lambda (c3: C).(csubc g (CHead c k0 (lift h (r k0 n) x1)) c3)))))))) 
H8 (Bind Abst) H17) in (let H24 \def (eq_ind_r K k (\lambda (k0: K).(drop h 
(r k0 n) c x0)) H5 (Bind Abst) H17) in (let H_x \def (H x0 (r (Bind Abst) n) 
h H24 c0 H20) in (let H25 \def H_x in (ex2_ind C (\lambda (c3: C).(drop h (r 
(Bind Abst) n) c3 c0)) (\lambda (c3: C).(csubc g c c3)) (ex2 C (\lambda (c3: 
C).(drop h (S n) c3 (CHead c0 (Bind Abbr) w))) (\lambda (c3: C).(csubc g 
(CHead c (Bind Abst) (lift h (r (Bind Abst) n) x1)) c3))) (\lambda (x: 
C).(\lambda (H26: (drop h (r (Bind Abst) n) x c0)).(\lambda (H27: (csubc g c 
x)).(ex_intro2 C (\lambda (c3: C).(drop h (S n) c3 (CHead c0 (Bind Abbr) w))) 
(\lambda (c3: C).(csubc g (CHead c (Bind Abst) (lift h (r (Bind Abst) n) x1)) 
c3)) (CHead x (Bind Abbr) (lift h n w)) (drop_skip_bind h n x c0 H26 Abbr w) 
(csubc_abst g c x H27 (lift h (r (Bind Abst) n) x1) a (sc3_lift g (asucc g a) 
x0 x1 H21 c h (r (Bind Abst) n) H24) (lift h n w) (sc3_lift g a c0 w H22 x h 
n H26)))))) H25)))))))) e1 H19)) v (sym_eq T v x1 H18))) k H17)) c1 (sym_eq C 
c1 x0 H16))) H15)) H14)) H13 H9 H10 H11)))]) in (H9 (refl_equal C (CHead x0 k 
x1)) (refl_equal C e1))) t H4))))))))) (drop_gen_skip_l c e2 t h n k 
H1)))))))) d))))))) c2)).

theorem csubc_drop_conf_rev:
 \forall (g: G).(\forall (c2: C).(\forall (e2: C).(\forall (d: nat).(\forall 
(h: nat).((drop h d c2 e2) \to (\forall (e1: C).((csubc g e1 e2) \to (ex2 C 
(\lambda (c1: C).(drop h d c1 e1)) (\lambda (c1: C).(csubc g c1 c2))))))))))
\def
 \lambda (g: G).(\lambda (c2: C).(C_ind (\lambda (c: C).(\forall (e2: 
C).(\forall (d: nat).(\forall (h: nat).((drop h d c e2) \to (\forall (e1: 
C).((csubc g e1 e2) \to (ex2 C (\lambda (c1: C).(drop h d c1 e1)) (\lambda 
(c1: C).(csubc g c1 c)))))))))) (\lambda (n: nat).(\lambda (e2: C).(\lambda 
(d: nat).(\lambda (h: nat).(\lambda (H: (drop h d (CSort n) e2)).(\lambda 
(e1: C).(\lambda (H0: (csubc g e1 e2)).(and3_ind (eq C e2 (CSort n)) (eq nat 
h O) (eq nat d O) (ex2 C (\lambda (c1: C).(drop h d c1 e1)) (\lambda (c1: 
C).(csubc g c1 (CSort n)))) (\lambda (H1: (eq C e2 (CSort n))).(\lambda (H2: 
(eq nat h O)).(\lambda (H3: (eq nat d O)).(eq_ind_r nat O (\lambda (n0: 
nat).(ex2 C (\lambda (c1: C).(drop n0 d c1 e1)) (\lambda (c1: C).(csubc g c1 
(CSort n))))) (eq_ind_r nat O (\lambda (n0: nat).(ex2 C (\lambda (c1: 
C).(drop O n0 c1 e1)) (\lambda (c1: C).(csubc g c1 (CSort n))))) (let H4 \def 
(eq_ind C e2 (\lambda (c: C).(csubc g e1 c)) H0 (CSort n) H1) in (ex_intro2 C 
(\lambda (c1: C).(drop O O c1 e1)) (\lambda (c1: C).(csubc g c1 (CSort n))) 
e1 (drop_refl e1) H4)) d H3) h H2)))) (drop_gen_sort n h d e2 H))))))))) 
(\lambda (c: C).(\lambda (H: ((\forall (e2: C).(\forall (d: nat).(\forall (h: 
nat).((drop h d c e2) \to (\forall (e1: C).((csubc g e1 e2) \to (ex2 C 
(\lambda (c1: C).(drop h d c1 e1)) (\lambda (c1: C).(csubc g c1 
c))))))))))).(\lambda (k: K).(\lambda (t: T).(\lambda (e2: C).(\lambda (d: 
nat).(nat_ind (\lambda (n: nat).(\forall (h: nat).((drop h n (CHead c k t) 
e2) \to (\forall (e1: C).((csubc g e1 e2) \to (ex2 C (\lambda (c1: C).(drop h 
n c1 e1)) (\lambda (c1: C).(csubc g c1 (CHead c k t))))))))) (\lambda (h: 
nat).(nat_ind (\lambda (n: nat).((drop n O (CHead c k t) e2) \to (\forall 
(e1: C).((csubc g e1 e2) \to (ex2 C (\lambda (c1: C).(drop n O c1 e1)) 
(\lambda (c1: C).(csubc g c1 (CHead c k t)))))))) (\lambda (H0: (drop O O 
(CHead c k t) e2)).(\lambda (e1: C).(\lambda (H1: (csubc g e1 e2)).(let H2 
\def (eq_ind_r C e2 (\lambda (c0: C).(csubc g e1 c0)) H1 (CHead c k t) 
(drop_gen_refl (CHead c k t) e2 H0)) in (ex_intro2 C (\lambda (c1: C).(drop O 
O c1 e1)) (\lambda (c1: C).(csubc g c1 (CHead c k t))) e1 (drop_refl e1) 
H2))))) (\lambda (n: nat).(\lambda (_: (((drop n O (CHead c k t) e2) \to 
(\forall (e1: C).((csubc g e1 e2) \to (ex2 C (\lambda (c1: C).(drop n O c1 
e1)) (\lambda (c1: C).(csubc g c1 (CHead c k t))))))))).(\lambda (H1: (drop 
(S n) O (CHead c k t) e2)).(\lambda (e1: C).(\lambda (H2: (csubc g e1 
e2)).(let H_x \def (H e2 O (r k n) (drop_gen_drop k c e2 t n H1) e1 H2) in 
(let H3 \def H_x in (ex2_ind C (\lambda (c1: C).(drop (r k n) O c1 e1)) 
(\lambda (c1: C).(csubc g c1 c)) (ex2 C (\lambda (c1: C).(drop (S n) O c1 
e1)) (\lambda (c1: C).(csubc g c1 (CHead c k t)))) (\lambda (x: C).(\lambda 
(H4: (drop (r k n) O x e1)).(\lambda (H5: (csubc g x c)).(ex_intro2 C 
(\lambda (c1: C).(drop (S n) O c1 e1)) (\lambda (c1: C).(csubc g c1 (CHead c 
k t))) (CHead x k t) (drop_drop k n x e1 H4 t) (csubc_head g x c H5 k t))))) 
H3)))))))) h)) (\lambda (n: nat).(\lambda (H0: ((\forall (h: nat).((drop h n 
(CHead c k t) e2) \to (\forall (e1: C).((csubc g e1 e2) \to (ex2 C (\lambda 
(c1: C).(drop h n c1 e1)) (\lambda (c1: C).(csubc g c1 (CHead c k 
t)))))))))).(\lambda (h: nat).(\lambda (H1: (drop h (S n) (CHead c k t) 
e2)).(\lambda (e1: C).(\lambda (H2: (csubc g e1 e2)).(ex3_2_ind C T (\lambda 
(e: C).(\lambda (v: T).(eq C e2 (CHead e k v)))) (\lambda (_: C).(\lambda (v: 
T).(eq T t (lift h (r k n) v)))) (\lambda (e: C).(\lambda (_: T).(drop h (r k 
n) c e))) (ex2 C (\lambda (c1: C).(drop h (S n) c1 e1)) (\lambda (c1: 
C).(csubc g c1 (CHead c k t)))) (\lambda (x0: C).(\lambda (x1: T).(\lambda 
(H3: (eq C e2 (CHead x0 k x1))).(\lambda (H4: (eq T t (lift h (r k n) 
x1))).(\lambda (H5: (drop h (r k n) c x0)).(let H6 \def (eq_ind C e2 (\lambda 
(c0: C).(csubc g e1 c0)) H2 (CHead x0 k x1) H3) in (let H7 \def (eq_ind C e2 
(\lambda (c0: C).(\forall (h0: nat).((drop h0 n (CHead c k t) c0) \to 
(\forall (e3: C).((csubc g e3 c0) \to (ex2 C (\lambda (c1: C).(drop h0 n c1 
e3)) (\lambda (c1: C).(csubc g c1 (CHead c k t))))))))) H0 (CHead x0 k x1) 
H3) in (let H8 \def (eq_ind T t (\lambda (t0: T).(\forall (h0: nat).((drop h0 
n (CHead c k t0) (CHead x0 k x1)) \to (\forall (e3: C).((csubc g e3 (CHead x0 
k x1)) \to (ex2 C (\lambda (c1: C).(drop h0 n c1 e3)) (\lambda (c1: C).(csubc 
g c1 (CHead c k t0))))))))) H7 (lift h (r k n) x1) H4) in (eq_ind_r T (lift h 
(r k n) x1) (\lambda (t0: T).(ex2 C (\lambda (c1: C).(drop h (S n) c1 e1)) 
(\lambda (c1: C).(csubc g c1 (CHead c k t0))))) (let H9 \def (match H6 in 
csubc return (\lambda (c0: C).(\lambda (c1: C).(\lambda (_: (csubc ? c0 
c1)).((eq C c0 e1) \to ((eq C c1 (CHead x0 k x1)) \to (ex2 C (\lambda (c3: 
C).(drop h (S n) c3 e1)) (\lambda (c3: C).(csubc g c3 (CHead c k (lift h (r k 
n) x1)))))))))) with [(csubc_sort n0) \Rightarrow (\lambda (H9: (eq C (CSort 
n0) e1)).(\lambda (H10: (eq C (CSort n0) (CHead x0 k x1))).(eq_ind C (CSort 
n0) (\lambda (c0: C).((eq C (CSort n0) (CHead x0 k x1)) \to (ex2 C (\lambda 
(c1: C).(drop h (S n) c1 c0)) (\lambda (c1: C).(csubc g c1 (CHead c k (lift h 
(r k n) x1))))))) (\lambda (H11: (eq C (CSort n0) (CHead x0 k x1))).(let H12 
\def (eq_ind C (CSort n0) (\lambda (e: C).(match e in C return (\lambda (_: 
C).Prop) with [(CSort _) \Rightarrow True | (CHead _ _ _) \Rightarrow 
False])) I (CHead x0 k x1) H11) in (False_ind (ex2 C (\lambda (c1: C).(drop h 
(S n) c1 (CSort n0))) (\lambda (c1: C).(csubc g c1 (CHead c k (lift h (r k n) 
x1))))) H12))) e1 H9 H10))) | (csubc_head c1 c0 H9 k0 v) \Rightarrow (\lambda 
(H10: (eq C (CHead c1 k0 v) e1)).(\lambda (H11: (eq C (CHead c0 k0 v) (CHead 
x0 k x1))).(eq_ind C (CHead c1 k0 v) (\lambda (c3: C).((eq C (CHead c0 k0 v) 
(CHead x0 k x1)) \to ((csubc g c1 c0) \to (ex2 C (\lambda (c4: C).(drop h (S 
n) c4 c3)) (\lambda (c4: C).(csubc g c4 (CHead c k (lift h (r k n) x1)))))))) 
(\lambda (H12: (eq C (CHead c0 k0 v) (CHead x0 k x1))).(let H13 \def (f_equal 
C T (\lambda (e: C).(match e in C return (\lambda (_: C).T) with [(CSort _) 
\Rightarrow v | (CHead _ _ t0) \Rightarrow t0])) (CHead c0 k0 v) (CHead x0 k 
x1) H12) in ((let H14 \def (f_equal C K (\lambda (e: C).(match e in C return 
(\lambda (_: C).K) with [(CSort _) \Rightarrow k0 | (CHead _ k1 _) 
\Rightarrow k1])) (CHead c0 k0 v) (CHead x0 k x1) H12) in ((let H15 \def 
(f_equal C C (\lambda (e: C).(match e in C return (\lambda (_: C).C) with 
[(CSort _) \Rightarrow c0 | (CHead c3 _ _) \Rightarrow c3])) (CHead c0 k0 v) 
(CHead x0 k x1) H12) in (eq_ind C x0 (\lambda (c3: C).((eq K k0 k) \to ((eq T 
v x1) \to ((csubc g c1 c3) \to (ex2 C (\lambda (c4: C).(drop h (S n) c4 
(CHead c1 k0 v))) (\lambda (c4: C).(csubc g c4 (CHead c k (lift h (r k n) 
x1))))))))) (\lambda (H16: (eq K k0 k)).(eq_ind K k (\lambda (k1: K).((eq T v 
x1) \to ((csubc g c1 x0) \to (ex2 C (\lambda (c3: C).(drop h (S n) c3 (CHead 
c1 k1 v))) (\lambda (c3: C).(csubc g c3 (CHead c k (lift h (r k n) x1)))))))) 
(\lambda (H17: (eq T v x1)).(eq_ind T x1 (\lambda (t0: T).((csubc g c1 x0) 
\to (ex2 C (\lambda (c3: C).(drop h (S n) c3 (CHead c1 k t0))) (\lambda (c3: 
C).(csubc g c3 (CHead c k (lift h (r k n) x1))))))) (\lambda (H18: (csubc g 
c1 x0)).(let H19 \def (eq_ind T v (\lambda (t0: T).(eq C (CHead c1 k0 t0) 
e1)) H10 x1 H17) in (let H20 \def (eq_ind K k0 (\lambda (k1: K).(eq C (CHead 
c1 k1 x1) e1)) H19 k H16) in (let H_x \def (H x0 (r k n) h H5 c1 H18) in (let 
H21 \def H_x in (ex2_ind C (\lambda (c3: C).(drop h (r k n) c3 c1)) (\lambda 
(c3: C).(csubc g c3 c)) (ex2 C (\lambda (c3: C).(drop h (S n) c3 (CHead c1 k 
x1))) (\lambda (c3: C).(csubc g c3 (CHead c k (lift h (r k n) x1))))) 
(\lambda (x: C).(\lambda (H22: (drop h (r k n) x c1)).(\lambda (H23: (csubc g 
x c)).(ex_intro2 C (\lambda (c3: C).(drop h (S n) c3 (CHead c1 k x1))) 
(\lambda (c3: C).(csubc g c3 (CHead c k (lift h (r k n) x1)))) (CHead x k 
(lift h (r k n) x1)) (drop_skip k h n x c1 H22 x1) (csubc_head g x c H23 k 
(lift h (r k n) x1)))))) H21)))))) v (sym_eq T v x1 H17))) k0 (sym_eq K k0 k 
H16))) c0 (sym_eq C c0 x0 H15))) H14)) H13))) e1 H10 H11 H9))) | (csubc_abst 
c1 c0 H9 v a H10 w H11) \Rightarrow (\lambda (H12: (eq C (CHead c1 (Bind 
Abst) v) e1)).(\lambda (H13: (eq C (CHead c0 (Bind Abbr) w) (CHead x0 k 
x1))).(eq_ind C (CHead c1 (Bind Abst) v) (\lambda (c3: C).((eq C (CHead c0 
(Bind Abbr) w) (CHead x0 k x1)) \to ((csubc g c1 c0) \to ((sc3 g (asucc g a) 
c1 v) \to ((sc3 g a c0 w) \to (ex2 C (\lambda (c4: C).(drop h (S n) c4 c3)) 
(\lambda (c4: C).(csubc g c4 (CHead c k (lift h (r k n) x1)))))))))) (\lambda 
(H14: (eq C (CHead c0 (Bind Abbr) w) (CHead x0 k x1))).(let H15 \def (f_equal 
C T (\lambda (e: C).(match e in C return (\lambda (_: C).T) with [(CSort _) 
\Rightarrow w | (CHead _ _ t0) \Rightarrow t0])) (CHead c0 (Bind Abbr) w) 
(CHead x0 k x1) H14) in ((let H16 \def (f_equal C K (\lambda (e: C).(match e 
in C return (\lambda (_: C).K) with [(CSort _) \Rightarrow (Bind Abbr) | 
(CHead _ k0 _) \Rightarrow k0])) (CHead c0 (Bind Abbr) w) (CHead x0 k x1) 
H14) in ((let H17 \def (f_equal C C (\lambda (e: C).(match e in C return 
(\lambda (_: C).C) with [(CSort _) \Rightarrow c0 | (CHead c3 _ _) 
\Rightarrow c3])) (CHead c0 (Bind Abbr) w) (CHead x0 k x1) H14) in (eq_ind C 
x0 (\lambda (c3: C).((eq K (Bind Abbr) k) \to ((eq T w x1) \to ((csubc g c1 
c3) \to ((sc3 g (asucc g a) c1 v) \to ((sc3 g a c3 w) \to (ex2 C (\lambda 
(c4: C).(drop h (S n) c4 (CHead c1 (Bind Abst) v))) (\lambda (c4: C).(csubc g 
c4 (CHead c k (lift h (r k n) x1))))))))))) (\lambda (H18: (eq K (Bind Abbr) 
k)).(eq_ind K (Bind Abbr) (\lambda (k0: K).((eq T w x1) \to ((csubc g c1 x0) 
\to ((sc3 g (asucc g a) c1 v) \to ((sc3 g a x0 w) \to (ex2 C (\lambda (c3: 
C).(drop h (S n) c3 (CHead c1 (Bind Abst) v))) (\lambda (c3: C).(csubc g c3 
(CHead c k0 (lift h (r k0 n) x1)))))))))) (\lambda (H19: (eq T w x1)).(eq_ind 
T x1 (\lambda (t0: T).((csubc g c1 x0) \to ((sc3 g (asucc g a) c1 v) \to 
((sc3 g a x0 t0) \to (ex2 C (\lambda (c3: C).(drop h (S n) c3 (CHead c1 (Bind 
Abst) v))) (\lambda (c3: C).(csubc g c3 (CHead c (Bind Abbr) (lift h (r (Bind 
Abbr) n) x1))))))))) (\lambda (H20: (csubc g c1 x0)).(\lambda (H21: (sc3 g 
(asucc g a) c1 v)).(\lambda (H22: (sc3 g a x0 x1)).(let H23 \def (eq_ind_r K 
k (\lambda (k0: K).(\forall (h0: nat).((drop h0 n (CHead c k0 (lift h (r k0 
n) x1)) (CHead x0 k0 x1)) \to (\forall (e3: C).((csubc g e3 (CHead x0 k0 x1)) 
\to (ex2 C (\lambda (c3: C).(drop h0 n c3 e3)) (\lambda (c3: C).(csubc g c3 
(CHead c k0 (lift h (r k0 n) x1)))))))))) H8 (Bind Abbr) H18) in (let H24 
\def (eq_ind_r K k (\lambda (k0: K).(drop h (r k0 n) c x0)) H5 (Bind Abbr) 
H18) in (let H_x \def (H x0 (r (Bind Abbr) n) h H24 c1 H20) in (let H25 \def 
H_x in (ex2_ind C (\lambda (c3: C).(drop h (r (Bind Abbr) n) c3 c1)) (\lambda 
(c3: C).(csubc g c3 c)) (ex2 C (\lambda (c3: C).(drop h (S n) c3 (CHead c1 
(Bind Abst) v))) (\lambda (c3: C).(csubc g c3 (CHead c (Bind Abbr) (lift h (r 
(Bind Abbr) n) x1))))) (\lambda (x: C).(\lambda (H26: (drop h (r (Bind Abbr) 
n) x c1)).(\lambda (H27: (csubc g x c)).(ex_intro2 C (\lambda (c3: C).(drop h 
(S n) c3 (CHead c1 (Bind Abst) v))) (\lambda (c3: C).(csubc g c3 (CHead c 
(Bind Abbr) (lift h (r (Bind Abbr) n) x1)))) (CHead x (Bind Abst) (lift h n 
v)) (drop_skip_bind h n x c1 H26 Abst v) (csubc_abst g x c H27 (lift h n v) a 
(sc3_lift g (asucc g a) c1 v H21 x h n H26) (lift h (r (Bind Abbr) n) x1) 
(sc3_lift g a x0 x1 H22 c h (r (Bind Abbr) n) H24)))))) H25)))))))) w (sym_eq 
T w x1 H19))) k H18)) c0 (sym_eq C c0 x0 H17))) H16)) H15))) e1 H12 H13 H9 
H10 H11)))]) in (H9 (refl_equal C e1) (refl_equal C (CHead x0 k x1)))) t 
H4))))))))) (drop_gen_skip_l c e2 t h n k H1)))))))) d))))))) c2)).

