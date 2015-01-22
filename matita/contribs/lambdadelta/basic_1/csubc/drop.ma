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

include "Basic-1/csubc/fwd.ma".

include "Basic-1/sc3/props.ma".

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
C).(\lambda (H2: (csubc g (CHead c k t) c2)).(let H_x \def (csubc_gen_head_l 
g c c2 t k H2) in (let H3 \def H_x in (or3_ind (ex2 C (\lambda (c3: C).(eq C 
c2 (CHead c3 k t))) (\lambda (c3: C).(csubc g c c3))) (ex5_3 C T A (\lambda 
(_: C).(\lambda (_: T).(\lambda (_: A).(eq K k (Bind Abst))))) (\lambda (c3: 
C).(\lambda (w: T).(\lambda (_: A).(eq C c2 (CHead c3 (Bind Abbr) w))))) 
(\lambda (c3: C).(\lambda (_: T).(\lambda (_: A).(csubc g c c3)))) (\lambda 
(_: C).(\lambda (_: T).(\lambda (a: A).(sc3 g (asucc g a) c t)))) (\lambda 
(c3: C).(\lambda (w: T).(\lambda (a: A).(sc3 g a c3 w))))) (ex4_3 B C T 
(\lambda (b: B).(\lambda (c3: C).(\lambda (v2: T).(eq C c2 (CHead c3 (Bind b) 
v2))))) (\lambda (_: B).(\lambda (_: C).(\lambda (_: T).(eq K k (Bind 
Void))))) (\lambda (b: B).(\lambda (_: C).(\lambda (_: T).(not (eq B b 
Void))))) (\lambda (_: B).(\lambda (c3: C).(\lambda (_: T).(csubc g c c3))))) 
(ex2 C (\lambda (e2: C).(drop (S n) O c2 e2)) (\lambda (e2: C).(csubc g e1 
e2))) (\lambda (H4: (ex2 C (\lambda (c3: C).(eq C c2 (CHead c3 k t))) 
(\lambda (c3: C).(csubc g c c3)))).(ex2_ind C (\lambda (c3: C).(eq C c2 
(CHead c3 k t))) (\lambda (c3: C).(csubc g c c3)) (ex2 C (\lambda (e2: 
C).(drop (S n) O c2 e2)) (\lambda (e2: C).(csubc g e1 e2))) (\lambda (x: 
C).(\lambda (H5: (eq C c2 (CHead x k t))).(\lambda (H6: (csubc g c 
x)).(eq_ind_r C (CHead x k t) (\lambda (c0: C).(ex2 C (\lambda (e2: C).(drop 
(S n) O c0 e2)) (\lambda (e2: C).(csubc g e1 e2)))) (let H_x0 \def (H e1 (r k 
n) (drop_gen_drop k c e1 t n H1) x H6) in (let H7 \def H_x0 in (ex2_ind C 
(\lambda (e2: C).(drop (r k n) O x e2)) (\lambda (e2: C).(csubc g e1 e2)) 
(ex2 C (\lambda (e2: C).(drop (S n) O (CHead x k t) e2)) (\lambda (e2: 
C).(csubc g e1 e2))) (\lambda (x0: C).(\lambda (H8: (drop (r k n) O x 
x0)).(\lambda (H9: (csubc g e1 x0)).(ex_intro2 C (\lambda (e2: C).(drop (S n) 
O (CHead x k t) e2)) (\lambda (e2: C).(csubc g e1 e2)) x0 (drop_drop k n x x0 
H8 t) H9)))) H7))) c2 H5)))) H4)) (\lambda (H4: (ex5_3 C T A (\lambda (_: 
C).(\lambda (_: T).(\lambda (_: A).(eq K k (Bind Abst))))) (\lambda (c3: 
C).(\lambda (w: T).(\lambda (_: A).(eq C c2 (CHead c3 (Bind Abbr) w))))) 
(\lambda (c3: C).(\lambda (_: T).(\lambda (_: A).(csubc g c c3)))) (\lambda 
(_: C).(\lambda (_: T).(\lambda (a: A).(sc3 g (asucc g a) c t)))) (\lambda 
(c3: C).(\lambda (w: T).(\lambda (a: A).(sc3 g a c3 w)))))).(ex5_3_ind C T A 
(\lambda (_: C).(\lambda (_: T).(\lambda (_: A).(eq K k (Bind Abst))))) 
(\lambda (c3: C).(\lambda (w: T).(\lambda (_: A).(eq C c2 (CHead c3 (Bind 
Abbr) w))))) (\lambda (c3: C).(\lambda (_: T).(\lambda (_: A).(csubc g c 
c3)))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(sc3 g (asucc g a) c 
t)))) (\lambda (c3: C).(\lambda (w: T).(\lambda (a: A).(sc3 g a c3 w)))) (ex2 
C (\lambda (e2: C).(drop (S n) O c2 e2)) (\lambda (e2: C).(csubc g e1 e2))) 
(\lambda (x0: C).(\lambda (x1: T).(\lambda (x2: A).(\lambda (H5: (eq K k 
(Bind Abst))).(\lambda (H6: (eq C c2 (CHead x0 (Bind Abbr) x1))).(\lambda 
(H7: (csubc g c x0)).(\lambda (_: (sc3 g (asucc g x2) c t)).(\lambda (_: (sc3 
g x2 x0 x1)).(eq_ind_r C (CHead x0 (Bind Abbr) x1) (\lambda (c0: C).(ex2 C 
(\lambda (e2: C).(drop (S n) O c0 e2)) (\lambda (e2: C).(csubc g e1 e2)))) 
(let H10 \def (eq_ind K k (\lambda (k0: K).(drop (r k0 n) O c e1)) 
(drop_gen_drop k c e1 t n H1) (Bind Abst) H5) in (let H11 \def (eq_ind K k 
(\lambda (k0: K).((drop n O (CHead c k0 t) e1) \to (\forall (c3: C).((csubc g 
(CHead c k0 t) c3) \to (ex2 C (\lambda (e2: C).(drop n O c3 e2)) (\lambda 
(e2: C).(csubc g e1 e2))))))) H0 (Bind Abst) H5) in (let H_x0 \def (H e1 (r 
(Bind Abst) n) H10 x0 H7) in (let H12 \def H_x0 in (ex2_ind C (\lambda (e2: 
C).(drop n O x0 e2)) (\lambda (e2: C).(csubc g e1 e2)) (ex2 C (\lambda (e2: 
C).(drop (S n) O (CHead x0 (Bind Abbr) x1) e2)) (\lambda (e2: C).(csubc g e1 
e2))) (\lambda (x: C).(\lambda (H13: (drop n O x0 x)).(\lambda (H14: (csubc g 
e1 x)).(ex_intro2 C (\lambda (e2: C).(drop (S n) O (CHead x0 (Bind Abbr) x1) 
e2)) (\lambda (e2: C).(csubc g e1 e2)) x (drop_drop (Bind Abbr) n x0 x H13 
x1) H14)))) H12))))) c2 H6))))))))) H4)) (\lambda (H4: (ex4_3 B C T (\lambda 
(b: B).(\lambda (c3: C).(\lambda (v2: T).(eq C c2 (CHead c3 (Bind b) v2))))) 
(\lambda (_: B).(\lambda (_: C).(\lambda (_: T).(eq K k (Bind Void))))) 
(\lambda (b: B).(\lambda (_: C).(\lambda (_: T).(not (eq B b Void))))) 
(\lambda (_: B).(\lambda (c3: C).(\lambda (_: T).(csubc g c 
c3)))))).(ex4_3_ind B C T (\lambda (b: B).(\lambda (c3: C).(\lambda (v2: 
T).(eq C c2 (CHead c3 (Bind b) v2))))) (\lambda (_: B).(\lambda (_: 
C).(\lambda (_: T).(eq K k (Bind Void))))) (\lambda (b: B).(\lambda (_: 
C).(\lambda (_: T).(not (eq B b Void))))) (\lambda (_: B).(\lambda (c3: 
C).(\lambda (_: T).(csubc g c c3)))) (ex2 C (\lambda (e2: C).(drop (S n) O c2 
e2)) (\lambda (e2: C).(csubc g e1 e2))) (\lambda (x0: B).(\lambda (x1: 
C).(\lambda (x2: T).(\lambda (H5: (eq C c2 (CHead x1 (Bind x0) x2))).(\lambda 
(H6: (eq K k (Bind Void))).(\lambda (_: (not (eq B x0 Void))).(\lambda (H8: 
(csubc g c x1)).(eq_ind_r C (CHead x1 (Bind x0) x2) (\lambda (c0: C).(ex2 C 
(\lambda (e2: C).(drop (S n) O c0 e2)) (\lambda (e2: C).(csubc g e1 e2)))) 
(let H9 \def (eq_ind K k (\lambda (k0: K).(drop (r k0 n) O c e1)) 
(drop_gen_drop k c e1 t n H1) (Bind Void) H6) in (let H10 \def (eq_ind K k 
(\lambda (k0: K).((drop n O (CHead c k0 t) e1) \to (\forall (c3: C).((csubc g 
(CHead c k0 t) c3) \to (ex2 C (\lambda (e2: C).(drop n O c3 e2)) (\lambda 
(e2: C).(csubc g e1 e2))))))) H0 (Bind Void) H6) in (let H_x0 \def (H e1 (r 
(Bind Void) n) H9 x1 H8) in (let H11 \def H_x0 in (ex2_ind C (\lambda (e2: 
C).(drop n O x1 e2)) (\lambda (e2: C).(csubc g e1 e2)) (ex2 C (\lambda (e2: 
C).(drop (S n) O (CHead x1 (Bind x0) x2) e2)) (\lambda (e2: C).(csubc g e1 
e2))) (\lambda (x: C).(\lambda (H12: (drop n O x1 x)).(\lambda (H13: (csubc g 
e1 x)).(ex_intro2 C (\lambda (e2: C).(drop (S n) O (CHead x1 (Bind x0) x2) 
e2)) (\lambda (e2: C).(csubc g e1 e2)) x (drop_drop (Bind x0) n x1 x H12 x2) 
H13)))) H11))))) c2 H5)))))))) H4)) H3)))))))) h))))))) c1)).
(* COMMENTS
Initial nodes: 2389
END *)

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
c1 e1)) (\lambda (c1: C).(csubc g (CHead c k t0) c1)))) (let H_x \def 
(csubc_gen_head_l g x0 e1 x1 k H6) in (let H9 \def H_x in (or3_ind (ex2 C 
(\lambda (c3: C).(eq C e1 (CHead c3 k x1))) (\lambda (c3: C).(csubc g x0 
c3))) (ex5_3 C T A (\lambda (_: C).(\lambda (_: T).(\lambda (_: A).(eq K k 
(Bind Abst))))) (\lambda (c3: C).(\lambda (w: T).(\lambda (_: A).(eq C e1 
(CHead c3 (Bind Abbr) w))))) (\lambda (c3: C).(\lambda (_: T).(\lambda (_: 
A).(csubc g x0 c3)))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(sc3 g 
(asucc g a) x0 x1)))) (\lambda (c3: C).(\lambda (w: T).(\lambda (a: A).(sc3 g 
a c3 w))))) (ex4_3 B C T (\lambda (b: B).(\lambda (c3: C).(\lambda (v2: 
T).(eq C e1 (CHead c3 (Bind b) v2))))) (\lambda (_: B).(\lambda (_: 
C).(\lambda (_: T).(eq K k (Bind Void))))) (\lambda (b: B).(\lambda (_: 
C).(\lambda (_: T).(not (eq B b Void))))) (\lambda (_: B).(\lambda (c3: 
C).(\lambda (_: T).(csubc g x0 c3))))) (ex2 C (\lambda (c1: C).(drop h (S n) 
c1 e1)) (\lambda (c1: C).(csubc g (CHead c k (lift h (r k n) x1)) c1))) 
(\lambda (H10: (ex2 C (\lambda (c3: C).(eq C e1 (CHead c3 k x1))) (\lambda 
(c3: C).(csubc g x0 c3)))).(ex2_ind C (\lambda (c3: C).(eq C e1 (CHead c3 k 
x1))) (\lambda (c3: C).(csubc g x0 c3)) (ex2 C (\lambda (c1: C).(drop h (S n) 
c1 e1)) (\lambda (c1: C).(csubc g (CHead c k (lift h (r k n) x1)) c1))) 
(\lambda (x: C).(\lambda (H11: (eq C e1 (CHead x k x1))).(\lambda (H12: 
(csubc g x0 x)).(eq_ind_r C (CHead x k x1) (\lambda (c0: C).(ex2 C (\lambda 
(c1: C).(drop h (S n) c1 c0)) (\lambda (c1: C).(csubc g (CHead c k (lift h (r 
k n) x1)) c1)))) (let H_x0 \def (H x0 (r k n) h H5 x H12) in (let H13 \def 
H_x0 in (ex2_ind C (\lambda (c1: C).(drop h (r k n) c1 x)) (\lambda (c1: 
C).(csubc g c c1)) (ex2 C (\lambda (c1: C).(drop h (S n) c1 (CHead x k x1))) 
(\lambda (c1: C).(csubc g (CHead c k (lift h (r k n) x1)) c1))) (\lambda (x2: 
C).(\lambda (H14: (drop h (r k n) x2 x)).(\lambda (H15: (csubc g c 
x2)).(ex_intro2 C (\lambda (c1: C).(drop h (S n) c1 (CHead x k x1))) (\lambda 
(c1: C).(csubc g (CHead c k (lift h (r k n) x1)) c1)) (CHead x2 k (lift h (r 
k n) x1)) (drop_skip k h n x2 x H14 x1) (csubc_head g c x2 H15 k (lift h (r k 
n) x1)))))) H13))) e1 H11)))) H10)) (\lambda (H10: (ex5_3 C T A (\lambda (_: 
C).(\lambda (_: T).(\lambda (_: A).(eq K k (Bind Abst))))) (\lambda (c3: 
C).(\lambda (w: T).(\lambda (_: A).(eq C e1 (CHead c3 (Bind Abbr) w))))) 
(\lambda (c3: C).(\lambda (_: T).(\lambda (_: A).(csubc g x0 c3)))) (\lambda 
(_: C).(\lambda (_: T).(\lambda (a: A).(sc3 g (asucc g a) x0 x1)))) (\lambda 
(c3: C).(\lambda (w: T).(\lambda (a: A).(sc3 g a c3 w)))))).(ex5_3_ind C T A 
(\lambda (_: C).(\lambda (_: T).(\lambda (_: A).(eq K k (Bind Abst))))) 
(\lambda (c3: C).(\lambda (w: T).(\lambda (_: A).(eq C e1 (CHead c3 (Bind 
Abbr) w))))) (\lambda (c3: C).(\lambda (_: T).(\lambda (_: A).(csubc g x0 
c3)))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(sc3 g (asucc g a) x0 
x1)))) (\lambda (c3: C).(\lambda (w: T).(\lambda (a: A).(sc3 g a c3 w)))) 
(ex2 C (\lambda (c1: C).(drop h (S n) c1 e1)) (\lambda (c1: C).(csubc g 
(CHead c k (lift h (r k n) x1)) c1))) (\lambda (x2: C).(\lambda (x3: 
T).(\lambda (x4: A).(\lambda (H11: (eq K k (Bind Abst))).(\lambda (H12: (eq C 
e1 (CHead x2 (Bind Abbr) x3))).(\lambda (H13: (csubc g x0 x2)).(\lambda (H14: 
(sc3 g (asucc g x4) x0 x1)).(\lambda (H15: (sc3 g x4 x2 x3)).(eq_ind_r C 
(CHead x2 (Bind Abbr) x3) (\lambda (c0: C).(ex2 C (\lambda (c1: C).(drop h (S 
n) c1 c0)) (\lambda (c1: C).(csubc g (CHead c k (lift h (r k n) x1)) c1)))) 
(let H16 \def (eq_ind K k (\lambda (k0: K).(\forall (h0: nat).((drop h0 n 
(CHead c k0 (lift h (r k0 n) x1)) (CHead x0 k0 x1)) \to (\forall (e3: 
C).((csubc g (CHead x0 k0 x1) e3) \to (ex2 C (\lambda (c1: C).(drop h0 n c1 
e3)) (\lambda (c1: C).(csubc g (CHead c k0 (lift h (r k0 n) x1)) c1)))))))) 
H8 (Bind Abst) H11) in (let H17 \def (eq_ind K k (\lambda (k0: K).(drop h (r 
k0 n) c x0)) H5 (Bind Abst) H11) in (eq_ind_r K (Bind Abst) (\lambda (k0: 
K).(ex2 C (\lambda (c1: C).(drop h (S n) c1 (CHead x2 (Bind Abbr) x3))) 
(\lambda (c1: C).(csubc g (CHead c k0 (lift h (r k0 n) x1)) c1)))) (let H_x0 
\def (H x0 (r (Bind Abst) n) h H17 x2 H13) in (let H18 \def H_x0 in (ex2_ind 
C (\lambda (c1: C).(drop h n c1 x2)) (\lambda (c1: C).(csubc g c c1)) (ex2 C 
(\lambda (c1: C).(drop h (S n) c1 (CHead x2 (Bind Abbr) x3))) (\lambda (c1: 
C).(csubc g (CHead c (Bind Abst) (lift h (r (Bind Abst) n) x1)) c1))) 
(\lambda (x: C).(\lambda (H19: (drop h n x x2)).(\lambda (H20: (csubc g c 
x)).(ex_intro2 C (\lambda (c1: C).(drop h (S n) c1 (CHead x2 (Bind Abbr) 
x3))) (\lambda (c1: C).(csubc g (CHead c (Bind Abst) (lift h (r (Bind Abst) 
n) x1)) c1)) (CHead x (Bind Abbr) (lift h n x3)) (drop_skip_bind h n x x2 H19 
Abbr x3) (csubc_abst g c x H20 (lift h (r (Bind Abst) n) x1) x4 (sc3_lift g 
(asucc g x4) x0 x1 H14 c h (r (Bind Abst) n) H17) (lift h n x3) (sc3_lift g 
x4 x2 x3 H15 x h n H19)))))) H18))) k H11))) e1 H12))))))))) H10)) (\lambda 
(H10: (ex4_3 B C T (\lambda (b: B).(\lambda (c3: C).(\lambda (v2: T).(eq C e1 
(CHead c3 (Bind b) v2))))) (\lambda (_: B).(\lambda (_: C).(\lambda (_: 
T).(eq K k (Bind Void))))) (\lambda (b: B).(\lambda (_: C).(\lambda (_: 
T).(not (eq B b Void))))) (\lambda (_: B).(\lambda (c3: C).(\lambda (_: 
T).(csubc g x0 c3)))))).(ex4_3_ind B C T (\lambda (b: B).(\lambda (c3: 
C).(\lambda (v2: T).(eq C e1 (CHead c3 (Bind b) v2))))) (\lambda (_: 
B).(\lambda (_: C).(\lambda (_: T).(eq K k (Bind Void))))) (\lambda (b: 
B).(\lambda (_: C).(\lambda (_: T).(not (eq B b Void))))) (\lambda (_: 
B).(\lambda (c3: C).(\lambda (_: T).(csubc g x0 c3)))) (ex2 C (\lambda (c1: 
C).(drop h (S n) c1 e1)) (\lambda (c1: C).(csubc g (CHead c k (lift h (r k n) 
x1)) c1))) (\lambda (x2: B).(\lambda (x3: C).(\lambda (x4: T).(\lambda (H11: 
(eq C e1 (CHead x3 (Bind x2) x4))).(\lambda (H12: (eq K k (Bind 
Void))).(\lambda (H13: (not (eq B x2 Void))).(\lambda (H14: (csubc g x0 
x3)).(eq_ind_r C (CHead x3 (Bind x2) x4) (\lambda (c0: C).(ex2 C (\lambda 
(c1: C).(drop h (S n) c1 c0)) (\lambda (c1: C).(csubc g (CHead c k (lift h (r 
k n) x1)) c1)))) (let H15 \def (eq_ind K k (\lambda (k0: K).(\forall (h0: 
nat).((drop h0 n (CHead c k0 (lift h (r k0 n) x1)) (CHead x0 k0 x1)) \to 
(\forall (e3: C).((csubc g (CHead x0 k0 x1) e3) \to (ex2 C (\lambda (c1: 
C).(drop h0 n c1 e3)) (\lambda (c1: C).(csubc g (CHead c k0 (lift h (r k0 n) 
x1)) c1)))))))) H8 (Bind Void) H12) in (let H16 \def (eq_ind K k (\lambda 
(k0: K).(drop h (r k0 n) c x0)) H5 (Bind Void) H12) in (eq_ind_r K (Bind 
Void) (\lambda (k0: K).(ex2 C (\lambda (c1: C).(drop h (S n) c1 (CHead x3 
(Bind x2) x4))) (\lambda (c1: C).(csubc g (CHead c k0 (lift h (r k0 n) x1)) 
c1)))) (let H_x0 \def (H x0 (r (Bind Void) n) h H16 x3 H14) in (let H17 \def 
H_x0 in (ex2_ind C (\lambda (c1: C).(drop h n c1 x3)) (\lambda (c1: C).(csubc 
g c c1)) (ex2 C (\lambda (c1: C).(drop h (S n) c1 (CHead x3 (Bind x2) x4))) 
(\lambda (c1: C).(csubc g (CHead c (Bind Void) (lift h (r (Bind Void) n) x1)) 
c1))) (\lambda (x: C).(\lambda (H18: (drop h n x x3)).(\lambda (H19: (csubc g 
c x)).(ex_intro2 C (\lambda (c1: C).(drop h (S n) c1 (CHead x3 (Bind x2) 
x4))) (\lambda (c1: C).(csubc g (CHead c (Bind Void) (lift h (r (Bind Void) 
n) x1)) c1)) (CHead x (Bind x2) (lift h n x4)) (drop_skip_bind h n x x3 H18 
x2 x4) (csubc_void g c x H19 x2 H13 (lift h (r (Bind Void) n) x1) (lift h n 
x4)))))) H17))) k H12))) e1 H11)))))))) H10)) H9))) t H4))))))))) 
(drop_gen_skip_l c e2 t h n k H1)))))))) d))))))) c2)).
(* COMMENTS
Initial nodes: 3747
END *)

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
(\lambda (c1: C).(csubc g c1 (CHead c k t0))))) (let H_x \def 
(csubc_gen_head_r g x0 e1 x1 k H6) in (let H9 \def H_x in (or3_ind (ex2 C 
(\lambda (c1: C).(eq C e1 (CHead c1 k x1))) (\lambda (c1: C).(csubc g c1 
x0))) (ex5_3 C T A (\lambda (_: C).(\lambda (_: T).(\lambda (_: A).(eq K k 
(Bind Abbr))))) (\lambda (c1: C).(\lambda (v: T).(\lambda (_: A).(eq C e1 
(CHead c1 (Bind Abst) v))))) (\lambda (c1: C).(\lambda (_: T).(\lambda (_: 
A).(csubc g c1 x0)))) (\lambda (c1: C).(\lambda (v: T).(\lambda (a: A).(sc3 g 
(asucc g a) c1 v)))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(sc3 g a 
x0 x1))))) (ex4_3 B C T (\lambda (_: B).(\lambda (c1: C).(\lambda (v1: T).(eq 
C e1 (CHead c1 (Bind Void) v1))))) (\lambda (b: B).(\lambda (_: C).(\lambda 
(_: T).(eq K k (Bind b))))) (\lambda (b: B).(\lambda (_: C).(\lambda (_: 
T).(not (eq B b Void))))) (\lambda (_: B).(\lambda (c1: C).(\lambda (_: 
T).(csubc g c1 x0))))) (ex2 C (\lambda (c1: C).(drop h (S n) c1 e1)) (\lambda 
(c1: C).(csubc g c1 (CHead c k (lift h (r k n) x1))))) (\lambda (H10: (ex2 C 
(\lambda (c1: C).(eq C e1 (CHead c1 k x1))) (\lambda (c1: C).(csubc g c1 
x0)))).(ex2_ind C (\lambda (c1: C).(eq C e1 (CHead c1 k x1))) (\lambda (c1: 
C).(csubc g c1 x0)) (ex2 C (\lambda (c1: C).(drop h (S n) c1 e1)) (\lambda 
(c1: C).(csubc g c1 (CHead c k (lift h (r k n) x1))))) (\lambda (x: 
C).(\lambda (H11: (eq C e1 (CHead x k x1))).(\lambda (H12: (csubc g x 
x0)).(eq_ind_r C (CHead x k x1) (\lambda (c0: C).(ex2 C (\lambda (c1: 
C).(drop h (S n) c1 c0)) (\lambda (c1: C).(csubc g c1 (CHead c k (lift h (r k 
n) x1)))))) (let H_x0 \def (H x0 (r k n) h H5 x H12) in (let H13 \def H_x0 in 
(ex2_ind C (\lambda (c1: C).(drop h (r k n) c1 x)) (\lambda (c1: C).(csubc g 
c1 c)) (ex2 C (\lambda (c1: C).(drop h (S n) c1 (CHead x k x1))) (\lambda 
(c1: C).(csubc g c1 (CHead c k (lift h (r k n) x1))))) (\lambda (x2: 
C).(\lambda (H14: (drop h (r k n) x2 x)).(\lambda (H15: (csubc g x2 
c)).(ex_intro2 C (\lambda (c1: C).(drop h (S n) c1 (CHead x k x1))) (\lambda 
(c1: C).(csubc g c1 (CHead c k (lift h (r k n) x1)))) (CHead x2 k (lift h (r 
k n) x1)) (drop_skip k h n x2 x H14 x1) (csubc_head g x2 c H15 k (lift h (r k 
n) x1)))))) H13))) e1 H11)))) H10)) (\lambda (H10: (ex5_3 C T A (\lambda (_: 
C).(\lambda (_: T).(\lambda (_: A).(eq K k (Bind Abbr))))) (\lambda (c1: 
C).(\lambda (v: T).(\lambda (_: A).(eq C e1 (CHead c1 (Bind Abst) v))))) 
(\lambda (c1: C).(\lambda (_: T).(\lambda (_: A).(csubc g c1 x0)))) (\lambda 
(c1: C).(\lambda (v: T).(\lambda (a: A).(sc3 g (asucc g a) c1 v)))) (\lambda 
(_: C).(\lambda (_: T).(\lambda (a: A).(sc3 g a x0 x1)))))).(ex5_3_ind C T A 
(\lambda (_: C).(\lambda (_: T).(\lambda (_: A).(eq K k (Bind Abbr))))) 
(\lambda (c1: C).(\lambda (v: T).(\lambda (_: A).(eq C e1 (CHead c1 (Bind 
Abst) v))))) (\lambda (c1: C).(\lambda (_: T).(\lambda (_: A).(csubc g c1 
x0)))) (\lambda (c1: C).(\lambda (v: T).(\lambda (a: A).(sc3 g (asucc g a) c1 
v)))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(sc3 g a x0 x1)))) (ex2 
C (\lambda (c1: C).(drop h (S n) c1 e1)) (\lambda (c1: C).(csubc g c1 (CHead 
c k (lift h (r k n) x1))))) (\lambda (x2: C).(\lambda (x3: T).(\lambda (x4: 
A).(\lambda (H11: (eq K k (Bind Abbr))).(\lambda (H12: (eq C e1 (CHead x2 
(Bind Abst) x3))).(\lambda (H13: (csubc g x2 x0)).(\lambda (H14: (sc3 g 
(asucc g x4) x2 x3)).(\lambda (H15: (sc3 g x4 x0 x1)).(eq_ind_r C (CHead x2 
(Bind Abst) x3) (\lambda (c0: C).(ex2 C (\lambda (c1: C).(drop h (S n) c1 
c0)) (\lambda (c1: C).(csubc g c1 (CHead c k (lift h (r k n) x1)))))) (let 
H16 \def (eq_ind K k (\lambda (k0: K).(\forall (h0: nat).((drop h0 n (CHead c 
k0 (lift h (r k0 n) x1)) (CHead x0 k0 x1)) \to (\forall (e3: C).((csubc g e3 
(CHead x0 k0 x1)) \to (ex2 C (\lambda (c1: C).(drop h0 n c1 e3)) (\lambda 
(c1: C).(csubc g c1 (CHead c k0 (lift h (r k0 n) x1)))))))))) H8 (Bind Abbr) 
H11) in (let H17 \def (eq_ind K k (\lambda (k0: K).(drop h (r k0 n) c x0)) H5 
(Bind Abbr) H11) in (eq_ind_r K (Bind Abbr) (\lambda (k0: K).(ex2 C (\lambda 
(c1: C).(drop h (S n) c1 (CHead x2 (Bind Abst) x3))) (\lambda (c1: C).(csubc 
g c1 (CHead c k0 (lift h (r k0 n) x1)))))) (let H_x0 \def (H x0 (r (Bind 
Abbr) n) h H17 x2 H13) in (let H18 \def H_x0 in (ex2_ind C (\lambda (c1: 
C).(drop h n c1 x2)) (\lambda (c1: C).(csubc g c1 c)) (ex2 C (\lambda (c1: 
C).(drop h (S n) c1 (CHead x2 (Bind Abst) x3))) (\lambda (c1: C).(csubc g c1 
(CHead c (Bind Abbr) (lift h (r (Bind Abbr) n) x1))))) (\lambda (x: 
C).(\lambda (H19: (drop h n x x2)).(\lambda (H20: (csubc g x c)).(ex_intro2 C 
(\lambda (c1: C).(drop h (S n) c1 (CHead x2 (Bind Abst) x3))) (\lambda (c1: 
C).(csubc g c1 (CHead c (Bind Abbr) (lift h (r (Bind Abbr) n) x1)))) (CHead x 
(Bind Abst) (lift h n x3)) (drop_skip_bind h n x x2 H19 Abst x3) (csubc_abst 
g x c H20 (lift h n x3) x4 (sc3_lift g (asucc g x4) x2 x3 H14 x h n H19) 
(lift h (r (Bind Abbr) n) x1) (sc3_lift g x4 x0 x1 H15 c h (r (Bind Abbr) n) 
H17)))))) H18))) k H11))) e1 H12))))))))) H10)) (\lambda (H10: (ex4_3 B C T 
(\lambda (_: B).(\lambda (c1: C).(\lambda (v1: T).(eq C e1 (CHead c1 (Bind 
Void) v1))))) (\lambda (b: B).(\lambda (_: C).(\lambda (_: T).(eq K k (Bind 
b))))) (\lambda (b: B).(\lambda (_: C).(\lambda (_: T).(not (eq B b Void))))) 
(\lambda (_: B).(\lambda (c1: C).(\lambda (_: T).(csubc g c1 
x0)))))).(ex4_3_ind B C T (\lambda (_: B).(\lambda (c1: C).(\lambda (v1: 
T).(eq C e1 (CHead c1 (Bind Void) v1))))) (\lambda (b: B).(\lambda (_: 
C).(\lambda (_: T).(eq K k (Bind b))))) (\lambda (b: B).(\lambda (_: 
C).(\lambda (_: T).(not (eq B b Void))))) (\lambda (_: B).(\lambda (c1: 
C).(\lambda (_: T).(csubc g c1 x0)))) (ex2 C (\lambda (c1: C).(drop h (S n) 
c1 e1)) (\lambda (c1: C).(csubc g c1 (CHead c k (lift h (r k n) x1))))) 
(\lambda (x2: B).(\lambda (x3: C).(\lambda (x4: T).(\lambda (H11: (eq C e1 
(CHead x3 (Bind Void) x4))).(\lambda (H12: (eq K k (Bind x2))).(\lambda (H13: 
(not (eq B x2 Void))).(\lambda (H14: (csubc g x3 x0)).(eq_ind_r C (CHead x3 
(Bind Void) x4) (\lambda (c0: C).(ex2 C (\lambda (c1: C).(drop h (S n) c1 
c0)) (\lambda (c1: C).(csubc g c1 (CHead c k (lift h (r k n) x1)))))) (let 
H15 \def (eq_ind K k (\lambda (k0: K).(\forall (h0: nat).((drop h0 n (CHead c 
k0 (lift h (r k0 n) x1)) (CHead x0 k0 x1)) \to (\forall (e3: C).((csubc g e3 
(CHead x0 k0 x1)) \to (ex2 C (\lambda (c1: C).(drop h0 n c1 e3)) (\lambda 
(c1: C).(csubc g c1 (CHead c k0 (lift h (r k0 n) x1)))))))))) H8 (Bind x2) 
H12) in (let H16 \def (eq_ind K k (\lambda (k0: K).(drop h (r k0 n) c x0)) H5 
(Bind x2) H12) in (eq_ind_r K (Bind x2) (\lambda (k0: K).(ex2 C (\lambda (c1: 
C).(drop h (S n) c1 (CHead x3 (Bind Void) x4))) (\lambda (c1: C).(csubc g c1 
(CHead c k0 (lift h (r k0 n) x1)))))) (let H_x0 \def (H x0 (r (Bind x2) n) h 
H16 x3 H14) in (let H17 \def H_x0 in (ex2_ind C (\lambda (c1: C).(drop h n c1 
x3)) (\lambda (c1: C).(csubc g c1 c)) (ex2 C (\lambda (c1: C).(drop h (S n) 
c1 (CHead x3 (Bind Void) x4))) (\lambda (c1: C).(csubc g c1 (CHead c (Bind 
x2) (lift h (r (Bind x2) n) x1))))) (\lambda (x: C).(\lambda (H18: (drop h n 
x x3)).(\lambda (H19: (csubc g x c)).(ex_intro2 C (\lambda (c1: C).(drop h (S 
n) c1 (CHead x3 (Bind Void) x4))) (\lambda (c1: C).(csubc g c1 (CHead c (Bind 
x2) (lift h (r (Bind x2) n) x1)))) (CHead x (Bind Void) (lift h n x4)) 
(drop_skip_bind h n x x3 H18 Void x4) (csubc_void g x c H19 x2 H13 (lift h n 
x4) (lift h (r (Bind x2) n) x1)))))) H17))) k H12))) e1 H11)))))))) H10)) 
H9))) t H4))))))))) (drop_gen_skip_l c e2 t h n k H1)))))))) d))))))) c2)).
(* COMMENTS
Initial nodes: 3747
END *)

