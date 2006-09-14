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

set "baseuri" "cic:/matita/LAMBDA-TYPES/Level-1/LambdaDelta/ceqc/props".

include "ceqc/defs.ma".

include "sc3/props.ma".

theorem csubc_refl:
 \forall (g: G).(\forall (c: C).(csubc g c c))
\def
 \lambda (g: G).(\lambda (c: C).(C_ind (\lambda (c0: C).(csubc g c0 c0)) 
(\lambda (n: nat).(csubc_sort g n)) (\lambda (c0: C).(\lambda (H: (csubc g c0 
c0)).(\lambda (k: K).(\lambda (t: T).(csubc_head g c0 c0 H k t))))) c)).

theorem ceqc_sym:
 \forall (g: G).(\forall (c1: C).(\forall (c2: C).((ceqc g c1 c2) \to (ceqc g 
c2 c1))))
\def
 \lambda (g: G).(\lambda (c1: C).(\lambda (c2: C).(\lambda (H: (ceqc g c1 
c2)).(let H0 \def H in (or_ind (csubc g c1 c2) (csubc g c2 c1) (ceqc g c2 c1) 
(\lambda (H1: (csubc g c1 c2)).(or_intror (csubc g c2 c1) (csubc g c1 c2) 
H1)) (\lambda (H1: (csubc g c2 c1)).(or_introl (csubc g c2 c1) (csubc g c1 
c2) H1)) H0))))).

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

theorem drop1_csubc_trans:
 \forall (g: G).(\forall (hds: PList).(\forall (c2: C).(\forall (e2: 
C).((drop1 hds c2 e2) \to (\forall (e1: C).((csubc g e2 e1) \to (ex2 C 
(\lambda (c1: C).(drop1 hds c1 e1)) (\lambda (c1: C).(csubc g c2 c1)))))))))
\def
 \lambda (g: G).(\lambda (hds: PList).(PList_ind (\lambda (p: PList).(\forall 
(c2: C).(\forall (e2: C).((drop1 p c2 e2) \to (\forall (e1: C).((csubc g e2 
e1) \to (ex2 C (\lambda (c1: C).(drop1 p c1 e1)) (\lambda (c1: C).(csubc g c2 
c1))))))))) (\lambda (c2: C).(\lambda (e2: C).(\lambda (H: (drop1 PNil c2 
e2)).(\lambda (e1: C).(\lambda (H0: (csubc g e2 e1)).(let H1 \def (match H in 
drop1 return (\lambda (p: PList).(\lambda (c: C).(\lambda (c0: C).(\lambda 
(_: (drop1 p c c0)).((eq PList p PNil) \to ((eq C c c2) \to ((eq C c0 e2) \to 
(ex2 C (\lambda (c1: C).(drop1 PNil c1 e1)) (\lambda (c1: C).(csubc g c2 
c1)))))))))) with [(drop1_nil c) \Rightarrow (\lambda (_: (eq PList PNil 
PNil)).(\lambda (H2: (eq C c c2)).(\lambda (H3: (eq C c e2)).(eq_ind C c2 
(\lambda (c0: C).((eq C c0 e2) \to (ex2 C (\lambda (c1: C).(drop1 PNil c1 
e1)) (\lambda (c1: C).(csubc g c2 c1))))) (\lambda (H4: (eq C c2 e2)).(eq_ind 
C e2 (\lambda (c0: C).(ex2 C (\lambda (c1: C).(drop1 PNil c1 e1)) (\lambda 
(c1: C).(csubc g c0 c1)))) (let H5 \def (eq_ind_r C e2 (\lambda (c0: 
C).(csubc g c0 e1)) H0 c2 H4) in (eq_ind C c2 (\lambda (c0: C).(ex2 C 
(\lambda (c1: C).(drop1 PNil c1 e1)) (\lambda (c1: C).(csubc g c0 c1)))) 
(ex_intro2 C (\lambda (c1: C).(drop1 PNil c1 e1)) (\lambda (c1: C).(csubc g 
c2 c1)) e1 (drop1_nil e1) H5) e2 H4)) c2 (sym_eq C c2 e2 H4))) c (sym_eq C c 
c2 H2) H3)))) | (drop1_cons c1 c0 h d H1 c3 hds0 H2) \Rightarrow (\lambda 
(H3: (eq PList (PCons h d hds0) PNil)).(\lambda (H4: (eq C c1 c2)).(\lambda 
(H5: (eq C c3 e2)).((let H6 \def (eq_ind PList (PCons h d hds0) (\lambda (e: 
PList).(match e in PList return (\lambda (_: PList).Prop) with [PNil 
\Rightarrow False | (PCons _ _ _) \Rightarrow True])) I PNil H3) in 
(False_ind ((eq C c1 c2) \to ((eq C c3 e2) \to ((drop h d c1 c0) \to ((drop1 
hds0 c0 c3) \to (ex2 C (\lambda (c4: C).(drop1 PNil c4 e1)) (\lambda (c4: 
C).(csubc g c2 c4))))))) H6)) H4 H5 H1 H2))))]) in (H1 (refl_equal PList 
PNil) (refl_equal C c2) (refl_equal C e2)))))))) (\lambda (n: nat).(\lambda 
(n0: nat).(\lambda (p: PList).(\lambda (H: ((\forall (c2: C).(\forall (e2: 
C).((drop1 p c2 e2) \to (\forall (e1: C).((csubc g e2 e1) \to (ex2 C (\lambda 
(c1: C).(drop1 p c1 e1)) (\lambda (c1: C).(csubc g c2 c1)))))))))).(\lambda 
(c2: C).(\lambda (e2: C).(\lambda (H0: (drop1 (PCons n n0 p) c2 e2)).(\lambda 
(e1: C).(\lambda (H1: (csubc g e2 e1)).(let H2 \def (match H0 in drop1 return 
(\lambda (p0: PList).(\lambda (c: C).(\lambda (c0: C).(\lambda (_: (drop1 p0 
c c0)).((eq PList p0 (PCons n n0 p)) \to ((eq C c c2) \to ((eq C c0 e2) \to 
(ex2 C (\lambda (c1: C).(drop1 (PCons n n0 p) c1 e1)) (\lambda (c1: C).(csubc 
g c2 c1)))))))))) with [(drop1_nil c) \Rightarrow (\lambda (H2: (eq PList 
PNil (PCons n n0 p))).(\lambda (H3: (eq C c c2)).(\lambda (H4: (eq C c 
e2)).((let H5 \def (eq_ind PList PNil (\lambda (e: PList).(match e in PList 
return (\lambda (_: PList).Prop) with [PNil \Rightarrow True | (PCons _ _ _) 
\Rightarrow False])) I (PCons n n0 p) H2) in (False_ind ((eq C c c2) \to ((eq 
C c e2) \to (ex2 C (\lambda (c1: C).(drop1 (PCons n n0 p) c1 e1)) (\lambda 
(c1: C).(csubc g c2 c1))))) H5)) H3 H4)))) | (drop1_cons c1 c0 h d H2 c3 hds0 
H3) \Rightarrow (\lambda (H4: (eq PList (PCons h d hds0) (PCons n n0 
p))).(\lambda (H5: (eq C c1 c2)).(\lambda (H6: (eq C c3 e2)).((let H7 \def 
(f_equal PList PList (\lambda (e: PList).(match e in PList return (\lambda 
(_: PList).PList) with [PNil \Rightarrow hds0 | (PCons _ _ p0) \Rightarrow 
p0])) (PCons h d hds0) (PCons n n0 p) H4) in ((let H8 \def (f_equal PList nat 
(\lambda (e: PList).(match e in PList return (\lambda (_: PList).nat) with 
[PNil \Rightarrow d | (PCons _ n1 _) \Rightarrow n1])) (PCons h d hds0) 
(PCons n n0 p) H4) in ((let H9 \def (f_equal PList nat (\lambda (e: 
PList).(match e in PList return (\lambda (_: PList).nat) with [PNil 
\Rightarrow h | (PCons n1 _ _) \Rightarrow n1])) (PCons h d hds0) (PCons n n0 
p) H4) in (eq_ind nat n (\lambda (n1: nat).((eq nat d n0) \to ((eq PList hds0 
p) \to ((eq C c1 c2) \to ((eq C c3 e2) \to ((drop n1 d c1 c0) \to ((drop1 
hds0 c0 c3) \to (ex2 C (\lambda (c4: C).(drop1 (PCons n n0 p) c4 e1)) 
(\lambda (c4: C).(csubc g c2 c4)))))))))) (\lambda (H10: (eq nat d 
n0)).(eq_ind nat n0 (\lambda (n1: nat).((eq PList hds0 p) \to ((eq C c1 c2) 
\to ((eq C c3 e2) \to ((drop n n1 c1 c0) \to ((drop1 hds0 c0 c3) \to (ex2 C 
(\lambda (c4: C).(drop1 (PCons n n0 p) c4 e1)) (\lambda (c4: C).(csubc g c2 
c4))))))))) (\lambda (H11: (eq PList hds0 p)).(eq_ind PList p (\lambda (p0: 
PList).((eq C c1 c2) \to ((eq C c3 e2) \to ((drop n n0 c1 c0) \to ((drop1 p0 
c0 c3) \to (ex2 C (\lambda (c4: C).(drop1 (PCons n n0 p) c4 e1)) (\lambda 
(c4: C).(csubc g c2 c4)))))))) (\lambda (H12: (eq C c1 c2)).(eq_ind C c2 
(\lambda (c: C).((eq C c3 e2) \to ((drop n n0 c c0) \to ((drop1 p c0 c3) \to 
(ex2 C (\lambda (c4: C).(drop1 (PCons n n0 p) c4 e1)) (\lambda (c4: C).(csubc 
g c2 c4))))))) (\lambda (H13: (eq C c3 e2)).(eq_ind C e2 (\lambda (c: 
C).((drop n n0 c2 c0) \to ((drop1 p c0 c) \to (ex2 C (\lambda (c4: C).(drop1 
(PCons n n0 p) c4 e1)) (\lambda (c4: C).(csubc g c2 c4)))))) (\lambda (H14: 
(drop n n0 c2 c0)).(\lambda (H15: (drop1 p c0 e2)).(let H_x \def (H c0 e2 H15 
e1 H1) in (let H16 \def H_x in (ex2_ind C (\lambda (c4: C).(drop1 p c4 e1)) 
(\lambda (c4: C).(csubc g c0 c4)) (ex2 C (\lambda (c4: C).(drop1 (PCons n n0 
p) c4 e1)) (\lambda (c4: C).(csubc g c2 c4))) (\lambda (x: C).(\lambda (H17: 
(drop1 p x e1)).(\lambda (H18: (csubc g c0 x)).(let H_x0 \def 
(drop_csubc_trans g c2 c0 n0 n H14 x H18) in (let H19 \def H_x0 in (ex2_ind C 
(\lambda (c4: C).(drop n n0 c4 x)) (\lambda (c4: C).(csubc g c2 c4)) (ex2 C 
(\lambda (c4: C).(drop1 (PCons n n0 p) c4 e1)) (\lambda (c4: C).(csubc g c2 
c4))) (\lambda (x0: C).(\lambda (H20: (drop n n0 x0 x)).(\lambda (H21: (csubc 
g c2 x0)).(ex_intro2 C (\lambda (c4: C).(drop1 (PCons n n0 p) c4 e1)) 
(\lambda (c4: C).(csubc g c2 c4)) x0 (drop1_cons x0 x n n0 H20 e1 p H17) 
H21)))) H19)))))) H16))))) c3 (sym_eq C c3 e2 H13))) c1 (sym_eq C c1 c2 
H12))) hds0 (sym_eq PList hds0 p H11))) d (sym_eq nat d n0 H10))) h (sym_eq 
nat h n H9))) H8)) H7)) H5 H6 H2 H3))))]) in (H2 (refl_equal PList (PCons n 
n0 p)) (refl_equal C c2) (refl_equal C e2)))))))))))) hds)).

theorem csubc_drop1_conf_rev:
 \forall (g: G).(\forall (hds: PList).(\forall (c2: C).(\forall (e2: 
C).((drop1 hds c2 e2) \to (\forall (e1: C).((csubc g e1 e2) \to (ex2 C 
(\lambda (c1: C).(drop1 hds c1 e1)) (\lambda (c1: C).(csubc g c1 c2)))))))))
\def
 \lambda (g: G).(\lambda (hds: PList).(PList_ind (\lambda (p: PList).(\forall 
(c2: C).(\forall (e2: C).((drop1 p c2 e2) \to (\forall (e1: C).((csubc g e1 
e2) \to (ex2 C (\lambda (c1: C).(drop1 p c1 e1)) (\lambda (c1: C).(csubc g c1 
c2))))))))) (\lambda (c2: C).(\lambda (e2: C).(\lambda (H: (drop1 PNil c2 
e2)).(\lambda (e1: C).(\lambda (H0: (csubc g e1 e2)).(let H1 \def (match H in 
drop1 return (\lambda (p: PList).(\lambda (c: C).(\lambda (c0: C).(\lambda 
(_: (drop1 p c c0)).((eq PList p PNil) \to ((eq C c c2) \to ((eq C c0 e2) \to 
(ex2 C (\lambda (c1: C).(drop1 PNil c1 e1)) (\lambda (c1: C).(csubc g c1 
c2)))))))))) with [(drop1_nil c) \Rightarrow (\lambda (_: (eq PList PNil 
PNil)).(\lambda (H2: (eq C c c2)).(\lambda (H3: (eq C c e2)).(eq_ind C c2 
(\lambda (c0: C).((eq C c0 e2) \to (ex2 C (\lambda (c1: C).(drop1 PNil c1 
e1)) (\lambda (c1: C).(csubc g c1 c2))))) (\lambda (H4: (eq C c2 e2)).(eq_ind 
C e2 (\lambda (c0: C).(ex2 C (\lambda (c1: C).(drop1 PNil c1 e1)) (\lambda 
(c1: C).(csubc g c1 c0)))) (let H5 \def (eq_ind_r C e2 (\lambda (c0: 
C).(csubc g e1 c0)) H0 c2 H4) in (eq_ind C c2 (\lambda (c0: C).(ex2 C 
(\lambda (c1: C).(drop1 PNil c1 e1)) (\lambda (c1: C).(csubc g c1 c0)))) 
(ex_intro2 C (\lambda (c1: C).(drop1 PNil c1 e1)) (\lambda (c1: C).(csubc g 
c1 c2)) e1 (drop1_nil e1) H5) e2 H4)) c2 (sym_eq C c2 e2 H4))) c (sym_eq C c 
c2 H2) H3)))) | (drop1_cons c1 c0 h d H1 c3 hds0 H2) \Rightarrow (\lambda 
(H3: (eq PList (PCons h d hds0) PNil)).(\lambda (H4: (eq C c1 c2)).(\lambda 
(H5: (eq C c3 e2)).((let H6 \def (eq_ind PList (PCons h d hds0) (\lambda (e: 
PList).(match e in PList return (\lambda (_: PList).Prop) with [PNil 
\Rightarrow False | (PCons _ _ _) \Rightarrow True])) I PNil H3) in 
(False_ind ((eq C c1 c2) \to ((eq C c3 e2) \to ((drop h d c1 c0) \to ((drop1 
hds0 c0 c3) \to (ex2 C (\lambda (c4: C).(drop1 PNil c4 e1)) (\lambda (c4: 
C).(csubc g c4 c2))))))) H6)) H4 H5 H1 H2))))]) in (H1 (refl_equal PList 
PNil) (refl_equal C c2) (refl_equal C e2)))))))) (\lambda (n: nat).(\lambda 
(n0: nat).(\lambda (p: PList).(\lambda (H: ((\forall (c2: C).(\forall (e2: 
C).((drop1 p c2 e2) \to (\forall (e1: C).((csubc g e1 e2) \to (ex2 C (\lambda 
(c1: C).(drop1 p c1 e1)) (\lambda (c1: C).(csubc g c1 c2)))))))))).(\lambda 
(c2: C).(\lambda (e2: C).(\lambda (H0: (drop1 (PCons n n0 p) c2 e2)).(\lambda 
(e1: C).(\lambda (H1: (csubc g e1 e2)).(let H2 \def (match H0 in drop1 return 
(\lambda (p0: PList).(\lambda (c: C).(\lambda (c0: C).(\lambda (_: (drop1 p0 
c c0)).((eq PList p0 (PCons n n0 p)) \to ((eq C c c2) \to ((eq C c0 e2) \to 
(ex2 C (\lambda (c1: C).(drop1 (PCons n n0 p) c1 e1)) (\lambda (c1: C).(csubc 
g c1 c2)))))))))) with [(drop1_nil c) \Rightarrow (\lambda (H2: (eq PList 
PNil (PCons n n0 p))).(\lambda (H3: (eq C c c2)).(\lambda (H4: (eq C c 
e2)).((let H5 \def (eq_ind PList PNil (\lambda (e: PList).(match e in PList 
return (\lambda (_: PList).Prop) with [PNil \Rightarrow True | (PCons _ _ _) 
\Rightarrow False])) I (PCons n n0 p) H2) in (False_ind ((eq C c c2) \to ((eq 
C c e2) \to (ex2 C (\lambda (c1: C).(drop1 (PCons n n0 p) c1 e1)) (\lambda 
(c1: C).(csubc g c1 c2))))) H5)) H3 H4)))) | (drop1_cons c1 c0 h d H2 c3 hds0 
H3) \Rightarrow (\lambda (H4: (eq PList (PCons h d hds0) (PCons n n0 
p))).(\lambda (H5: (eq C c1 c2)).(\lambda (H6: (eq C c3 e2)).((let H7 \def 
(f_equal PList PList (\lambda (e: PList).(match e in PList return (\lambda 
(_: PList).PList) with [PNil \Rightarrow hds0 | (PCons _ _ p0) \Rightarrow 
p0])) (PCons h d hds0) (PCons n n0 p) H4) in ((let H8 \def (f_equal PList nat 
(\lambda (e: PList).(match e in PList return (\lambda (_: PList).nat) with 
[PNil \Rightarrow d | (PCons _ n1 _) \Rightarrow n1])) (PCons h d hds0) 
(PCons n n0 p) H4) in ((let H9 \def (f_equal PList nat (\lambda (e: 
PList).(match e in PList return (\lambda (_: PList).nat) with [PNil 
\Rightarrow h | (PCons n1 _ _) \Rightarrow n1])) (PCons h d hds0) (PCons n n0 
p) H4) in (eq_ind nat n (\lambda (n1: nat).((eq nat d n0) \to ((eq PList hds0 
p) \to ((eq C c1 c2) \to ((eq C c3 e2) \to ((drop n1 d c1 c0) \to ((drop1 
hds0 c0 c3) \to (ex2 C (\lambda (c4: C).(drop1 (PCons n n0 p) c4 e1)) 
(\lambda (c4: C).(csubc g c4 c2)))))))))) (\lambda (H10: (eq nat d 
n0)).(eq_ind nat n0 (\lambda (n1: nat).((eq PList hds0 p) \to ((eq C c1 c2) 
\to ((eq C c3 e2) \to ((drop n n1 c1 c0) \to ((drop1 hds0 c0 c3) \to (ex2 C 
(\lambda (c4: C).(drop1 (PCons n n0 p) c4 e1)) (\lambda (c4: C).(csubc g c4 
c2))))))))) (\lambda (H11: (eq PList hds0 p)).(eq_ind PList p (\lambda (p0: 
PList).((eq C c1 c2) \to ((eq C c3 e2) \to ((drop n n0 c1 c0) \to ((drop1 p0 
c0 c3) \to (ex2 C (\lambda (c4: C).(drop1 (PCons n n0 p) c4 e1)) (\lambda 
(c4: C).(csubc g c4 c2)))))))) (\lambda (H12: (eq C c1 c2)).(eq_ind C c2 
(\lambda (c: C).((eq C c3 e2) \to ((drop n n0 c c0) \to ((drop1 p c0 c3) \to 
(ex2 C (\lambda (c4: C).(drop1 (PCons n n0 p) c4 e1)) (\lambda (c4: C).(csubc 
g c4 c2))))))) (\lambda (H13: (eq C c3 e2)).(eq_ind C e2 (\lambda (c: 
C).((drop n n0 c2 c0) \to ((drop1 p c0 c) \to (ex2 C (\lambda (c4: C).(drop1 
(PCons n n0 p) c4 e1)) (\lambda (c4: C).(csubc g c4 c2)))))) (\lambda (H14: 
(drop n n0 c2 c0)).(\lambda (H15: (drop1 p c0 e2)).(let H_x \def (H c0 e2 H15 
e1 H1) in (let H16 \def H_x in (ex2_ind C (\lambda (c4: C).(drop1 p c4 e1)) 
(\lambda (c4: C).(csubc g c4 c0)) (ex2 C (\lambda (c4: C).(drop1 (PCons n n0 
p) c4 e1)) (\lambda (c4: C).(csubc g c4 c2))) (\lambda (x: C).(\lambda (H17: 
(drop1 p x e1)).(\lambda (H18: (csubc g x c0)).(let H_x0 \def 
(csubc_drop_conf_rev g c2 c0 n0 n H14 x H18) in (let H19 \def H_x0 in 
(ex2_ind C (\lambda (c4: C).(drop n n0 c4 x)) (\lambda (c4: C).(csubc g c4 
c2)) (ex2 C (\lambda (c4: C).(drop1 (PCons n n0 p) c4 e1)) (\lambda (c4: 
C).(csubc g c4 c2))) (\lambda (x0: C).(\lambda (H20: (drop n n0 x0 
x)).(\lambda (H21: (csubc g x0 c2)).(ex_intro2 C (\lambda (c4: C).(drop1 
(PCons n n0 p) c4 e1)) (\lambda (c4: C).(csubc g c4 c2)) x0 (drop1_cons x0 x 
n n0 H20 e1 p H17) H21)))) H19)))))) H16))))) c3 (sym_eq C c3 e2 H13))) c1 
(sym_eq C c1 c2 H12))) hds0 (sym_eq PList hds0 p H11))) d (sym_eq nat d n0 
H10))) h (sym_eq nat h n H9))) H8)) H7)) H5 H6 H2 H3))))]) in (H2 (refl_equal 
PList (PCons n n0 p)) (refl_equal C c2) (refl_equal C e2)))))))))))) hds)).

theorem drop1_ceqc_trans:
 \forall (g: G).(\forall (hds: PList).(\forall (c2: C).(\forall (e2: 
C).((drop1 hds c2 e2) \to (\forall (e1: C).((ceqc g e2 e1) \to (ex2 C 
(\lambda (c1: C).(drop1 hds c1 e1)) (\lambda (c1: C).(ceqc g c2 c1)))))))))
\def
 \lambda (g: G).(\lambda (hds: PList).(\lambda (c2: C).(\lambda (e2: 
C).(\lambda (H: (drop1 hds c2 e2)).(\lambda (e1: C).(\lambda (H0: (ceqc g e2 
e1)).(let H1 \def H0 in (or_ind (csubc g e2 e1) (csubc g e1 e2) (ex2 C 
(\lambda (c1: C).(drop1 hds c1 e1)) (\lambda (c1: C).(ceqc g c2 c1))) 
(\lambda (H2: (csubc g e2 e1)).(let H_x \def (drop1_csubc_trans g hds c2 e2 H 
e1 H2) in (let H3 \def H_x in (ex2_ind C (\lambda (c1: C).(drop1 hds c1 e1)) 
(\lambda (c1: C).(csubc g c2 c1)) (ex2 C (\lambda (c1: C).(drop1 hds c1 e1)) 
(\lambda (c1: C).(ceqc g c2 c1))) (\lambda (x: C).(\lambda (H4: (drop1 hds x 
e1)).(\lambda (H5: (csubc g c2 x)).(ex_intro2 C (\lambda (c1: C).(drop1 hds 
c1 e1)) (\lambda (c1: C).(ceqc g c2 c1)) x H4 (or_introl (csubc g c2 x) 
(csubc g x c2) H5))))) H3)))) (\lambda (H2: (csubc g e1 e2)).(let H_x \def 
(csubc_drop1_conf_rev g hds c2 e2 H e1 H2) in (let H3 \def H_x in (ex2_ind C 
(\lambda (c1: C).(drop1 hds c1 e1)) (\lambda (c1: C).(csubc g c1 c2)) (ex2 C 
(\lambda (c1: C).(drop1 hds c1 e1)) (\lambda (c1: C).(ceqc g c2 c1))) 
(\lambda (x: C).(\lambda (H4: (drop1 hds x e1)).(\lambda (H5: (csubc g x 
c2)).(ex_intro2 C (\lambda (c1: C).(drop1 hds c1 e1)) (\lambda (c1: C).(ceqc 
g c2 c1)) x H4 (or_intror (csubc g c2 x) (csubc g x c2) H5))))) H3)))) 
H1)))))))).

axiom sc3_ceqc_trans:
 \forall (g: G).(\forall (a: A).(\forall (vs: TList).(\forall (c1: 
C).(\forall (t: T).((sc3 g a c1 (THeads (Flat Appl) vs t)) \to (\forall (c2: 
C).((ceqc g c2 c1) \to (sc3 g a c2 (THeads (Flat Appl) vs t)))))))))
.

