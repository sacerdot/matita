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

include "Basic-1/csuba/fwd.ma".

include "Basic-1/drop/fwd.ma".

theorem csuba_drop_abbr:
 \forall (i: nat).(\forall (c1: C).(\forall (d1: C).(\forall (u: T).((drop i 
O c1 (CHead d1 (Bind Abbr) u)) \to (\forall (g: G).(\forall (c2: C).((csuba g 
c1 c2) \to (ex2 C (\lambda (d2: C).(drop i O c2 (CHead d2 (Bind Abbr) u))) 
(\lambda (d2: C).(csuba g d1 d2))))))))))
\def
 \lambda (i: nat).(nat_ind (\lambda (n: nat).(\forall (c1: C).(\forall (d1: 
C).(\forall (u: T).((drop n O c1 (CHead d1 (Bind Abbr) u)) \to (\forall (g: 
G).(\forall (c2: C).((csuba g c1 c2) \to (ex2 C (\lambda (d2: C).(drop n O c2 
(CHead d2 (Bind Abbr) u))) (\lambda (d2: C).(csuba g d1 d2))))))))))) 
(\lambda (c1: C).(\lambda (d1: C).(\lambda (u: T).(\lambda (H: (drop O O c1 
(CHead d1 (Bind Abbr) u))).(\lambda (g: G).(\lambda (c2: C).(\lambda (H0: 
(csuba g c1 c2)).(let H1 \def (eq_ind C c1 (\lambda (c: C).(csuba g c c2)) H0 
(CHead d1 (Bind Abbr) u) (drop_gen_refl c1 (CHead d1 (Bind Abbr) u) H)) in 
(let H_x \def (csuba_gen_abbr g d1 c2 u H1) in (let H2 \def H_x in (ex2_ind C 
(\lambda (d2: C).(eq C c2 (CHead d2 (Bind Abbr) u))) (\lambda (d2: C).(csuba 
g d1 d2)) (ex2 C (\lambda (d2: C).(drop O O c2 (CHead d2 (Bind Abbr) u))) 
(\lambda (d2: C).(csuba g d1 d2))) (\lambda (x: C).(\lambda (H3: (eq C c2 
(CHead x (Bind Abbr) u))).(\lambda (H4: (csuba g d1 x)).(eq_ind_r C (CHead x 
(Bind Abbr) u) (\lambda (c: C).(ex2 C (\lambda (d2: C).(drop O O c (CHead d2 
(Bind Abbr) u))) (\lambda (d2: C).(csuba g d1 d2)))) (ex_intro2 C (\lambda 
(d2: C).(drop O O (CHead x (Bind Abbr) u) (CHead d2 (Bind Abbr) u))) (\lambda 
(d2: C).(csuba g d1 d2)) x (drop_refl (CHead x (Bind Abbr) u)) H4) c2 H3)))) 
H2))))))))))) (\lambda (n: nat).(\lambda (H: ((\forall (c1: C).(\forall (d1: 
C).(\forall (u: T).((drop n O c1 (CHead d1 (Bind Abbr) u)) \to (\forall (g: 
G).(\forall (c2: C).((csuba g c1 c2) \to (ex2 C (\lambda (d2: C).(drop n O c2 
(CHead d2 (Bind Abbr) u))) (\lambda (d2: C).(csuba g d1 
d2)))))))))))).(\lambda (c1: C).(C_ind (\lambda (c: C).(\forall (d1: 
C).(\forall (u: T).((drop (S n) O c (CHead d1 (Bind Abbr) u)) \to (\forall 
(g: G).(\forall (c2: C).((csuba g c c2) \to (ex2 C (\lambda (d2: C).(drop (S 
n) O c2 (CHead d2 (Bind Abbr) u))) (\lambda (d2: C).(csuba g d1 d2)))))))))) 
(\lambda (n0: nat).(\lambda (d1: C).(\lambda (u: T).(\lambda (H0: (drop (S n) 
O (CSort n0) (CHead d1 (Bind Abbr) u))).(\lambda (g: G).(\lambda (c2: 
C).(\lambda (_: (csuba g (CSort n0) c2)).(and3_ind (eq C (CHead d1 (Bind 
Abbr) u) (CSort n0)) (eq nat (S n) O) (eq nat O O) (ex2 C (\lambda (d2: 
C).(drop (S n) O c2 (CHead d2 (Bind Abbr) u))) (\lambda (d2: C).(csuba g d1 
d2))) (\lambda (_: (eq C (CHead d1 (Bind Abbr) u) (CSort n0))).(\lambda (H3: 
(eq nat (S n) O)).(\lambda (_: (eq nat O O)).(let H5 \def (eq_ind nat (S n) 
(\lambda (ee: nat).(match ee in nat return (\lambda (_: nat).Prop) with [O 
\Rightarrow False | (S _) \Rightarrow True])) I O H3) in (False_ind (ex2 C 
(\lambda (d2: C).(drop (S n) O c2 (CHead d2 (Bind Abbr) u))) (\lambda (d2: 
C).(csuba g d1 d2))) H5))))) (drop_gen_sort n0 (S n) O (CHead d1 (Bind Abbr) 
u) H0))))))))) (\lambda (c: C).(\lambda (H0: ((\forall (d1: C).(\forall (u: 
T).((drop (S n) O c (CHead d1 (Bind Abbr) u)) \to (\forall (g: G).(\forall 
(c2: C).((csuba g c c2) \to (ex2 C (\lambda (d2: C).(drop (S n) O c2 (CHead 
d2 (Bind Abbr) u))) (\lambda (d2: C).(csuba g d1 d2))))))))))).(\lambda (k: 
K).(\lambda (t: T).(\lambda (d1: C).(\lambda (u: T).(\lambda (H1: (drop (S n) 
O (CHead c k t) (CHead d1 (Bind Abbr) u))).(\lambda (g: G).(\lambda (c2: 
C).(\lambda (H2: (csuba g (CHead c k t) c2)).(K_ind (\lambda (k0: K).((csuba 
g (CHead c k0 t) c2) \to ((drop (r k0 n) O c (CHead d1 (Bind Abbr) u)) \to 
(ex2 C (\lambda (d2: C).(drop (S n) O c2 (CHead d2 (Bind Abbr) u))) (\lambda 
(d2: C).(csuba g d1 d2)))))) (\lambda (b: B).(\lambda (H3: (csuba g (CHead c 
(Bind b) t) c2)).(\lambda (H4: (drop (r (Bind b) n) O c (CHead d1 (Bind Abbr) 
u))).(B_ind (\lambda (b0: B).((csuba g (CHead c (Bind b0) t) c2) \to ((drop 
(r (Bind b0) n) O c (CHead d1 (Bind Abbr) u)) \to (ex2 C (\lambda (d2: 
C).(drop (S n) O c2 (CHead d2 (Bind Abbr) u))) (\lambda (d2: C).(csuba g d1 
d2)))))) (\lambda (H5: (csuba g (CHead c (Bind Abbr) t) c2)).(\lambda (H6: 
(drop (r (Bind Abbr) n) O c (CHead d1 (Bind Abbr) u))).(let H_x \def 
(csuba_gen_abbr g c c2 t H5) in (let H7 \def H_x in (ex2_ind C (\lambda (d2: 
C).(eq C c2 (CHead d2 (Bind Abbr) t))) (\lambda (d2: C).(csuba g c d2)) (ex2 
C (\lambda (d2: C).(drop (S n) O c2 (CHead d2 (Bind Abbr) u))) (\lambda (d2: 
C).(csuba g d1 d2))) (\lambda (x: C).(\lambda (H8: (eq C c2 (CHead x (Bind 
Abbr) t))).(\lambda (H9: (csuba g c x)).(eq_ind_r C (CHead x (Bind Abbr) t) 
(\lambda (c0: C).(ex2 C (\lambda (d2: C).(drop (S n) O c0 (CHead d2 (Bind 
Abbr) u))) (\lambda (d2: C).(csuba g d1 d2)))) (let H10 \def (H c d1 u H6 g x 
H9) in (ex2_ind C (\lambda (d2: C).(drop n O x (CHead d2 (Bind Abbr) u))) 
(\lambda (d2: C).(csuba g d1 d2)) (ex2 C (\lambda (d2: C).(drop (S n) O 
(CHead x (Bind Abbr) t) (CHead d2 (Bind Abbr) u))) (\lambda (d2: C).(csuba g 
d1 d2))) (\lambda (x0: C).(\lambda (H11: (drop n O x (CHead x0 (Bind Abbr) 
u))).(\lambda (H12: (csuba g d1 x0)).(let H13 \def (refl_equal nat (r (Bind 
Abbr) n)) in (let H14 \def (eq_ind nat n (\lambda (n0: nat).(drop n0 O x 
(CHead x0 (Bind Abbr) u))) H11 (r (Bind Abbr) n) H13) in (ex_intro2 C 
(\lambda (d2: C).(drop (S n) O (CHead x (Bind Abbr) t) (CHead d2 (Bind Abbr) 
u))) (\lambda (d2: C).(csuba g d1 d2)) x0 (drop_drop (Bind Abbr) n x (CHead 
x0 (Bind Abbr) u) H14 t) H12)))))) H10)) c2 H8)))) H7))))) (\lambda (H5: 
(csuba g (CHead c (Bind Abst) t) c2)).(\lambda (H6: (drop (r (Bind Abst) n) O 
c (CHead d1 (Bind Abbr) u))).(let H_x \def (csuba_gen_abst g c c2 t H5) in 
(let H7 \def H_x in (or_ind (ex2 C (\lambda (d2: C).(eq C c2 (CHead d2 (Bind 
Abst) t))) (\lambda (d2: C).(csuba g c d2))) (ex4_3 C T A (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (_: A).(eq C c2 (CHead d2 (Bind Abbr) u2))))) 
(\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g c d2)))) (\lambda 
(_: C).(\lambda (_: T).(\lambda (a: A).(arity g c t (asucc g a))))) (\lambda 
(d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 a))))) (ex2 C 
(\lambda (d2: C).(drop (S n) O c2 (CHead d2 (Bind Abbr) u))) (\lambda (d2: 
C).(csuba g d1 d2))) (\lambda (H8: (ex2 C (\lambda (d2: C).(eq C c2 (CHead d2 
(Bind Abst) t))) (\lambda (d2: C).(csuba g c d2)))).(ex2_ind C (\lambda (d2: 
C).(eq C c2 (CHead d2 (Bind Abst) t))) (\lambda (d2: C).(csuba g c d2)) (ex2 
C (\lambda (d2: C).(drop (S n) O c2 (CHead d2 (Bind Abbr) u))) (\lambda (d2: 
C).(csuba g d1 d2))) (\lambda (x: C).(\lambda (H9: (eq C c2 (CHead x (Bind 
Abst) t))).(\lambda (H10: (csuba g c x)).(eq_ind_r C (CHead x (Bind Abst) t) 
(\lambda (c0: C).(ex2 C (\lambda (d2: C).(drop (S n) O c0 (CHead d2 (Bind 
Abbr) u))) (\lambda (d2: C).(csuba g d1 d2)))) (let H11 \def (H c d1 u H6 g x 
H10) in (ex2_ind C (\lambda (d2: C).(drop n O x (CHead d2 (Bind Abbr) u))) 
(\lambda (d2: C).(csuba g d1 d2)) (ex2 C (\lambda (d2: C).(drop (S n) O 
(CHead x (Bind Abst) t) (CHead d2 (Bind Abbr) u))) (\lambda (d2: C).(csuba g 
d1 d2))) (\lambda (x0: C).(\lambda (H12: (drop n O x (CHead x0 (Bind Abbr) 
u))).(\lambda (H13: (csuba g d1 x0)).(let H14 \def (refl_equal nat (r (Bind 
Abbr) n)) in (let H15 \def (eq_ind nat n (\lambda (n0: nat).(drop n0 O x 
(CHead x0 (Bind Abbr) u))) H12 (r (Bind Abbr) n) H14) in (ex_intro2 C 
(\lambda (d2: C).(drop (S n) O (CHead x (Bind Abst) t) (CHead d2 (Bind Abbr) 
u))) (\lambda (d2: C).(csuba g d1 d2)) x0 (drop_drop (Bind Abst) n x (CHead 
x0 (Bind Abbr) u) H15 t) H13)))))) H11)) c2 H9)))) H8)) (\lambda (H8: (ex4_3 
C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(eq C c2 (CHead d2 
(Bind Abbr) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g 
c d2)))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g c t (asucc 
g a))))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 
a)))))).(ex4_3_ind C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: 
A).(eq C c2 (CHead d2 (Bind Abbr) u2))))) (\lambda (d2: C).(\lambda (_: 
T).(\lambda (_: A).(csuba g c d2)))) (\lambda (_: C).(\lambda (_: T).(\lambda 
(a: A).(arity g c t (asucc g a))))) (\lambda (d2: C).(\lambda (u2: 
T).(\lambda (a: A).(arity g d2 u2 a)))) (ex2 C (\lambda (d2: C).(drop (S n) O 
c2 (CHead d2 (Bind Abbr) u))) (\lambda (d2: C).(csuba g d1 d2))) (\lambda 
(x0: C).(\lambda (x1: T).(\lambda (x2: A).(\lambda (H9: (eq C c2 (CHead x0 
(Bind Abbr) x1))).(\lambda (H10: (csuba g c x0)).(\lambda (_: (arity g c t 
(asucc g x2))).(\lambda (_: (arity g x0 x1 x2)).(eq_ind_r C (CHead x0 (Bind 
Abbr) x1) (\lambda (c0: C).(ex2 C (\lambda (d2: C).(drop (S n) O c0 (CHead d2 
(Bind Abbr) u))) (\lambda (d2: C).(csuba g d1 d2)))) (let H13 \def (H c d1 u 
H6 g x0 H10) in (ex2_ind C (\lambda (d2: C).(drop n O x0 (CHead d2 (Bind 
Abbr) u))) (\lambda (d2: C).(csuba g d1 d2)) (ex2 C (\lambda (d2: C).(drop (S 
n) O (CHead x0 (Bind Abbr) x1) (CHead d2 (Bind Abbr) u))) (\lambda (d2: 
C).(csuba g d1 d2))) (\lambda (x: C).(\lambda (H14: (drop n O x0 (CHead x 
(Bind Abbr) u))).(\lambda (H15: (csuba g d1 x)).(let H16 \def (refl_equal nat 
(r (Bind Abbr) n)) in (let H17 \def (eq_ind nat n (\lambda (n0: nat).(drop n0 
O x0 (CHead x (Bind Abbr) u))) H14 (r (Bind Abbr) n) H16) in (ex_intro2 C 
(\lambda (d2: C).(drop (S n) O (CHead x0 (Bind Abbr) x1) (CHead d2 (Bind 
Abbr) u))) (\lambda (d2: C).(csuba g d1 d2)) x (drop_drop (Bind Abbr) n x0 
(CHead x (Bind Abbr) u) H17 x1) H15)))))) H13)) c2 H9)))))))) H8)) H7))))) 
(\lambda (H5: (csuba g (CHead c (Bind Void) t) c2)).(\lambda (H6: (drop (r 
(Bind Void) n) O c (CHead d1 (Bind Abbr) u))).(let H_x \def (csuba_gen_void g 
c c2 t H5) in (let H7 \def H_x in (ex2_3_ind B C T (\lambda (b0: B).(\lambda 
(d2: C).(\lambda (u2: T).(eq C c2 (CHead d2 (Bind b0) u2))))) (\lambda (_: 
B).(\lambda (d2: C).(\lambda (_: T).(csuba g c d2)))) (ex2 C (\lambda (d2: 
C).(drop (S n) O c2 (CHead d2 (Bind Abbr) u))) (\lambda (d2: C).(csuba g d1 
d2))) (\lambda (x0: B).(\lambda (x1: C).(\lambda (x2: T).(\lambda (H8: (eq C 
c2 (CHead x1 (Bind x0) x2))).(\lambda (H9: (csuba g c x1)).(eq_ind_r C (CHead 
x1 (Bind x0) x2) (\lambda (c0: C).(ex2 C (\lambda (d2: C).(drop (S n) O c0 
(CHead d2 (Bind Abbr) u))) (\lambda (d2: C).(csuba g d1 d2)))) (let H10 \def 
(H c d1 u H6 g x1 H9) in (ex2_ind C (\lambda (d2: C).(drop n O x1 (CHead d2 
(Bind Abbr) u))) (\lambda (d2: C).(csuba g d1 d2)) (ex2 C (\lambda (d2: 
C).(drop (S n) O (CHead x1 (Bind x0) x2) (CHead d2 (Bind Abbr) u))) (\lambda 
(d2: C).(csuba g d1 d2))) (\lambda (x: C).(\lambda (H11: (drop n O x1 (CHead 
x (Bind Abbr) u))).(\lambda (H12: (csuba g d1 x)).(let H13 \def (refl_equal 
nat (r (Bind Abbr) n)) in (let H14 \def (eq_ind nat n (\lambda (n0: 
nat).(drop n0 O x1 (CHead x (Bind Abbr) u))) H11 (r (Bind Abbr) n) H13) in 
(ex_intro2 C (\lambda (d2: C).(drop (S n) O (CHead x1 (Bind x0) x2) (CHead d2 
(Bind Abbr) u))) (\lambda (d2: C).(csuba g d1 d2)) x (drop_drop (Bind x0) n 
x1 (CHead x (Bind Abbr) u) H14 x2) H12)))))) H10)) c2 H8)))))) H7))))) b H3 
H4)))) (\lambda (f: F).(\lambda (H3: (csuba g (CHead c (Flat f) t) 
c2)).(\lambda (H4: (drop (r (Flat f) n) O c (CHead d1 (Bind Abbr) u))).(let 
H_x \def (csuba_gen_flat g c c2 t f H3) in (let H5 \def H_x in (ex2_2_ind C T 
(\lambda (d2: C).(\lambda (u2: T).(eq C c2 (CHead d2 (Flat f) u2)))) (\lambda 
(d2: C).(\lambda (_: T).(csuba g c d2))) (ex2 C (\lambda (d2: C).(drop (S n) 
O c2 (CHead d2 (Bind Abbr) u))) (\lambda (d2: C).(csuba g d1 d2))) (\lambda 
(x0: C).(\lambda (x1: T).(\lambda (H6: (eq C c2 (CHead x0 (Flat f) 
x1))).(\lambda (H7: (csuba g c x0)).(eq_ind_r C (CHead x0 (Flat f) x1) 
(\lambda (c0: C).(ex2 C (\lambda (d2: C).(drop (S n) O c0 (CHead d2 (Bind 
Abbr) u))) (\lambda (d2: C).(csuba g d1 d2)))) (let H8 \def (H0 d1 u H4 g x0 
H7) in (ex2_ind C (\lambda (d2: C).(drop (S n) O x0 (CHead d2 (Bind Abbr) 
u))) (\lambda (d2: C).(csuba g d1 d2)) (ex2 C (\lambda (d2: C).(drop (S n) O 
(CHead x0 (Flat f) x1) (CHead d2 (Bind Abbr) u))) (\lambda (d2: C).(csuba g 
d1 d2))) (\lambda (x: C).(\lambda (H9: (drop (S n) O x0 (CHead x (Bind Abbr) 
u))).(\lambda (H10: (csuba g d1 x)).(ex_intro2 C (\lambda (d2: C).(drop (S n) 
O (CHead x0 (Flat f) x1) (CHead d2 (Bind Abbr) u))) (\lambda (d2: C).(csuba g 
d1 d2)) x (drop_drop (Flat f) n x0 (CHead x (Bind Abbr) u) H9 x1) H10)))) 
H8)) c2 H6))))) H5)))))) k H2 (drop_gen_drop k c (CHead d1 (Bind Abbr) u) t n 
H1)))))))))))) c1)))) i).
(* COMMENTS
Initial nodes: 3648
END *)

theorem csuba_drop_abst:
 \forall (i: nat).(\forall (c1: C).(\forall (d1: C).(\forall (u1: T).((drop i 
O c1 (CHead d1 (Bind Abst) u1)) \to (\forall (g: G).(\forall (c2: C).((csuba 
g c1 c2) \to (or (ex2 C (\lambda (d2: C).(drop i O c2 (CHead d2 (Bind Abst) 
u1))) (\lambda (d2: C).(csuba g d1 d2))) (ex4_3 C T A (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (_: A).(drop i O c2 (CHead d2 (Bind Abbr) 
u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d1 d2)))) 
(\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 (asucc g 
a))))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 
a)))))))))))))
\def
 \lambda (i: nat).(nat_ind (\lambda (n: nat).(\forall (c1: C).(\forall (d1: 
C).(\forall (u1: T).((drop n O c1 (CHead d1 (Bind Abst) u1)) \to (\forall (g: 
G).(\forall (c2: C).((csuba g c1 c2) \to (or (ex2 C (\lambda (d2: C).(drop n 
O c2 (CHead d2 (Bind Abst) u1))) (\lambda (d2: C).(csuba g d1 d2))) (ex4_3 C 
T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(drop n O c2 (CHead d2 
(Bind Abbr) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g 
d1 d2)))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 
(asucc g a))))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 
u2 a)))))))))))))) (\lambda (c1: C).(\lambda (d1: C).(\lambda (u1: 
T).(\lambda (H: (drop O O c1 (CHead d1 (Bind Abst) u1))).(\lambda (g: 
G).(\lambda (c2: C).(\lambda (H0: (csuba g c1 c2)).(let H1 \def (eq_ind C c1 
(\lambda (c: C).(csuba g c c2)) H0 (CHead d1 (Bind Abst) u1) (drop_gen_refl 
c1 (CHead d1 (Bind Abst) u1) H)) in (let H_x \def (csuba_gen_abst g d1 c2 u1 
H1) in (let H2 \def H_x in (or_ind (ex2 C (\lambda (d2: C).(eq C c2 (CHead d2 
(Bind Abst) u1))) (\lambda (d2: C).(csuba g d1 d2))) (ex4_3 C T A (\lambda 
(d2: C).(\lambda (u2: T).(\lambda (_: A).(eq C c2 (CHead d2 (Bind Abbr) 
u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d1 d2)))) 
(\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 (asucc g 
a))))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 
a))))) (or (ex2 C (\lambda (d2: C).(drop O O c2 (CHead d2 (Bind Abst) u1))) 
(\lambda (d2: C).(csuba g d1 d2))) (ex4_3 C T A (\lambda (d2: C).(\lambda 
(u2: T).(\lambda (_: A).(drop O O c2 (CHead d2 (Bind Abbr) u2))))) (\lambda 
(d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d1 d2)))) (\lambda (_: 
C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 (asucc g a))))) (\lambda 
(d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 a)))))) (\lambda (H3: 
(ex2 C (\lambda (d2: C).(eq C c2 (CHead d2 (Bind Abst) u1))) (\lambda (d2: 
C).(csuba g d1 d2)))).(ex2_ind C (\lambda (d2: C).(eq C c2 (CHead d2 (Bind 
Abst) u1))) (\lambda (d2: C).(csuba g d1 d2)) (or (ex2 C (\lambda (d2: 
C).(drop O O c2 (CHead d2 (Bind Abst) u1))) (\lambda (d2: C).(csuba g d1 
d2))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(drop O 
O c2 (CHead d2 (Bind Abbr) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda 
(_: A).(csuba g d1 d2)))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: 
A).(arity g d1 u1 (asucc g a))))) (\lambda (d2: C).(\lambda (u2: T).(\lambda 
(a: A).(arity g d2 u2 a)))))) (\lambda (x: C).(\lambda (H4: (eq C c2 (CHead x 
(Bind Abst) u1))).(\lambda (H5: (csuba g d1 x)).(eq_ind_r C (CHead x (Bind 
Abst) u1) (\lambda (c: C).(or (ex2 C (\lambda (d2: C).(drop O O c (CHead d2 
(Bind Abst) u1))) (\lambda (d2: C).(csuba g d1 d2))) (ex4_3 C T A (\lambda 
(d2: C).(\lambda (u2: T).(\lambda (_: A).(drop O O c (CHead d2 (Bind Abbr) 
u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d1 d2)))) 
(\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 (asucc g 
a))))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 
a))))))) (or_introl (ex2 C (\lambda (d2: C).(drop O O (CHead x (Bind Abst) 
u1) (CHead d2 (Bind Abst) u1))) (\lambda (d2: C).(csuba g d1 d2))) (ex4_3 C T 
A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(drop O O (CHead x (Bind 
Abst) u1) (CHead d2 (Bind Abbr) u2))))) (\lambda (d2: C).(\lambda (_: 
T).(\lambda (_: A).(csuba g d1 d2)))) (\lambda (_: C).(\lambda (_: 
T).(\lambda (a: A).(arity g d1 u1 (asucc g a))))) (\lambda (d2: C).(\lambda 
(u2: T).(\lambda (a: A).(arity g d2 u2 a))))) (ex_intro2 C (\lambda (d2: 
C).(drop O O (CHead x (Bind Abst) u1) (CHead d2 (Bind Abst) u1))) (\lambda 
(d2: C).(csuba g d1 d2)) x (drop_refl (CHead x (Bind Abst) u1)) H5)) c2 
H4)))) H3)) (\lambda (H3: (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: 
T).(\lambda (_: A).(eq C c2 (CHead d2 (Bind Abbr) u2))))) (\lambda (d2: 
C).(\lambda (_: T).(\lambda (_: A).(csuba g d1 d2)))) (\lambda (_: 
C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 (asucc g a))))) (\lambda 
(d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 a)))))).(ex4_3_ind C 
T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(eq C c2 (CHead d2 
(Bind Abbr) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g 
d1 d2)))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 
(asucc g a))))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 
u2 a)))) (or (ex2 C (\lambda (d2: C).(drop O O c2 (CHead d2 (Bind Abst) u1))) 
(\lambda (d2: C).(csuba g d1 d2))) (ex4_3 C T A (\lambda (d2: C).(\lambda 
(u2: T).(\lambda (_: A).(drop O O c2 (CHead d2 (Bind Abbr) u2))))) (\lambda 
(d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d1 d2)))) (\lambda (_: 
C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 (asucc g a))))) (\lambda 
(d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 a)))))) (\lambda (x0: 
C).(\lambda (x1: T).(\lambda (x2: A).(\lambda (H4: (eq C c2 (CHead x0 (Bind 
Abbr) x1))).(\lambda (H5: (csuba g d1 x0)).(\lambda (H6: (arity g d1 u1 
(asucc g x2))).(\lambda (H7: (arity g x0 x1 x2)).(eq_ind_r C (CHead x0 (Bind 
Abbr) x1) (\lambda (c: C).(or (ex2 C (\lambda (d2: C).(drop O O c (CHead d2 
(Bind Abst) u1))) (\lambda (d2: C).(csuba g d1 d2))) (ex4_3 C T A (\lambda 
(d2: C).(\lambda (u2: T).(\lambda (_: A).(drop O O c (CHead d2 (Bind Abbr) 
u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d1 d2)))) 
(\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 (asucc g 
a))))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 
a))))))) (or_intror (ex2 C (\lambda (d2: C).(drop O O (CHead x0 (Bind Abbr) 
x1) (CHead d2 (Bind Abst) u1))) (\lambda (d2: C).(csuba g d1 d2))) (ex4_3 C T 
A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(drop O O (CHead x0 (Bind 
Abbr) x1) (CHead d2 (Bind Abbr) u2))))) (\lambda (d2: C).(\lambda (_: 
T).(\lambda (_: A).(csuba g d1 d2)))) (\lambda (_: C).(\lambda (_: 
T).(\lambda (a: A).(arity g d1 u1 (asucc g a))))) (\lambda (d2: C).(\lambda 
(u2: T).(\lambda (a: A).(arity g d2 u2 a))))) (ex4_3_intro C T A (\lambda 
(d2: C).(\lambda (u2: T).(\lambda (_: A).(drop O O (CHead x0 (Bind Abbr) x1) 
(CHead d2 (Bind Abbr) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: 
A).(csuba g d1 d2)))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity 
g d1 u1 (asucc g a))))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: 
A).(arity g d2 u2 a)))) x0 x1 x2 (drop_refl (CHead x0 (Bind Abbr) x1)) H5 H6 
H7)) c2 H4)))))))) H3)) H2))))))))))) (\lambda (n: nat).(\lambda (H: 
((\forall (c1: C).(\forall (d1: C).(\forall (u1: T).((drop n O c1 (CHead d1 
(Bind Abst) u1)) \to (\forall (g: G).(\forall (c2: C).((csuba g c1 c2) \to 
(or (ex2 C (\lambda (d2: C).(drop n O c2 (CHead d2 (Bind Abst) u1))) (\lambda 
(d2: C).(csuba g d1 d2))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: 
T).(\lambda (_: A).(drop n O c2 (CHead d2 (Bind Abbr) u2))))) (\lambda (d2: 
C).(\lambda (_: T).(\lambda (_: A).(csuba g d1 d2)))) (\lambda (_: 
C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 (asucc g a))))) (\lambda 
(d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 
a))))))))))))))).(\lambda (c1: C).(C_ind (\lambda (c: C).(\forall (d1: 
C).(\forall (u1: T).((drop (S n) O c (CHead d1 (Bind Abst) u1)) \to (\forall 
(g: G).(\forall (c2: C).((csuba g c c2) \to (or (ex2 C (\lambda (d2: C).(drop 
(S n) O c2 (CHead d2 (Bind Abst) u1))) (\lambda (d2: C).(csuba g d1 d2))) 
(ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(drop (S n) O 
c2 (CHead d2 (Bind Abbr) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda 
(_: A).(csuba g d1 d2)))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: 
A).(arity g d1 u1 (asucc g a))))) (\lambda (d2: C).(\lambda (u2: T).(\lambda 
(a: A).(arity g d2 u2 a))))))))))))) (\lambda (n0: nat).(\lambda (d1: 
C).(\lambda (u1: T).(\lambda (H0: (drop (S n) O (CSort n0) (CHead d1 (Bind 
Abst) u1))).(\lambda (g: G).(\lambda (c2: C).(\lambda (_: (csuba g (CSort n0) 
c2)).(and3_ind (eq C (CHead d1 (Bind Abst) u1) (CSort n0)) (eq nat (S n) O) 
(eq nat O O) (or (ex2 C (\lambda (d2: C).(drop (S n) O c2 (CHead d2 (Bind 
Abst) u1))) (\lambda (d2: C).(csuba g d1 d2))) (ex4_3 C T A (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (_: A).(drop (S n) O c2 (CHead d2 (Bind Abbr) 
u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d1 d2)))) 
(\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 (asucc g 
a))))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 
a)))))) (\lambda (_: (eq C (CHead d1 (Bind Abst) u1) (CSort n0))).(\lambda 
(H3: (eq nat (S n) O)).(\lambda (_: (eq nat O O)).(let H5 \def (eq_ind nat (S 
n) (\lambda (ee: nat).(match ee in nat return (\lambda (_: nat).Prop) with [O 
\Rightarrow False | (S _) \Rightarrow True])) I O H3) in (False_ind (or (ex2 
C (\lambda (d2: C).(drop (S n) O c2 (CHead d2 (Bind Abst) u1))) (\lambda (d2: 
C).(csuba g d1 d2))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda 
(_: A).(drop (S n) O c2 (CHead d2 (Bind Abbr) u2))))) (\lambda (d2: 
C).(\lambda (_: T).(\lambda (_: A).(csuba g d1 d2)))) (\lambda (_: 
C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 (asucc g a))))) (\lambda 
(d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 a)))))) H5))))) 
(drop_gen_sort n0 (S n) O (CHead d1 (Bind Abst) u1) H0))))))))) (\lambda (c: 
C).(\lambda (H0: ((\forall (d1: C).(\forall (u1: T).((drop (S n) O c (CHead 
d1 (Bind Abst) u1)) \to (\forall (g: G).(\forall (c2: C).((csuba g c c2) \to 
(or (ex2 C (\lambda (d2: C).(drop (S n) O c2 (CHead d2 (Bind Abst) u1))) 
(\lambda (d2: C).(csuba g d1 d2))) (ex4_3 C T A (\lambda (d2: C).(\lambda 
(u2: T).(\lambda (_: A).(drop (S n) O c2 (CHead d2 (Bind Abbr) u2))))) 
(\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d1 d2)))) (\lambda 
(_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 (asucc g a))))) 
(\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 
a)))))))))))))).(\lambda (k: K).(\lambda (t: T).(\lambda (d1: C).(\lambda 
(u1: T).(\lambda (H1: (drop (S n) O (CHead c k t) (CHead d1 (Bind Abst) 
u1))).(\lambda (g: G).(\lambda (c2: C).(\lambda (H2: (csuba g (CHead c k t) 
c2)).(K_ind (\lambda (k0: K).((csuba g (CHead c k0 t) c2) \to ((drop (r k0 n) 
O c (CHead d1 (Bind Abst) u1)) \to (or (ex2 C (\lambda (d2: C).(drop (S n) O 
c2 (CHead d2 (Bind Abst) u1))) (\lambda (d2: C).(csuba g d1 d2))) (ex4_3 C T 
A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(drop (S n) O c2 (CHead 
d2 (Bind Abbr) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: 
A).(csuba g d1 d2)))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity 
g d1 u1 (asucc g a))))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: 
A).(arity g d2 u2 a))))))))) (\lambda (b: B).(\lambda (H3: (csuba g (CHead c 
(Bind b) t) c2)).(\lambda (H4: (drop (r (Bind b) n) O c (CHead d1 (Bind Abst) 
u1))).(B_ind (\lambda (b0: B).((csuba g (CHead c (Bind b0) t) c2) \to ((drop 
(r (Bind b0) n) O c (CHead d1 (Bind Abst) u1)) \to (or (ex2 C (\lambda (d2: 
C).(drop (S n) O c2 (CHead d2 (Bind Abst) u1))) (\lambda (d2: C).(csuba g d1 
d2))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(drop (S 
n) O c2 (CHead d2 (Bind Abbr) u2))))) (\lambda (d2: C).(\lambda (_: 
T).(\lambda (_: A).(csuba g d1 d2)))) (\lambda (_: C).(\lambda (_: 
T).(\lambda (a: A).(arity g d1 u1 (asucc g a))))) (\lambda (d2: C).(\lambda 
(u2: T).(\lambda (a: A).(arity g d2 u2 a))))))))) (\lambda (H5: (csuba g 
(CHead c (Bind Abbr) t) c2)).(\lambda (H6: (drop (r (Bind Abbr) n) O c (CHead 
d1 (Bind Abst) u1))).(let H_x \def (csuba_gen_abbr g c c2 t H5) in (let H7 
\def H_x in (ex2_ind C (\lambda (d2: C).(eq C c2 (CHead d2 (Bind Abbr) t))) 
(\lambda (d2: C).(csuba g c d2)) (or (ex2 C (\lambda (d2: C).(drop (S n) O c2 
(CHead d2 (Bind Abst) u1))) (\lambda (d2: C).(csuba g d1 d2))) (ex4_3 C T A 
(\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(drop (S n) O c2 (CHead d2 
(Bind Abbr) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g 
d1 d2)))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 
(asucc g a))))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 
u2 a)))))) (\lambda (x: C).(\lambda (H8: (eq C c2 (CHead x (Bind Abbr) 
t))).(\lambda (H9: (csuba g c x)).(eq_ind_r C (CHead x (Bind Abbr) t) 
(\lambda (c0: C).(or (ex2 C (\lambda (d2: C).(drop (S n) O c0 (CHead d2 (Bind 
Abst) u1))) (\lambda (d2: C).(csuba g d1 d2))) (ex4_3 C T A (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (_: A).(drop (S n) O c0 (CHead d2 (Bind Abbr) 
u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d1 d2)))) 
(\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 (asucc g 
a))))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 
a))))))) (let H10 \def (H c d1 u1 H6 g x H9) in (or_ind (ex2 C (\lambda (d2: 
C).(drop n O x (CHead d2 (Bind Abst) u1))) (\lambda (d2: C).(csuba g d1 d2))) 
(ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(drop n O x 
(CHead d2 (Bind Abbr) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: 
A).(csuba g d1 d2)))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity 
g d1 u1 (asucc g a))))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: 
A).(arity g d2 u2 a))))) (or (ex2 C (\lambda (d2: C).(drop (S n) O (CHead x 
(Bind Abbr) t) (CHead d2 (Bind Abst) u1))) (\lambda (d2: C).(csuba g d1 d2))) 
(ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(drop (S n) O 
(CHead x (Bind Abbr) t) (CHead d2 (Bind Abbr) u2))))) (\lambda (d2: 
C).(\lambda (_: T).(\lambda (_: A).(csuba g d1 d2)))) (\lambda (_: 
C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 (asucc g a))))) (\lambda 
(d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 a)))))) (\lambda 
(H11: (ex2 C (\lambda (d2: C).(drop n O x (CHead d2 (Bind Abst) u1))) 
(\lambda (d2: C).(csuba g d1 d2)))).(ex2_ind C (\lambda (d2: C).(drop n O x 
(CHead d2 (Bind Abst) u1))) (\lambda (d2: C).(csuba g d1 d2)) (or (ex2 C 
(\lambda (d2: C).(drop (S n) O (CHead x (Bind Abbr) t) (CHead d2 (Bind Abst) 
u1))) (\lambda (d2: C).(csuba g d1 d2))) (ex4_3 C T A (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (_: A).(drop (S n) O (CHead x (Bind Abbr) t) 
(CHead d2 (Bind Abbr) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: 
A).(csuba g d1 d2)))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity 
g d1 u1 (asucc g a))))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: 
A).(arity g d2 u2 a)))))) (\lambda (x0: C).(\lambda (H12: (drop n O x (CHead 
x0 (Bind Abst) u1))).(\lambda (H13: (csuba g d1 x0)).(let H14 \def 
(refl_equal nat (r (Bind Abbr) n)) in (let H15 \def (eq_ind nat n (\lambda 
(n0: nat).(drop n0 O x (CHead x0 (Bind Abst) u1))) H12 (r (Bind Abbr) n) H14) 
in (or_introl (ex2 C (\lambda (d2: C).(drop (S n) O (CHead x (Bind Abbr) t) 
(CHead d2 (Bind Abst) u1))) (\lambda (d2: C).(csuba g d1 d2))) (ex4_3 C T A 
(\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(drop (S n) O (CHead x 
(Bind Abbr) t) (CHead d2 (Bind Abbr) u2))))) (\lambda (d2: C).(\lambda (_: 
T).(\lambda (_: A).(csuba g d1 d2)))) (\lambda (_: C).(\lambda (_: 
T).(\lambda (a: A).(arity g d1 u1 (asucc g a))))) (\lambda (d2: C).(\lambda 
(u2: T).(\lambda (a: A).(arity g d2 u2 a))))) (ex_intro2 C (\lambda (d2: 
C).(drop (S n) O (CHead x (Bind Abbr) t) (CHead d2 (Bind Abst) u1))) (\lambda 
(d2: C).(csuba g d1 d2)) x0 (drop_drop (Bind Abbr) n x (CHead x0 (Bind Abst) 
u1) H15 t) H13))))))) H11)) (\lambda (H11: (ex4_3 C T A (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (_: A).(drop n O x (CHead d2 (Bind Abbr) u2))))) 
(\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d1 d2)))) (\lambda 
(_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 (asucc g a))))) 
(\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 
a)))))).(ex4_3_ind C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: 
A).(drop n O x (CHead d2 (Bind Abbr) u2))))) (\lambda (d2: C).(\lambda (_: 
T).(\lambda (_: A).(csuba g d1 d2)))) (\lambda (_: C).(\lambda (_: 
T).(\lambda (a: A).(arity g d1 u1 (asucc g a))))) (\lambda (d2: C).(\lambda 
(u2: T).(\lambda (a: A).(arity g d2 u2 a)))) (or (ex2 C (\lambda (d2: 
C).(drop (S n) O (CHead x (Bind Abbr) t) (CHead d2 (Bind Abst) u1))) (\lambda 
(d2: C).(csuba g d1 d2))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: 
T).(\lambda (_: A).(drop (S n) O (CHead x (Bind Abbr) t) (CHead d2 (Bind 
Abbr) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d1 
d2)))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 (asucc 
g a))))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 
a)))))) (\lambda (x0: C).(\lambda (x1: T).(\lambda (x2: A).(\lambda (H12: 
(drop n O x (CHead x0 (Bind Abbr) x1))).(\lambda (H13: (csuba g d1 
x0)).(\lambda (H14: (arity g d1 u1 (asucc g x2))).(\lambda (H15: (arity g x0 
x1 x2)).(let H16 \def (refl_equal nat (r (Bind Abbr) n)) in (let H17 \def 
(eq_ind nat n (\lambda (n0: nat).(drop n0 O x (CHead x0 (Bind Abbr) x1))) H12 
(r (Bind Abbr) n) H16) in (or_intror (ex2 C (\lambda (d2: C).(drop (S n) O 
(CHead x (Bind Abbr) t) (CHead d2 (Bind Abst) u1))) (\lambda (d2: C).(csuba g 
d1 d2))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(drop 
(S n) O (CHead x (Bind Abbr) t) (CHead d2 (Bind Abbr) u2))))) (\lambda (d2: 
C).(\lambda (_: T).(\lambda (_: A).(csuba g d1 d2)))) (\lambda (_: 
C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 (asucc g a))))) (\lambda 
(d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 a))))) (ex4_3_intro C 
T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(drop (S n) O (CHead x 
(Bind Abbr) t) (CHead d2 (Bind Abbr) u2))))) (\lambda (d2: C).(\lambda (_: 
T).(\lambda (_: A).(csuba g d1 d2)))) (\lambda (_: C).(\lambda (_: 
T).(\lambda (a: A).(arity g d1 u1 (asucc g a))))) (\lambda (d2: C).(\lambda 
(u2: T).(\lambda (a: A).(arity g d2 u2 a)))) x0 x1 x2 (drop_drop (Bind Abbr) 
n x (CHead x0 (Bind Abbr) x1) H17 t) H13 H14 H15))))))))))) H11)) H10)) c2 
H8)))) H7))))) (\lambda (H5: (csuba g (CHead c (Bind Abst) t) c2)).(\lambda 
(H6: (drop (r (Bind Abst) n) O c (CHead d1 (Bind Abst) u1))).(let H_x \def 
(csuba_gen_abst g c c2 t H5) in (let H7 \def H_x in (or_ind (ex2 C (\lambda 
(d2: C).(eq C c2 (CHead d2 (Bind Abst) t))) (\lambda (d2: C).(csuba g c d2))) 
(ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(eq C c2 
(CHead d2 (Bind Abbr) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: 
A).(csuba g c d2)))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g 
c t (asucc g a))))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity 
g d2 u2 a))))) (or (ex2 C (\lambda (d2: C).(drop (S n) O c2 (CHead d2 (Bind 
Abst) u1))) (\lambda (d2: C).(csuba g d1 d2))) (ex4_3 C T A (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (_: A).(drop (S n) O c2 (CHead d2 (Bind Abbr) 
u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d1 d2)))) 
(\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 (asucc g 
a))))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 
a)))))) (\lambda (H8: (ex2 C (\lambda (d2: C).(eq C c2 (CHead d2 (Bind Abst) 
t))) (\lambda (d2: C).(csuba g c d2)))).(ex2_ind C (\lambda (d2: C).(eq C c2 
(CHead d2 (Bind Abst) t))) (\lambda (d2: C).(csuba g c d2)) (or (ex2 C 
(\lambda (d2: C).(drop (S n) O c2 (CHead d2 (Bind Abst) u1))) (\lambda (d2: 
C).(csuba g d1 d2))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda 
(_: A).(drop (S n) O c2 (CHead d2 (Bind Abbr) u2))))) (\lambda (d2: 
C).(\lambda (_: T).(\lambda (_: A).(csuba g d1 d2)))) (\lambda (_: 
C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 (asucc g a))))) (\lambda 
(d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 a)))))) (\lambda (x: 
C).(\lambda (H9: (eq C c2 (CHead x (Bind Abst) t))).(\lambda (H10: (csuba g c 
x)).(eq_ind_r C (CHead x (Bind Abst) t) (\lambda (c0: C).(or (ex2 C (\lambda 
(d2: C).(drop (S n) O c0 (CHead d2 (Bind Abst) u1))) (\lambda (d2: C).(csuba 
g d1 d2))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: 
A).(drop (S n) O c0 (CHead d2 (Bind Abbr) u2))))) (\lambda (d2: C).(\lambda 
(_: T).(\lambda (_: A).(csuba g d1 d2)))) (\lambda (_: C).(\lambda (_: 
T).(\lambda (a: A).(arity g d1 u1 (asucc g a))))) (\lambda (d2: C).(\lambda 
(u2: T).(\lambda (a: A).(arity g d2 u2 a))))))) (let H11 \def (H c d1 u1 H6 g 
x H10) in (or_ind (ex2 C (\lambda (d2: C).(drop n O x (CHead d2 (Bind Abst) 
u1))) (\lambda (d2: C).(csuba g d1 d2))) (ex4_3 C T A (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (_: A).(drop n O x (CHead d2 (Bind Abbr) u2))))) 
(\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d1 d2)))) (\lambda 
(_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 (asucc g a))))) 
(\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 a))))) (or 
(ex2 C (\lambda (d2: C).(drop (S n) O (CHead x (Bind Abst) t) (CHead d2 (Bind 
Abst) u1))) (\lambda (d2: C).(csuba g d1 d2))) (ex4_3 C T A (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (_: A).(drop (S n) O (CHead x (Bind Abst) t) 
(CHead d2 (Bind Abbr) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: 
A).(csuba g d1 d2)))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity 
g d1 u1 (asucc g a))))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: 
A).(arity g d2 u2 a)))))) (\lambda (H12: (ex2 C (\lambda (d2: C).(drop n O x 
(CHead d2 (Bind Abst) u1))) (\lambda (d2: C).(csuba g d1 d2)))).(ex2_ind C 
(\lambda (d2: C).(drop n O x (CHead d2 (Bind Abst) u1))) (\lambda (d2: 
C).(csuba g d1 d2)) (or (ex2 C (\lambda (d2: C).(drop (S n) O (CHead x (Bind 
Abst) t) (CHead d2 (Bind Abst) u1))) (\lambda (d2: C).(csuba g d1 d2))) 
(ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(drop (S n) O 
(CHead x (Bind Abst) t) (CHead d2 (Bind Abbr) u2))))) (\lambda (d2: 
C).(\lambda (_: T).(\lambda (_: A).(csuba g d1 d2)))) (\lambda (_: 
C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 (asucc g a))))) (\lambda 
(d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 a)))))) (\lambda (x0: 
C).(\lambda (H13: (drop n O x (CHead x0 (Bind Abst) u1))).(\lambda (H14: 
(csuba g d1 x0)).(let H15 \def (refl_equal nat (r (Bind Abbr) n)) in (let H16 
\def (eq_ind nat n (\lambda (n0: nat).(drop n0 O x (CHead x0 (Bind Abst) 
u1))) H13 (r (Bind Abbr) n) H15) in (or_introl (ex2 C (\lambda (d2: C).(drop 
(S n) O (CHead x (Bind Abst) t) (CHead d2 (Bind Abst) u1))) (\lambda (d2: 
C).(csuba g d1 d2))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda 
(_: A).(drop (S n) O (CHead x (Bind Abst) t) (CHead d2 (Bind Abbr) u2))))) 
(\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d1 d2)))) (\lambda 
(_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 (asucc g a))))) 
(\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 a))))) 
(ex_intro2 C (\lambda (d2: C).(drop (S n) O (CHead x (Bind Abst) t) (CHead d2 
(Bind Abst) u1))) (\lambda (d2: C).(csuba g d1 d2)) x0 (drop_drop (Bind Abst) 
n x (CHead x0 (Bind Abst) u1) H16 t) H14))))))) H12)) (\lambda (H12: (ex4_3 C 
T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(drop n O x (CHead d2 
(Bind Abbr) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g 
d1 d2)))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 
(asucc g a))))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 
u2 a)))))).(ex4_3_ind C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: 
A).(drop n O x (CHead d2 (Bind Abbr) u2))))) (\lambda (d2: C).(\lambda (_: 
T).(\lambda (_: A).(csuba g d1 d2)))) (\lambda (_: C).(\lambda (_: 
T).(\lambda (a: A).(arity g d1 u1 (asucc g a))))) (\lambda (d2: C).(\lambda 
(u2: T).(\lambda (a: A).(arity g d2 u2 a)))) (or (ex2 C (\lambda (d2: 
C).(drop (S n) O (CHead x (Bind Abst) t) (CHead d2 (Bind Abst) u1))) (\lambda 
(d2: C).(csuba g d1 d2))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: 
T).(\lambda (_: A).(drop (S n) O (CHead x (Bind Abst) t) (CHead d2 (Bind 
Abbr) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d1 
d2)))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 (asucc 
g a))))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 
a)))))) (\lambda (x0: C).(\lambda (x1: T).(\lambda (x2: A).(\lambda (H13: 
(drop n O x (CHead x0 (Bind Abbr) x1))).(\lambda (H14: (csuba g d1 
x0)).(\lambda (H15: (arity g d1 u1 (asucc g x2))).(\lambda (H16: (arity g x0 
x1 x2)).(let H17 \def (refl_equal nat (r (Bind Abbr) n)) in (let H18 \def 
(eq_ind nat n (\lambda (n0: nat).(drop n0 O x (CHead x0 (Bind Abbr) x1))) H13 
(r (Bind Abbr) n) H17) in (or_intror (ex2 C (\lambda (d2: C).(drop (S n) O 
(CHead x (Bind Abst) t) (CHead d2 (Bind Abst) u1))) (\lambda (d2: C).(csuba g 
d1 d2))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(drop 
(S n) O (CHead x (Bind Abst) t) (CHead d2 (Bind Abbr) u2))))) (\lambda (d2: 
C).(\lambda (_: T).(\lambda (_: A).(csuba g d1 d2)))) (\lambda (_: 
C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 (asucc g a))))) (\lambda 
(d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 a))))) (ex4_3_intro C 
T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(drop (S n) O (CHead x 
(Bind Abst) t) (CHead d2 (Bind Abbr) u2))))) (\lambda (d2: C).(\lambda (_: 
T).(\lambda (_: A).(csuba g d1 d2)))) (\lambda (_: C).(\lambda (_: 
T).(\lambda (a: A).(arity g d1 u1 (asucc g a))))) (\lambda (d2: C).(\lambda 
(u2: T).(\lambda (a: A).(arity g d2 u2 a)))) x0 x1 x2 (drop_drop (Bind Abst) 
n x (CHead x0 (Bind Abbr) x1) H18 t) H14 H15 H16))))))))))) H12)) H11)) c2 
H9)))) H8)) (\lambda (H8: (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: 
T).(\lambda (_: A).(eq C c2 (CHead d2 (Bind Abbr) u2))))) (\lambda (d2: 
C).(\lambda (_: T).(\lambda (_: A).(csuba g c d2)))) (\lambda (_: C).(\lambda 
(_: T).(\lambda (a: A).(arity g c t (asucc g a))))) (\lambda (d2: C).(\lambda 
(u2: T).(\lambda (a: A).(arity g d2 u2 a)))))).(ex4_3_ind C T A (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (_: A).(eq C c2 (CHead d2 (Bind Abbr) u2))))) 
(\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g c d2)))) (\lambda 
(_: C).(\lambda (_: T).(\lambda (a: A).(arity g c t (asucc g a))))) (\lambda 
(d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 a)))) (or (ex2 C 
(\lambda (d2: C).(drop (S n) O c2 (CHead d2 (Bind Abst) u1))) (\lambda (d2: 
C).(csuba g d1 d2))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda 
(_: A).(drop (S n) O c2 (CHead d2 (Bind Abbr) u2))))) (\lambda (d2: 
C).(\lambda (_: T).(\lambda (_: A).(csuba g d1 d2)))) (\lambda (_: 
C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 (asucc g a))))) (\lambda 
(d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 a)))))) (\lambda (x0: 
C).(\lambda (x1: T).(\lambda (x2: A).(\lambda (H9: (eq C c2 (CHead x0 (Bind 
Abbr) x1))).(\lambda (H10: (csuba g c x0)).(\lambda (_: (arity g c t (asucc g 
x2))).(\lambda (_: (arity g x0 x1 x2)).(eq_ind_r C (CHead x0 (Bind Abbr) x1) 
(\lambda (c0: C).(or (ex2 C (\lambda (d2: C).(drop (S n) O c0 (CHead d2 (Bind 
Abst) u1))) (\lambda (d2: C).(csuba g d1 d2))) (ex4_3 C T A (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (_: A).(drop (S n) O c0 (CHead d2 (Bind Abbr) 
u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d1 d2)))) 
(\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 (asucc g 
a))))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 
a))))))) (let H13 \def (H c d1 u1 H6 g x0 H10) in (or_ind (ex2 C (\lambda 
(d2: C).(drop n O x0 (CHead d2 (Bind Abst) u1))) (\lambda (d2: C).(csuba g d1 
d2))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(drop n 
O x0 (CHead d2 (Bind Abbr) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda 
(_: A).(csuba g d1 d2)))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: 
A).(arity g d1 u1 (asucc g a))))) (\lambda (d2: C).(\lambda (u2: T).(\lambda 
(a: A).(arity g d2 u2 a))))) (or (ex2 C (\lambda (d2: C).(drop (S n) O (CHead 
x0 (Bind Abbr) x1) (CHead d2 (Bind Abst) u1))) (\lambda (d2: C).(csuba g d1 
d2))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(drop (S 
n) O (CHead x0 (Bind Abbr) x1) (CHead d2 (Bind Abbr) u2))))) (\lambda (d2: 
C).(\lambda (_: T).(\lambda (_: A).(csuba g d1 d2)))) (\lambda (_: 
C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 (asucc g a))))) (\lambda 
(d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 a)))))) (\lambda 
(H14: (ex2 C (\lambda (d2: C).(drop n O x0 (CHead d2 (Bind Abst) u1))) 
(\lambda (d2: C).(csuba g d1 d2)))).(ex2_ind C (\lambda (d2: C).(drop n O x0 
(CHead d2 (Bind Abst) u1))) (\lambda (d2: C).(csuba g d1 d2)) (or (ex2 C 
(\lambda (d2: C).(drop (S n) O (CHead x0 (Bind Abbr) x1) (CHead d2 (Bind 
Abst) u1))) (\lambda (d2: C).(csuba g d1 d2))) (ex4_3 C T A (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (_: A).(drop (S n) O (CHead x0 (Bind Abbr) x1) 
(CHead d2 (Bind Abbr) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: 
A).(csuba g d1 d2)))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity 
g d1 u1 (asucc g a))))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: 
A).(arity g d2 u2 a)))))) (\lambda (x: C).(\lambda (H15: (drop n O x0 (CHead 
x (Bind Abst) u1))).(\lambda (H16: (csuba g d1 x)).(let H17 \def (refl_equal 
nat (r (Bind Abbr) n)) in (let H18 \def (eq_ind nat n (\lambda (n0: 
nat).(drop n0 O x0 (CHead x (Bind Abst) u1))) H15 (r (Bind Abbr) n) H17) in 
(or_introl (ex2 C (\lambda (d2: C).(drop (S n) O (CHead x0 (Bind Abbr) x1) 
(CHead d2 (Bind Abst) u1))) (\lambda (d2: C).(csuba g d1 d2))) (ex4_3 C T A 
(\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(drop (S n) O (CHead x0 
(Bind Abbr) x1) (CHead d2 (Bind Abbr) u2))))) (\lambda (d2: C).(\lambda (_: 
T).(\lambda (_: A).(csuba g d1 d2)))) (\lambda (_: C).(\lambda (_: 
T).(\lambda (a: A).(arity g d1 u1 (asucc g a))))) (\lambda (d2: C).(\lambda 
(u2: T).(\lambda (a: A).(arity g d2 u2 a))))) (ex_intro2 C (\lambda (d2: 
C).(drop (S n) O (CHead x0 (Bind Abbr) x1) (CHead d2 (Bind Abst) u1))) 
(\lambda (d2: C).(csuba g d1 d2)) x (drop_drop (Bind Abbr) n x0 (CHead x 
(Bind Abst) u1) H18 x1) H16))))))) H14)) (\lambda (H14: (ex4_3 C T A (\lambda 
(d2: C).(\lambda (u2: T).(\lambda (_: A).(drop n O x0 (CHead d2 (Bind Abbr) 
u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d1 d2)))) 
(\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 (asucc g 
a))))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 
a)))))).(ex4_3_ind C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: 
A).(drop n O x0 (CHead d2 (Bind Abbr) u2))))) (\lambda (d2: C).(\lambda (_: 
T).(\lambda (_: A).(csuba g d1 d2)))) (\lambda (_: C).(\lambda (_: 
T).(\lambda (a: A).(arity g d1 u1 (asucc g a))))) (\lambda (d2: C).(\lambda 
(u2: T).(\lambda (a: A).(arity g d2 u2 a)))) (or (ex2 C (\lambda (d2: 
C).(drop (S n) O (CHead x0 (Bind Abbr) x1) (CHead d2 (Bind Abst) u1))) 
(\lambda (d2: C).(csuba g d1 d2))) (ex4_3 C T A (\lambda (d2: C).(\lambda 
(u2: T).(\lambda (_: A).(drop (S n) O (CHead x0 (Bind Abbr) x1) (CHead d2 
(Bind Abbr) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g 
d1 d2)))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 
(asucc g a))))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 
u2 a)))))) (\lambda (x3: C).(\lambda (x4: T).(\lambda (x5: A).(\lambda (H15: 
(drop n O x0 (CHead x3 (Bind Abbr) x4))).(\lambda (H16: (csuba g d1 
x3)).(\lambda (H17: (arity g d1 u1 (asucc g x5))).(\lambda (H18: (arity g x3 
x4 x5)).(let H19 \def (refl_equal nat (r (Bind Abbr) n)) in (let H20 \def 
(eq_ind nat n (\lambda (n0: nat).(drop n0 O x0 (CHead x3 (Bind Abbr) x4))) 
H15 (r (Bind Abbr) n) H19) in (or_intror (ex2 C (\lambda (d2: C).(drop (S n) 
O (CHead x0 (Bind Abbr) x1) (CHead d2 (Bind Abst) u1))) (\lambda (d2: 
C).(csuba g d1 d2))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda 
(_: A).(drop (S n) O (CHead x0 (Bind Abbr) x1) (CHead d2 (Bind Abbr) u2))))) 
(\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d1 d2)))) (\lambda 
(_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 (asucc g a))))) 
(\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 a))))) 
(ex4_3_intro C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(drop (S 
n) O (CHead x0 (Bind Abbr) x1) (CHead d2 (Bind Abbr) u2))))) (\lambda (d2: 
C).(\lambda (_: T).(\lambda (_: A).(csuba g d1 d2)))) (\lambda (_: 
C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 (asucc g a))))) (\lambda 
(d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 a)))) x3 x4 x5 
(drop_drop (Bind Abbr) n x0 (CHead x3 (Bind Abbr) x4) H20 x1) H16 H17 
H18))))))))))) H14)) H13)) c2 H9)))))))) H8)) H7))))) (\lambda (H5: (csuba g 
(CHead c (Bind Void) t) c2)).(\lambda (H6: (drop (r (Bind Void) n) O c (CHead 
d1 (Bind Abst) u1))).(let H_x \def (csuba_gen_void g c c2 t H5) in (let H7 
\def H_x in (ex2_3_ind B C T (\lambda (b0: B).(\lambda (d2: C).(\lambda (u2: 
T).(eq C c2 (CHead d2 (Bind b0) u2))))) (\lambda (_: B).(\lambda (d2: 
C).(\lambda (_: T).(csuba g c d2)))) (or (ex2 C (\lambda (d2: C).(drop (S n) 
O c2 (CHead d2 (Bind Abst) u1))) (\lambda (d2: C).(csuba g d1 d2))) (ex4_3 C 
T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(drop (S n) O c2 (CHead 
d2 (Bind Abbr) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: 
A).(csuba g d1 d2)))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity 
g d1 u1 (asucc g a))))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: 
A).(arity g d2 u2 a)))))) (\lambda (x0: B).(\lambda (x1: C).(\lambda (x2: 
T).(\lambda (H8: (eq C c2 (CHead x1 (Bind x0) x2))).(\lambda (H9: (csuba g c 
x1)).(eq_ind_r C (CHead x1 (Bind x0) x2) (\lambda (c0: C).(or (ex2 C (\lambda 
(d2: C).(drop (S n) O c0 (CHead d2 (Bind Abst) u1))) (\lambda (d2: C).(csuba 
g d1 d2))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: 
A).(drop (S n) O c0 (CHead d2 (Bind Abbr) u2))))) (\lambda (d2: C).(\lambda 
(_: T).(\lambda (_: A).(csuba g d1 d2)))) (\lambda (_: C).(\lambda (_: 
T).(\lambda (a: A).(arity g d1 u1 (asucc g a))))) (\lambda (d2: C).(\lambda 
(u2: T).(\lambda (a: A).(arity g d2 u2 a))))))) (let H10 \def (H c d1 u1 H6 g 
x1 H9) in (or_ind (ex2 C (\lambda (d2: C).(drop n O x1 (CHead d2 (Bind Abst) 
u1))) (\lambda (d2: C).(csuba g d1 d2))) (ex4_3 C T A (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (_: A).(drop n O x1 (CHead d2 (Bind Abbr) 
u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d1 d2)))) 
(\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 (asucc g 
a))))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 
a))))) (or (ex2 C (\lambda (d2: C).(drop (S n) O (CHead x1 (Bind x0) x2) 
(CHead d2 (Bind Abst) u1))) (\lambda (d2: C).(csuba g d1 d2))) (ex4_3 C T A 
(\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(drop (S n) O (CHead x1 
(Bind x0) x2) (CHead d2 (Bind Abbr) u2))))) (\lambda (d2: C).(\lambda (_: 
T).(\lambda (_: A).(csuba g d1 d2)))) (\lambda (_: C).(\lambda (_: 
T).(\lambda (a: A).(arity g d1 u1 (asucc g a))))) (\lambda (d2: C).(\lambda 
(u2: T).(\lambda (a: A).(arity g d2 u2 a)))))) (\lambda (H11: (ex2 C (\lambda 
(d2: C).(drop n O x1 (CHead d2 (Bind Abst) u1))) (\lambda (d2: C).(csuba g d1 
d2)))).(ex2_ind C (\lambda (d2: C).(drop n O x1 (CHead d2 (Bind Abst) u1))) 
(\lambda (d2: C).(csuba g d1 d2)) (or (ex2 C (\lambda (d2: C).(drop (S n) O 
(CHead x1 (Bind x0) x2) (CHead d2 (Bind Abst) u1))) (\lambda (d2: C).(csuba g 
d1 d2))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(drop 
(S n) O (CHead x1 (Bind x0) x2) (CHead d2 (Bind Abbr) u2))))) (\lambda (d2: 
C).(\lambda (_: T).(\lambda (_: A).(csuba g d1 d2)))) (\lambda (_: 
C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 (asucc g a))))) (\lambda 
(d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 a)))))) (\lambda (x: 
C).(\lambda (H12: (drop n O x1 (CHead x (Bind Abst) u1))).(\lambda (H13: 
(csuba g d1 x)).(let H14 \def (refl_equal nat (r (Bind Abbr) n)) in (let H15 
\def (eq_ind nat n (\lambda (n0: nat).(drop n0 O x1 (CHead x (Bind Abst) 
u1))) H12 (r (Bind Abbr) n) H14) in (or_introl (ex2 C (\lambda (d2: C).(drop 
(S n) O (CHead x1 (Bind x0) x2) (CHead d2 (Bind Abst) u1))) (\lambda (d2: 
C).(csuba g d1 d2))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda 
(_: A).(drop (S n) O (CHead x1 (Bind x0) x2) (CHead d2 (Bind Abbr) u2))))) 
(\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d1 d2)))) (\lambda 
(_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 (asucc g a))))) 
(\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 a))))) 
(ex_intro2 C (\lambda (d2: C).(drop (S n) O (CHead x1 (Bind x0) x2) (CHead d2 
(Bind Abst) u1))) (\lambda (d2: C).(csuba g d1 d2)) x (drop_drop (Bind x0) n 
x1 (CHead x (Bind Abst) u1) H15 x2) H13))))))) H11)) (\lambda (H11: (ex4_3 C 
T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(drop n O x1 (CHead d2 
(Bind Abbr) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g 
d1 d2)))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 
(asucc g a))))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 
u2 a)))))).(ex4_3_ind C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: 
A).(drop n O x1 (CHead d2 (Bind Abbr) u2))))) (\lambda (d2: C).(\lambda (_: 
T).(\lambda (_: A).(csuba g d1 d2)))) (\lambda (_: C).(\lambda (_: 
T).(\lambda (a: A).(arity g d1 u1 (asucc g a))))) (\lambda (d2: C).(\lambda 
(u2: T).(\lambda (a: A).(arity g d2 u2 a)))) (or (ex2 C (\lambda (d2: 
C).(drop (S n) O (CHead x1 (Bind x0) x2) (CHead d2 (Bind Abst) u1))) (\lambda 
(d2: C).(csuba g d1 d2))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: 
T).(\lambda (_: A).(drop (S n) O (CHead x1 (Bind x0) x2) (CHead d2 (Bind 
Abbr) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d1 
d2)))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 (asucc 
g a))))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 
a)))))) (\lambda (x3: C).(\lambda (x4: T).(\lambda (x5: A).(\lambda (H12: 
(drop n O x1 (CHead x3 (Bind Abbr) x4))).(\lambda (H13: (csuba g d1 
x3)).(\lambda (H14: (arity g d1 u1 (asucc g x5))).(\lambda (H15: (arity g x3 
x4 x5)).(let H16 \def (refl_equal nat (r (Bind Abbr) n)) in (let H17 \def 
(eq_ind nat n (\lambda (n0: nat).(drop n0 O x1 (CHead x3 (Bind Abbr) x4))) 
H12 (r (Bind Abbr) n) H16) in (or_intror (ex2 C (\lambda (d2: C).(drop (S n) 
O (CHead x1 (Bind x0) x2) (CHead d2 (Bind Abst) u1))) (\lambda (d2: C).(csuba 
g d1 d2))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: 
A).(drop (S n) O (CHead x1 (Bind x0) x2) (CHead d2 (Bind Abbr) u2))))) 
(\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d1 d2)))) (\lambda 
(_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 (asucc g a))))) 
(\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 a))))) 
(ex4_3_intro C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(drop (S 
n) O (CHead x1 (Bind x0) x2) (CHead d2 (Bind Abbr) u2))))) (\lambda (d2: 
C).(\lambda (_: T).(\lambda (_: A).(csuba g d1 d2)))) (\lambda (_: 
C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 (asucc g a))))) (\lambda 
(d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 a)))) x3 x4 x5 
(drop_drop (Bind x0) n x1 (CHead x3 (Bind Abbr) x4) H17 x2) H13 H14 
H15))))))))))) H11)) H10)) c2 H8)))))) H7))))) b H3 H4)))) (\lambda (f: 
F).(\lambda (H3: (csuba g (CHead c (Flat f) t) c2)).(\lambda (H4: (drop (r 
(Flat f) n) O c (CHead d1 (Bind Abst) u1))).(let H_x \def (csuba_gen_flat g c 
c2 t f H3) in (let H5 \def H_x in (ex2_2_ind C T (\lambda (d2: C).(\lambda 
(u2: T).(eq C c2 (CHead d2 (Flat f) u2)))) (\lambda (d2: C).(\lambda (_: 
T).(csuba g c d2))) (or (ex2 C (\lambda (d2: C).(drop (S n) O c2 (CHead d2 
(Bind Abst) u1))) (\lambda (d2: C).(csuba g d1 d2))) (ex4_3 C T A (\lambda 
(d2: C).(\lambda (u2: T).(\lambda (_: A).(drop (S n) O c2 (CHead d2 (Bind 
Abbr) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d1 
d2)))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 (asucc 
g a))))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 
a)))))) (\lambda (x0: C).(\lambda (x1: T).(\lambda (H6: (eq C c2 (CHead x0 
(Flat f) x1))).(\lambda (H7: (csuba g c x0)).(eq_ind_r C (CHead x0 (Flat f) 
x1) (\lambda (c0: C).(or (ex2 C (\lambda (d2: C).(drop (S n) O c0 (CHead d2 
(Bind Abst) u1))) (\lambda (d2: C).(csuba g d1 d2))) (ex4_3 C T A (\lambda 
(d2: C).(\lambda (u2: T).(\lambda (_: A).(drop (S n) O c0 (CHead d2 (Bind 
Abbr) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d1 
d2)))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 (asucc 
g a))))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 
a))))))) (let H8 \def (H0 d1 u1 H4 g x0 H7) in (or_ind (ex2 C (\lambda (d2: 
C).(drop (S n) O x0 (CHead d2 (Bind Abst) u1))) (\lambda (d2: C).(csuba g d1 
d2))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(drop (S 
n) O x0 (CHead d2 (Bind Abbr) u2))))) (\lambda (d2: C).(\lambda (_: 
T).(\lambda (_: A).(csuba g d1 d2)))) (\lambda (_: C).(\lambda (_: 
T).(\lambda (a: A).(arity g d1 u1 (asucc g a))))) (\lambda (d2: C).(\lambda 
(u2: T).(\lambda (a: A).(arity g d2 u2 a))))) (or (ex2 C (\lambda (d2: 
C).(drop (S n) O (CHead x0 (Flat f) x1) (CHead d2 (Bind Abst) u1))) (\lambda 
(d2: C).(csuba g d1 d2))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: 
T).(\lambda (_: A).(drop (S n) O (CHead x0 (Flat f) x1) (CHead d2 (Bind Abbr) 
u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d1 d2)))) 
(\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 (asucc g 
a))))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 
a)))))) (\lambda (H9: (ex2 C (\lambda (d2: C).(drop (S n) O x0 (CHead d2 
(Bind Abst) u1))) (\lambda (d2: C).(csuba g d1 d2)))).(ex2_ind C (\lambda 
(d2: C).(drop (S n) O x0 (CHead d2 (Bind Abst) u1))) (\lambda (d2: C).(csuba 
g d1 d2)) (or (ex2 C (\lambda (d2: C).(drop (S n) O (CHead x0 (Flat f) x1) 
(CHead d2 (Bind Abst) u1))) (\lambda (d2: C).(csuba g d1 d2))) (ex4_3 C T A 
(\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(drop (S n) O (CHead x0 
(Flat f) x1) (CHead d2 (Bind Abbr) u2))))) (\lambda (d2: C).(\lambda (_: 
T).(\lambda (_: A).(csuba g d1 d2)))) (\lambda (_: C).(\lambda (_: 
T).(\lambda (a: A).(arity g d1 u1 (asucc g a))))) (\lambda (d2: C).(\lambda 
(u2: T).(\lambda (a: A).(arity g d2 u2 a)))))) (\lambda (x: C).(\lambda (H10: 
(drop (S n) O x0 (CHead x (Bind Abst) u1))).(\lambda (H11: (csuba g d1 
x)).(or_introl (ex2 C (\lambda (d2: C).(drop (S n) O (CHead x0 (Flat f) x1) 
(CHead d2 (Bind Abst) u1))) (\lambda (d2: C).(csuba g d1 d2))) (ex4_3 C T A 
(\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(drop (S n) O (CHead x0 
(Flat f) x1) (CHead d2 (Bind Abbr) u2))))) (\lambda (d2: C).(\lambda (_: 
T).(\lambda (_: A).(csuba g d1 d2)))) (\lambda (_: C).(\lambda (_: 
T).(\lambda (a: A).(arity g d1 u1 (asucc g a))))) (\lambda (d2: C).(\lambda 
(u2: T).(\lambda (a: A).(arity g d2 u2 a))))) (ex_intro2 C (\lambda (d2: 
C).(drop (S n) O (CHead x0 (Flat f) x1) (CHead d2 (Bind Abst) u1))) (\lambda 
(d2: C).(csuba g d1 d2)) x (drop_drop (Flat f) n x0 (CHead x (Bind Abst) u1) 
H10 x1) H11))))) H9)) (\lambda (H9: (ex4_3 C T A (\lambda (d2: C).(\lambda 
(u2: T).(\lambda (_: A).(drop (S n) O x0 (CHead d2 (Bind Abbr) u2))))) 
(\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d1 d2)))) (\lambda 
(_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 (asucc g a))))) 
(\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 
a)))))).(ex4_3_ind C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: 
A).(drop (S n) O x0 (CHead d2 (Bind Abbr) u2))))) (\lambda (d2: C).(\lambda 
(_: T).(\lambda (_: A).(csuba g d1 d2)))) (\lambda (_: C).(\lambda (_: 
T).(\lambda (a: A).(arity g d1 u1 (asucc g a))))) (\lambda (d2: C).(\lambda 
(u2: T).(\lambda (a: A).(arity g d2 u2 a)))) (or (ex2 C (\lambda (d2: 
C).(drop (S n) O (CHead x0 (Flat f) x1) (CHead d2 (Bind Abst) u1))) (\lambda 
(d2: C).(csuba g d1 d2))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: 
T).(\lambda (_: A).(drop (S n) O (CHead x0 (Flat f) x1) (CHead d2 (Bind Abbr) 
u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d1 d2)))) 
(\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 (asucc g 
a))))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 
a)))))) (\lambda (x2: C).(\lambda (x3: T).(\lambda (x4: A).(\lambda (H10: 
(drop (S n) O x0 (CHead x2 (Bind Abbr) x3))).(\lambda (H11: (csuba g d1 
x2)).(\lambda (H12: (arity g d1 u1 (asucc g x4))).(\lambda (H13: (arity g x2 
x3 x4)).(or_intror (ex2 C (\lambda (d2: C).(drop (S n) O (CHead x0 (Flat f) 
x1) (CHead d2 (Bind Abst) u1))) (\lambda (d2: C).(csuba g d1 d2))) (ex4_3 C T 
A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(drop (S n) O (CHead x0 
(Flat f) x1) (CHead d2 (Bind Abbr) u2))))) (\lambda (d2: C).(\lambda (_: 
T).(\lambda (_: A).(csuba g d1 d2)))) (\lambda (_: C).(\lambda (_: 
T).(\lambda (a: A).(arity g d1 u1 (asucc g a))))) (\lambda (d2: C).(\lambda 
(u2: T).(\lambda (a: A).(arity g d2 u2 a))))) (ex4_3_intro C T A (\lambda 
(d2: C).(\lambda (u2: T).(\lambda (_: A).(drop (S n) O (CHead x0 (Flat f) x1) 
(CHead d2 (Bind Abbr) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: 
A).(csuba g d1 d2)))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity 
g d1 u1 (asucc g a))))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: 
A).(arity g d2 u2 a)))) x2 x3 x4 (drop_drop (Flat f) n x0 (CHead x2 (Bind 
Abbr) x3) H10 x1) H11 H12 H13))))))))) H9)) H8)) c2 H6))))) H5)))))) k H2 
(drop_gen_drop k c (CHead d1 (Bind Abst) u1) t n H1)))))))))))) c1)))) i).
(* COMMENTS
Initial nodes: 12528
END *)

theorem csuba_drop_abst_rev:
 \forall (i: nat).(\forall (c1: C).(\forall (d1: C).(\forall (u: T).((drop i 
O c1 (CHead d1 (Bind Abst) u)) \to (\forall (g: G).(\forall (c2: C).((csuba g 
c2 c1) \to (or (ex2 C (\lambda (d2: C).(drop i O c2 (CHead d2 (Bind Abst) 
u))) (\lambda (d2: C).(csuba g d2 d1))) (ex2_2 C T (\lambda (d2: C).(\lambda 
(u2: T).(drop i O c2 (CHead d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda 
(_: T).(csuba g d2 d1))))))))))))
\def
 \lambda (i: nat).(nat_ind (\lambda (n: nat).(\forall (c1: C).(\forall (d1: 
C).(\forall (u: T).((drop n O c1 (CHead d1 (Bind Abst) u)) \to (\forall (g: 
G).(\forall (c2: C).((csuba g c2 c1) \to (or (ex2 C (\lambda (d2: C).(drop n 
O c2 (CHead d2 (Bind Abst) u))) (\lambda (d2: C).(csuba g d2 d1))) (ex2_2 C T 
(\lambda (d2: C).(\lambda (u2: T).(drop n O c2 (CHead d2 (Bind Void) u2)))) 
(\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1))))))))))))) (\lambda (c1: 
C).(\lambda (d1: C).(\lambda (u: T).(\lambda (H: (drop O O c1 (CHead d1 (Bind 
Abst) u))).(\lambda (g: G).(\lambda (c2: C).(\lambda (H0: (csuba g c2 
c1)).(let H1 \def (eq_ind C c1 (\lambda (c: C).(csuba g c2 c)) H0 (CHead d1 
(Bind Abst) u) (drop_gen_refl c1 (CHead d1 (Bind Abst) u) H)) in (let H_x 
\def (csuba_gen_abst_rev g d1 c2 u H1) in (let H2 \def H_x in (or_ind (ex2 C 
(\lambda (d2: C).(eq C c2 (CHead d2 (Bind Abst) u))) (\lambda (d2: C).(csuba 
g d2 d1))) (ex2_2 C T (\lambda (d2: C).(\lambda (u2: T).(eq C c2 (CHead d2 
(Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1)))) (or 
(ex2 C (\lambda (d2: C).(drop O O c2 (CHead d2 (Bind Abst) u))) (\lambda (d2: 
C).(csuba g d2 d1))) (ex2_2 C T (\lambda (d2: C).(\lambda (u2: T).(drop O O 
c2 (CHead d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 
d1))))) (\lambda (H3: (ex2 C (\lambda (d2: C).(eq C c2 (CHead d2 (Bind Abst) 
u))) (\lambda (d2: C).(csuba g d2 d1)))).(ex2_ind C (\lambda (d2: C).(eq C c2 
(CHead d2 (Bind Abst) u))) (\lambda (d2: C).(csuba g d2 d1)) (or (ex2 C 
(\lambda (d2: C).(drop O O c2 (CHead d2 (Bind Abst) u))) (\lambda (d2: 
C).(csuba g d2 d1))) (ex2_2 C T (\lambda (d2: C).(\lambda (u2: T).(drop O O 
c2 (CHead d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 
d1))))) (\lambda (x: C).(\lambda (H4: (eq C c2 (CHead x (Bind Abst) 
u))).(\lambda (H5: (csuba g x d1)).(eq_ind_r C (CHead x (Bind Abst) u) 
(\lambda (c: C).(or (ex2 C (\lambda (d2: C).(drop O O c (CHead d2 (Bind Abst) 
u))) (\lambda (d2: C).(csuba g d2 d1))) (ex2_2 C T (\lambda (d2: C).(\lambda 
(u2: T).(drop O O c (CHead d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda 
(_: T).(csuba g d2 d1)))))) (or_introl (ex2 C (\lambda (d2: C).(drop O O 
(CHead x (Bind Abst) u) (CHead d2 (Bind Abst) u))) (\lambda (d2: C).(csuba g 
d2 d1))) (ex2_2 C T (\lambda (d2: C).(\lambda (u2: T).(drop O O (CHead x 
(Bind Abst) u) (CHead d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: 
T).(csuba g d2 d1)))) (ex_intro2 C (\lambda (d2: C).(drop O O (CHead x (Bind 
Abst) u) (CHead d2 (Bind Abst) u))) (\lambda (d2: C).(csuba g d2 d1)) x 
(drop_refl (CHead x (Bind Abst) u)) H5)) c2 H4)))) H3)) (\lambda (H3: (ex2_2 
C T (\lambda (d2: C).(\lambda (u2: T).(eq C c2 (CHead d2 (Bind Void) u2)))) 
(\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1))))).(ex2_2_ind C T (\lambda 
(d2: C).(\lambda (u2: T).(eq C c2 (CHead d2 (Bind Void) u2)))) (\lambda (d2: 
C).(\lambda (_: T).(csuba g d2 d1))) (or (ex2 C (\lambda (d2: C).(drop O O c2 
(CHead d2 (Bind Abst) u))) (\lambda (d2: C).(csuba g d2 d1))) (ex2_2 C T 
(\lambda (d2: C).(\lambda (u2: T).(drop O O c2 (CHead d2 (Bind Void) u2)))) 
(\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1))))) (\lambda (x0: 
C).(\lambda (x1: T).(\lambda (H4: (eq C c2 (CHead x0 (Bind Void) 
x1))).(\lambda (H5: (csuba g x0 d1)).(eq_ind_r C (CHead x0 (Bind Void) x1) 
(\lambda (c: C).(or (ex2 C (\lambda (d2: C).(drop O O c (CHead d2 (Bind Abst) 
u))) (\lambda (d2: C).(csuba g d2 d1))) (ex2_2 C T (\lambda (d2: C).(\lambda 
(u2: T).(drop O O c (CHead d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda 
(_: T).(csuba g d2 d1)))))) (or_intror (ex2 C (\lambda (d2: C).(drop O O 
(CHead x0 (Bind Void) x1) (CHead d2 (Bind Abst) u))) (\lambda (d2: C).(csuba 
g d2 d1))) (ex2_2 C T (\lambda (d2: C).(\lambda (u2: T).(drop O O (CHead x0 
(Bind Void) x1) (CHead d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: 
T).(csuba g d2 d1)))) (ex2_2_intro C T (\lambda (d2: C).(\lambda (u2: 
T).(drop O O (CHead x0 (Bind Void) x1) (CHead d2 (Bind Void) u2)))) (\lambda 
(d2: C).(\lambda (_: T).(csuba g d2 d1))) x0 x1 (drop_refl (CHead x0 (Bind 
Void) x1)) H5)) c2 H4))))) H3)) H2))))))))))) (\lambda (n: nat).(\lambda (H: 
((\forall (c1: C).(\forall (d1: C).(\forall (u: T).((drop n O c1 (CHead d1 
(Bind Abst) u)) \to (\forall (g: G).(\forall (c2: C).((csuba g c2 c1) \to (or 
(ex2 C (\lambda (d2: C).(drop n O c2 (CHead d2 (Bind Abst) u))) (\lambda (d2: 
C).(csuba g d2 d1))) (ex2_2 C T (\lambda (d2: C).(\lambda (u2: T).(drop n O 
c2 (CHead d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 
d1)))))))))))))).(\lambda (c1: C).(C_ind (\lambda (c: C).(\forall (d1: 
C).(\forall (u: T).((drop (S n) O c (CHead d1 (Bind Abst) u)) \to (\forall 
(g: G).(\forall (c2: C).((csuba g c2 c) \to (or (ex2 C (\lambda (d2: C).(drop 
(S n) O c2 (CHead d2 (Bind Abst) u))) (\lambda (d2: C).(csuba g d2 d1))) 
(ex2_2 C T (\lambda (d2: C).(\lambda (u2: T).(drop (S n) O c2 (CHead d2 (Bind 
Void) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1)))))))))))) 
(\lambda (n0: nat).(\lambda (d1: C).(\lambda (u: T).(\lambda (H0: (drop (S n) 
O (CSort n0) (CHead d1 (Bind Abst) u))).(\lambda (g: G).(\lambda (c2: 
C).(\lambda (_: (csuba g c2 (CSort n0))).(and3_ind (eq C (CHead d1 (Bind 
Abst) u) (CSort n0)) (eq nat (S n) O) (eq nat O O) (or (ex2 C (\lambda (d2: 
C).(drop (S n) O c2 (CHead d2 (Bind Abst) u))) (\lambda (d2: C).(csuba g d2 
d1))) (ex2_2 C T (\lambda (d2: C).(\lambda (u2: T).(drop (S n) O c2 (CHead d2 
(Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1))))) 
(\lambda (_: (eq C (CHead d1 (Bind Abst) u) (CSort n0))).(\lambda (H3: (eq 
nat (S n) O)).(\lambda (_: (eq nat O O)).(let H5 \def (eq_ind nat (S n) 
(\lambda (ee: nat).(match ee in nat return (\lambda (_: nat).Prop) with [O 
\Rightarrow False | (S _) \Rightarrow True])) I O H3) in (False_ind (or (ex2 
C (\lambda (d2: C).(drop (S n) O c2 (CHead d2 (Bind Abst) u))) (\lambda (d2: 
C).(csuba g d2 d1))) (ex2_2 C T (\lambda (d2: C).(\lambda (u2: T).(drop (S n) 
O c2 (CHead d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g 
d2 d1))))) H5))))) (drop_gen_sort n0 (S n) O (CHead d1 (Bind Abst) u) 
H0))))))))) (\lambda (c: C).(\lambda (H0: ((\forall (d1: C).(\forall (u: 
T).((drop (S n) O c (CHead d1 (Bind Abst) u)) \to (\forall (g: G).(\forall 
(c2: C).((csuba g c2 c) \to (or (ex2 C (\lambda (d2: C).(drop (S n) O c2 
(CHead d2 (Bind Abst) u))) (\lambda (d2: C).(csuba g d2 d1))) (ex2_2 C T 
(\lambda (d2: C).(\lambda (u2: T).(drop (S n) O c2 (CHead d2 (Bind Void) 
u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1))))))))))))).(\lambda 
(k: K).(\lambda (t: T).(\lambda (d1: C).(\lambda (u: T).(\lambda (H1: (drop 
(S n) O (CHead c k t) (CHead d1 (Bind Abst) u))).(\lambda (g: G).(\lambda 
(c2: C).(\lambda (H2: (csuba g c2 (CHead c k t))).(K_ind (\lambda (k0: 
K).((csuba g c2 (CHead c k0 t)) \to ((drop (r k0 n) O c (CHead d1 (Bind Abst) 
u)) \to (or (ex2 C (\lambda (d2: C).(drop (S n) O c2 (CHead d2 (Bind Abst) 
u))) (\lambda (d2: C).(csuba g d2 d1))) (ex2_2 C T (\lambda (d2: C).(\lambda 
(u2: T).(drop (S n) O c2 (CHead d2 (Bind Void) u2)))) (\lambda (d2: 
C).(\lambda (_: T).(csuba g d2 d1)))))))) (\lambda (b: B).(\lambda (H3: 
(csuba g c2 (CHead c (Bind b) t))).(\lambda (H4: (drop (r (Bind b) n) O c 
(CHead d1 (Bind Abst) u))).(B_ind (\lambda (b0: B).((csuba g c2 (CHead c 
(Bind b0) t)) \to ((drop (r (Bind b0) n) O c (CHead d1 (Bind Abst) u)) \to 
(or (ex2 C (\lambda (d2: C).(drop (S n) O c2 (CHead d2 (Bind Abst) u))) 
(\lambda (d2: C).(csuba g d2 d1))) (ex2_2 C T (\lambda (d2: C).(\lambda (u2: 
T).(drop (S n) O c2 (CHead d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda 
(_: T).(csuba g d2 d1)))))))) (\lambda (H5: (csuba g c2 (CHead c (Bind Abbr) 
t))).(\lambda (H6: (drop (r (Bind Abbr) n) O c (CHead d1 (Bind Abst) 
u))).(let H_x \def (csuba_gen_abbr_rev g c c2 t H5) in (let H7 \def H_x in 
(or3_ind (ex2 C (\lambda (d2: C).(eq C c2 (CHead d2 (Bind Abbr) t))) (\lambda 
(d2: C).(csuba g d2 c))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: 
T).(\lambda (_: A).(eq C c2 (CHead d2 (Bind Abst) u2))))) (\lambda (d2: 
C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 c)))) (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) (\lambda 
(_: C).(\lambda (_: T).(\lambda (a: A).(arity g c t a))))) (ex2_2 C T 
(\lambda (d2: C).(\lambda (u2: T).(eq C c2 (CHead d2 (Bind Void) u2)))) 
(\lambda (d2: C).(\lambda (_: T).(csuba g d2 c)))) (or (ex2 C (\lambda (d2: 
C).(drop (S n) O c2 (CHead d2 (Bind Abst) u))) (\lambda (d2: C).(csuba g d2 
d1))) (ex2_2 C T (\lambda (d2: C).(\lambda (u2: T).(drop (S n) O c2 (CHead d2 
(Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1))))) 
(\lambda (H8: (ex2 C (\lambda (d2: C).(eq C c2 (CHead d2 (Bind Abbr) t))) 
(\lambda (d2: C).(csuba g d2 c)))).(ex2_ind C (\lambda (d2: C).(eq C c2 
(CHead d2 (Bind Abbr) t))) (\lambda (d2: C).(csuba g d2 c)) (or (ex2 C 
(\lambda (d2: C).(drop (S n) O c2 (CHead d2 (Bind Abst) u))) (\lambda (d2: 
C).(csuba g d2 d1))) (ex2_2 C T (\lambda (d2: C).(\lambda (u2: T).(drop (S n) 
O c2 (CHead d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g 
d2 d1))))) (\lambda (x: C).(\lambda (H9: (eq C c2 (CHead x (Bind Abbr) 
t))).(\lambda (H10: (csuba g x c)).(eq_ind_r C (CHead x (Bind Abbr) t) 
(\lambda (c0: C).(or (ex2 C (\lambda (d2: C).(drop (S n) O c0 (CHead d2 (Bind 
Abst) u))) (\lambda (d2: C).(csuba g d2 d1))) (ex2_2 C T (\lambda (d2: 
C).(\lambda (u2: T).(drop (S n) O c0 (CHead d2 (Bind Void) u2)))) (\lambda 
(d2: C).(\lambda (_: T).(csuba g d2 d1)))))) (let H11 \def (H c d1 u H6 g x 
H10) in (or_ind (ex2 C (\lambda (d2: C).(drop n O x (CHead d2 (Bind Abst) 
u))) (\lambda (d2: C).(csuba g d2 d1))) (ex2_2 C T (\lambda (d2: C).(\lambda 
(u2: T).(drop n O x (CHead d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda 
(_: T).(csuba g d2 d1)))) (or (ex2 C (\lambda (d2: C).(drop (S n) O (CHead x 
(Bind Abbr) t) (CHead d2 (Bind Abst) u))) (\lambda (d2: C).(csuba g d2 d1))) 
(ex2_2 C T (\lambda (d2: C).(\lambda (u2: T).(drop (S n) O (CHead x (Bind 
Abbr) t) (CHead d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba 
g d2 d1))))) (\lambda (H12: (ex2 C (\lambda (d2: C).(drop n O x (CHead d2 
(Bind Abst) u))) (\lambda (d2: C).(csuba g d2 d1)))).(ex2_ind C (\lambda (d2: 
C).(drop n O x (CHead d2 (Bind Abst) u))) (\lambda (d2: C).(csuba g d2 d1)) 
(or (ex2 C (\lambda (d2: C).(drop (S n) O (CHead x (Bind Abbr) t) (CHead d2 
(Bind Abst) u))) (\lambda (d2: C).(csuba g d2 d1))) (ex2_2 C T (\lambda (d2: 
C).(\lambda (u2: T).(drop (S n) O (CHead x (Bind Abbr) t) (CHead d2 (Bind 
Void) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1))))) (\lambda 
(x0: C).(\lambda (H13: (drop n O x (CHead x0 (Bind Abst) u))).(\lambda (H14: 
(csuba g x0 d1)).(or_introl (ex2 C (\lambda (d2: C).(drop (S n) O (CHead x 
(Bind Abbr) t) (CHead d2 (Bind Abst) u))) (\lambda (d2: C).(csuba g d2 d1))) 
(ex2_2 C T (\lambda (d2: C).(\lambda (u2: T).(drop (S n) O (CHead x (Bind 
Abbr) t) (CHead d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba 
g d2 d1)))) (ex_intro2 C (\lambda (d2: C).(drop (S n) O (CHead x (Bind Abbr) 
t) (CHead d2 (Bind Abst) u))) (\lambda (d2: C).(csuba g d2 d1)) x0 (drop_drop 
(Bind Abbr) n x (CHead x0 (Bind Abst) u) H13 t) H14))))) H12)) (\lambda (H12: 
(ex2_2 C T (\lambda (d2: C).(\lambda (u2: T).(drop n O x (CHead d2 (Bind 
Void) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1))))).(ex2_2_ind 
C T (\lambda (d2: C).(\lambda (u2: T).(drop n O x (CHead d2 (Bind Void) 
u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1))) (or (ex2 C (\lambda 
(d2: C).(drop (S n) O (CHead x (Bind Abbr) t) (CHead d2 (Bind Abst) u))) 
(\lambda (d2: C).(csuba g d2 d1))) (ex2_2 C T (\lambda (d2: C).(\lambda (u2: 
T).(drop (S n) O (CHead x (Bind Abbr) t) (CHead d2 (Bind Void) u2)))) 
(\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1))))) (\lambda (x0: 
C).(\lambda (x1: T).(\lambda (H13: (drop n O x (CHead x0 (Bind Void) 
x1))).(\lambda (H14: (csuba g x0 d1)).(or_intror (ex2 C (\lambda (d2: 
C).(drop (S n) O (CHead x (Bind Abbr) t) (CHead d2 (Bind Abst) u))) (\lambda 
(d2: C).(csuba g d2 d1))) (ex2_2 C T (\lambda (d2: C).(\lambda (u2: T).(drop 
(S n) O (CHead x (Bind Abbr) t) (CHead d2 (Bind Void) u2)))) (\lambda (d2: 
C).(\lambda (_: T).(csuba g d2 d1)))) (ex2_2_intro C T (\lambda (d2: 
C).(\lambda (u2: T).(drop (S n) O (CHead x (Bind Abbr) t) (CHead d2 (Bind 
Void) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1))) x0 x1 
(drop_drop (Bind Abbr) n x (CHead x0 (Bind Void) x1) H13 t) H14)))))) H12)) 
H11)) c2 H9)))) H8)) (\lambda (H8: (ex4_3 C T A (\lambda (d2: C).(\lambda 
(u2: T).(\lambda (_: A).(eq C c2 (CHead d2 (Bind Abst) u2))))) (\lambda (d2: 
C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 c)))) (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) (\lambda 
(_: C).(\lambda (_: T).(\lambda (a: A).(arity g c t a)))))).(ex4_3_ind C T A 
(\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(eq C c2 (CHead d2 (Bind 
Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 
c)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 (asucc 
g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g c t a)))) 
(or (ex2 C (\lambda (d2: C).(drop (S n) O c2 (CHead d2 (Bind Abst) u))) 
(\lambda (d2: C).(csuba g d2 d1))) (ex2_2 C T (\lambda (d2: C).(\lambda (u2: 
T).(drop (S n) O c2 (CHead d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda 
(_: T).(csuba g d2 d1))))) (\lambda (x0: C).(\lambda (x1: T).(\lambda (x2: 
A).(\lambda (H9: (eq C c2 (CHead x0 (Bind Abst) x1))).(\lambda (H10: (csuba g 
x0 c)).(\lambda (_: (arity g x0 x1 (asucc g x2))).(\lambda (_: (arity g c t 
x2)).(eq_ind_r C (CHead x0 (Bind Abst) x1) (\lambda (c0: C).(or (ex2 C 
(\lambda (d2: C).(drop (S n) O c0 (CHead d2 (Bind Abst) u))) (\lambda (d2: 
C).(csuba g d2 d1))) (ex2_2 C T (\lambda (d2: C).(\lambda (u2: T).(drop (S n) 
O c0 (CHead d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g 
d2 d1)))))) (let H13 \def (H c d1 u H6 g x0 H10) in (or_ind (ex2 C (\lambda 
(d2: C).(drop n O x0 (CHead d2 (Bind Abst) u))) (\lambda (d2: C).(csuba g d2 
d1))) (ex2_2 C T (\lambda (d2: C).(\lambda (u2: T).(drop n O x0 (CHead d2 
(Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1)))) (or 
(ex2 C (\lambda (d2: C).(drop (S n) O (CHead x0 (Bind Abst) x1) (CHead d2 
(Bind Abst) u))) (\lambda (d2: C).(csuba g d2 d1))) (ex2_2 C T (\lambda (d2: 
C).(\lambda (u2: T).(drop (S n) O (CHead x0 (Bind Abst) x1) (CHead d2 (Bind 
Void) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1))))) (\lambda 
(H14: (ex2 C (\lambda (d2: C).(drop n O x0 (CHead d2 (Bind Abst) u))) 
(\lambda (d2: C).(csuba g d2 d1)))).(ex2_ind C (\lambda (d2: C).(drop n O x0 
(CHead d2 (Bind Abst) u))) (\lambda (d2: C).(csuba g d2 d1)) (or (ex2 C 
(\lambda (d2: C).(drop (S n) O (CHead x0 (Bind Abst) x1) (CHead d2 (Bind 
Abst) u))) (\lambda (d2: C).(csuba g d2 d1))) (ex2_2 C T (\lambda (d2: 
C).(\lambda (u2: T).(drop (S n) O (CHead x0 (Bind Abst) x1) (CHead d2 (Bind 
Void) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1))))) (\lambda 
(x: C).(\lambda (H15: (drop n O x0 (CHead x (Bind Abst) u))).(\lambda (H16: 
(csuba g x d1)).(or_introl (ex2 C (\lambda (d2: C).(drop (S n) O (CHead x0 
(Bind Abst) x1) (CHead d2 (Bind Abst) u))) (\lambda (d2: C).(csuba g d2 d1))) 
(ex2_2 C T (\lambda (d2: C).(\lambda (u2: T).(drop (S n) O (CHead x0 (Bind 
Abst) x1) (CHead d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: 
T).(csuba g d2 d1)))) (ex_intro2 C (\lambda (d2: C).(drop (S n) O (CHead x0 
(Bind Abst) x1) (CHead d2 (Bind Abst) u))) (\lambda (d2: C).(csuba g d2 d1)) 
x (drop_drop (Bind Abst) n x0 (CHead x (Bind Abst) u) H15 x1) H16))))) H14)) 
(\lambda (H14: (ex2_2 C T (\lambda (d2: C).(\lambda (u2: T).(drop n O x0 
(CHead d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 
d1))))).(ex2_2_ind C T (\lambda (d2: C).(\lambda (u2: T).(drop n O x0 (CHead 
d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1))) (or 
(ex2 C (\lambda (d2: C).(drop (S n) O (CHead x0 (Bind Abst) x1) (CHead d2 
(Bind Abst) u))) (\lambda (d2: C).(csuba g d2 d1))) (ex2_2 C T (\lambda (d2: 
C).(\lambda (u2: T).(drop (S n) O (CHead x0 (Bind Abst) x1) (CHead d2 (Bind 
Void) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1))))) (\lambda 
(x3: C).(\lambda (x4: T).(\lambda (H15: (drop n O x0 (CHead x3 (Bind Void) 
x4))).(\lambda (H16: (csuba g x3 d1)).(or_intror (ex2 C (\lambda (d2: 
C).(drop (S n) O (CHead x0 (Bind Abst) x1) (CHead d2 (Bind Abst) u))) 
(\lambda (d2: C).(csuba g d2 d1))) (ex2_2 C T (\lambda (d2: C).(\lambda (u2: 
T).(drop (S n) O (CHead x0 (Bind Abst) x1) (CHead d2 (Bind Void) u2)))) 
(\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1)))) (ex2_2_intro C T (\lambda 
(d2: C).(\lambda (u2: T).(drop (S n) O (CHead x0 (Bind Abst) x1) (CHead d2 
(Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1))) x3 x4 
(drop_drop (Bind Abst) n x0 (CHead x3 (Bind Void) x4) H15 x1) H16)))))) H14)) 
H13)) c2 H9)))))))) H8)) (\lambda (H8: (ex2_2 C T (\lambda (d2: C).(\lambda 
(u2: T).(eq C c2 (CHead d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: 
T).(csuba g d2 c))))).(ex2_2_ind C T (\lambda (d2: C).(\lambda (u2: T).(eq C 
c2 (CHead d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 
c))) (or (ex2 C (\lambda (d2: C).(drop (S n) O c2 (CHead d2 (Bind Abst) u))) 
(\lambda (d2: C).(csuba g d2 d1))) (ex2_2 C T (\lambda (d2: C).(\lambda (u2: 
T).(drop (S n) O c2 (CHead d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda 
(_: T).(csuba g d2 d1))))) (\lambda (x0: C).(\lambda (x1: T).(\lambda (H9: 
(eq C c2 (CHead x0 (Bind Void) x1))).(\lambda (H10: (csuba g x0 c)).(eq_ind_r 
C (CHead x0 (Bind Void) x1) (\lambda (c0: C).(or (ex2 C (\lambda (d2: 
C).(drop (S n) O c0 (CHead d2 (Bind Abst) u))) (\lambda (d2: C).(csuba g d2 
d1))) (ex2_2 C T (\lambda (d2: C).(\lambda (u2: T).(drop (S n) O c0 (CHead d2 
(Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1)))))) (let 
H11 \def (H c d1 u H6 g x0 H10) in (or_ind (ex2 C (\lambda (d2: C).(drop n O 
x0 (CHead d2 (Bind Abst) u))) (\lambda (d2: C).(csuba g d2 d1))) (ex2_2 C T 
(\lambda (d2: C).(\lambda (u2: T).(drop n O x0 (CHead d2 (Bind Void) u2)))) 
(\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1)))) (or (ex2 C (\lambda (d2: 
C).(drop (S n) O (CHead x0 (Bind Void) x1) (CHead d2 (Bind Abst) u))) 
(\lambda (d2: C).(csuba g d2 d1))) (ex2_2 C T (\lambda (d2: C).(\lambda (u2: 
T).(drop (S n) O (CHead x0 (Bind Void) x1) (CHead d2 (Bind Void) u2)))) 
(\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1))))) (\lambda (H12: (ex2 C 
(\lambda (d2: C).(drop n O x0 (CHead d2 (Bind Abst) u))) (\lambda (d2: 
C).(csuba g d2 d1)))).(ex2_ind C (\lambda (d2: C).(drop n O x0 (CHead d2 
(Bind Abst) u))) (\lambda (d2: C).(csuba g d2 d1)) (or (ex2 C (\lambda (d2: 
C).(drop (S n) O (CHead x0 (Bind Void) x1) (CHead d2 (Bind Abst) u))) 
(\lambda (d2: C).(csuba g d2 d1))) (ex2_2 C T (\lambda (d2: C).(\lambda (u2: 
T).(drop (S n) O (CHead x0 (Bind Void) x1) (CHead d2 (Bind Void) u2)))) 
(\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1))))) (\lambda (x: C).(\lambda 
(H13: (drop n O x0 (CHead x (Bind Abst) u))).(\lambda (H14: (csuba g x 
d1)).(or_introl (ex2 C (\lambda (d2: C).(drop (S n) O (CHead x0 (Bind Void) 
x1) (CHead d2 (Bind Abst) u))) (\lambda (d2: C).(csuba g d2 d1))) (ex2_2 C T 
(\lambda (d2: C).(\lambda (u2: T).(drop (S n) O (CHead x0 (Bind Void) x1) 
(CHead d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 
d1)))) (ex_intro2 C (\lambda (d2: C).(drop (S n) O (CHead x0 (Bind Void) x1) 
(CHead d2 (Bind Abst) u))) (\lambda (d2: C).(csuba g d2 d1)) x (drop_drop 
(Bind Void) n x0 (CHead x (Bind Abst) u) H13 x1) H14))))) H12)) (\lambda 
(H12: (ex2_2 C T (\lambda (d2: C).(\lambda (u2: T).(drop n O x0 (CHead d2 
(Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 
d1))))).(ex2_2_ind C T (\lambda (d2: C).(\lambda (u2: T).(drop n O x0 (CHead 
d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1))) (or 
(ex2 C (\lambda (d2: C).(drop (S n) O (CHead x0 (Bind Void) x1) (CHead d2 
(Bind Abst) u))) (\lambda (d2: C).(csuba g d2 d1))) (ex2_2 C T (\lambda (d2: 
C).(\lambda (u2: T).(drop (S n) O (CHead x0 (Bind Void) x1) (CHead d2 (Bind 
Void) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1))))) (\lambda 
(x2: C).(\lambda (x3: T).(\lambda (H13: (drop n O x0 (CHead x2 (Bind Void) 
x3))).(\lambda (H14: (csuba g x2 d1)).(or_intror (ex2 C (\lambda (d2: 
C).(drop (S n) O (CHead x0 (Bind Void) x1) (CHead d2 (Bind Abst) u))) 
(\lambda (d2: C).(csuba g d2 d1))) (ex2_2 C T (\lambda (d2: C).(\lambda (u2: 
T).(drop (S n) O (CHead x0 (Bind Void) x1) (CHead d2 (Bind Void) u2)))) 
(\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1)))) (ex2_2_intro C T (\lambda 
(d2: C).(\lambda (u2: T).(drop (S n) O (CHead x0 (Bind Void) x1) (CHead d2 
(Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1))) x2 x3 
(drop_drop (Bind Void) n x0 (CHead x2 (Bind Void) x3) H13 x1) H14)))))) H12)) 
H11)) c2 H9))))) H8)) H7))))) (\lambda (H5: (csuba g c2 (CHead c (Bind Abst) 
t))).(\lambda (H6: (drop (r (Bind Abst) n) O c (CHead d1 (Bind Abst) 
u))).(let H_x \def (csuba_gen_abst_rev g c c2 t H5) in (let H7 \def H_x in 
(or_ind (ex2 C (\lambda (d2: C).(eq C c2 (CHead d2 (Bind Abst) t))) (\lambda 
(d2: C).(csuba g d2 c))) (ex2_2 C T (\lambda (d2: C).(\lambda (u2: T).(eq C 
c2 (CHead d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 
c)))) (or (ex2 C (\lambda (d2: C).(drop (S n) O c2 (CHead d2 (Bind Abst) u))) 
(\lambda (d2: C).(csuba g d2 d1))) (ex2_2 C T (\lambda (d2: C).(\lambda (u2: 
T).(drop (S n) O c2 (CHead d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda 
(_: T).(csuba g d2 d1))))) (\lambda (H8: (ex2 C (\lambda (d2: C).(eq C c2 
(CHead d2 (Bind Abst) t))) (\lambda (d2: C).(csuba g d2 c)))).(ex2_ind C 
(\lambda (d2: C).(eq C c2 (CHead d2 (Bind Abst) t))) (\lambda (d2: C).(csuba 
g d2 c)) (or (ex2 C (\lambda (d2: C).(drop (S n) O c2 (CHead d2 (Bind Abst) 
u))) (\lambda (d2: C).(csuba g d2 d1))) (ex2_2 C T (\lambda (d2: C).(\lambda 
(u2: T).(drop (S n) O c2 (CHead d2 (Bind Void) u2)))) (\lambda (d2: 
C).(\lambda (_: T).(csuba g d2 d1))))) (\lambda (x: C).(\lambda (H9: (eq C c2 
(CHead x (Bind Abst) t))).(\lambda (H10: (csuba g x c)).(eq_ind_r C (CHead x 
(Bind Abst) t) (\lambda (c0: C).(or (ex2 C (\lambda (d2: C).(drop (S n) O c0 
(CHead d2 (Bind Abst) u))) (\lambda (d2: C).(csuba g d2 d1))) (ex2_2 C T 
(\lambda (d2: C).(\lambda (u2: T).(drop (S n) O c0 (CHead d2 (Bind Void) 
u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1)))))) (let H11 \def (H 
c d1 u H6 g x H10) in (or_ind (ex2 C (\lambda (d2: C).(drop n O x (CHead d2 
(Bind Abst) u))) (\lambda (d2: C).(csuba g d2 d1))) (ex2_2 C T (\lambda (d2: 
C).(\lambda (u2: T).(drop n O x (CHead d2 (Bind Void) u2)))) (\lambda (d2: 
C).(\lambda (_: T).(csuba g d2 d1)))) (or (ex2 C (\lambda (d2: C).(drop (S n) 
O (CHead x (Bind Abst) t) (CHead d2 (Bind Abst) u))) (\lambda (d2: C).(csuba 
g d2 d1))) (ex2_2 C T (\lambda (d2: C).(\lambda (u2: T).(drop (S n) O (CHead 
x (Bind Abst) t) (CHead d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: 
T).(csuba g d2 d1))))) (\lambda (H12: (ex2 C (\lambda (d2: C).(drop n O x 
(CHead d2 (Bind Abst) u))) (\lambda (d2: C).(csuba g d2 d1)))).(ex2_ind C 
(\lambda (d2: C).(drop n O x (CHead d2 (Bind Abst) u))) (\lambda (d2: 
C).(csuba g d2 d1)) (or (ex2 C (\lambda (d2: C).(drop (S n) O (CHead x (Bind 
Abst) t) (CHead d2 (Bind Abst) u))) (\lambda (d2: C).(csuba g d2 d1))) (ex2_2 
C T (\lambda (d2: C).(\lambda (u2: T).(drop (S n) O (CHead x (Bind Abst) t) 
(CHead d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 
d1))))) (\lambda (x0: C).(\lambda (H13: (drop n O x (CHead x0 (Bind Abst) 
u))).(\lambda (H14: (csuba g x0 d1)).(or_introl (ex2 C (\lambda (d2: C).(drop 
(S n) O (CHead x (Bind Abst) t) (CHead d2 (Bind Abst) u))) (\lambda (d2: 
C).(csuba g d2 d1))) (ex2_2 C T (\lambda (d2: C).(\lambda (u2: T).(drop (S n) 
O (CHead x (Bind Abst) t) (CHead d2 (Bind Void) u2)))) (\lambda (d2: 
C).(\lambda (_: T).(csuba g d2 d1)))) (ex_intro2 C (\lambda (d2: C).(drop (S 
n) O (CHead x (Bind Abst) t) (CHead d2 (Bind Abst) u))) (\lambda (d2: 
C).(csuba g d2 d1)) x0 (drop_drop (Bind Abst) n x (CHead x0 (Bind Abst) u) 
H13 t) H14))))) H12)) (\lambda (H12: (ex2_2 C T (\lambda (d2: C).(\lambda 
(u2: T).(drop n O x (CHead d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda 
(_: T).(csuba g d2 d1))))).(ex2_2_ind C T (\lambda (d2: C).(\lambda (u2: 
T).(drop n O x (CHead d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: 
T).(csuba g d2 d1))) (or (ex2 C (\lambda (d2: C).(drop (S n) O (CHead x (Bind 
Abst) t) (CHead d2 (Bind Abst) u))) (\lambda (d2: C).(csuba g d2 d1))) (ex2_2 
C T (\lambda (d2: C).(\lambda (u2: T).(drop (S n) O (CHead x (Bind Abst) t) 
(CHead d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 
d1))))) (\lambda (x0: C).(\lambda (x1: T).(\lambda (H13: (drop n O x (CHead 
x0 (Bind Void) x1))).(\lambda (H14: (csuba g x0 d1)).(or_intror (ex2 C 
(\lambda (d2: C).(drop (S n) O (CHead x (Bind Abst) t) (CHead d2 (Bind Abst) 
u))) (\lambda (d2: C).(csuba g d2 d1))) (ex2_2 C T (\lambda (d2: C).(\lambda 
(u2: T).(drop (S n) O (CHead x (Bind Abst) t) (CHead d2 (Bind Void) u2)))) 
(\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1)))) (ex2_2_intro C T (\lambda 
(d2: C).(\lambda (u2: T).(drop (S n) O (CHead x (Bind Abst) t) (CHead d2 
(Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1))) x0 x1 
(drop_drop (Bind Abst) n x (CHead x0 (Bind Void) x1) H13 t) H14)))))) H12)) 
H11)) c2 H9)))) H8)) (\lambda (H8: (ex2_2 C T (\lambda (d2: C).(\lambda (u2: 
T).(eq C c2 (CHead d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: 
T).(csuba g d2 c))))).(ex2_2_ind C T (\lambda (d2: C).(\lambda (u2: T).(eq C 
c2 (CHead d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 
c))) (or (ex2 C (\lambda (d2: C).(drop (S n) O c2 (CHead d2 (Bind Abst) u))) 
(\lambda (d2: C).(csuba g d2 d1))) (ex2_2 C T (\lambda (d2: C).(\lambda (u2: 
T).(drop (S n) O c2 (CHead d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda 
(_: T).(csuba g d2 d1))))) (\lambda (x0: C).(\lambda (x1: T).(\lambda (H9: 
(eq C c2 (CHead x0 (Bind Void) x1))).(\lambda (H10: (csuba g x0 c)).(eq_ind_r 
C (CHead x0 (Bind Void) x1) (\lambda (c0: C).(or (ex2 C (\lambda (d2: 
C).(drop (S n) O c0 (CHead d2 (Bind Abst) u))) (\lambda (d2: C).(csuba g d2 
d1))) (ex2_2 C T (\lambda (d2: C).(\lambda (u2: T).(drop (S n) O c0 (CHead d2 
(Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1)))))) (let 
H11 \def (H c d1 u H6 g x0 H10) in (or_ind (ex2 C (\lambda (d2: C).(drop n O 
x0 (CHead d2 (Bind Abst) u))) (\lambda (d2: C).(csuba g d2 d1))) (ex2_2 C T 
(\lambda (d2: C).(\lambda (u2: T).(drop n O x0 (CHead d2 (Bind Void) u2)))) 
(\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1)))) (or (ex2 C (\lambda (d2: 
C).(drop (S n) O (CHead x0 (Bind Void) x1) (CHead d2 (Bind Abst) u))) 
(\lambda (d2: C).(csuba g d2 d1))) (ex2_2 C T (\lambda (d2: C).(\lambda (u2: 
T).(drop (S n) O (CHead x0 (Bind Void) x1) (CHead d2 (Bind Void) u2)))) 
(\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1))))) (\lambda (H12: (ex2 C 
(\lambda (d2: C).(drop n O x0 (CHead d2 (Bind Abst) u))) (\lambda (d2: 
C).(csuba g d2 d1)))).(ex2_ind C (\lambda (d2: C).(drop n O x0 (CHead d2 
(Bind Abst) u))) (\lambda (d2: C).(csuba g d2 d1)) (or (ex2 C (\lambda (d2: 
C).(drop (S n) O (CHead x0 (Bind Void) x1) (CHead d2 (Bind Abst) u))) 
(\lambda (d2: C).(csuba g d2 d1))) (ex2_2 C T (\lambda (d2: C).(\lambda (u2: 
T).(drop (S n) O (CHead x0 (Bind Void) x1) (CHead d2 (Bind Void) u2)))) 
(\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1))))) (\lambda (x: C).(\lambda 
(H13: (drop n O x0 (CHead x (Bind Abst) u))).(\lambda (H14: (csuba g x 
d1)).(or_introl (ex2 C (\lambda (d2: C).(drop (S n) O (CHead x0 (Bind Void) 
x1) (CHead d2 (Bind Abst) u))) (\lambda (d2: C).(csuba g d2 d1))) (ex2_2 C T 
(\lambda (d2: C).(\lambda (u2: T).(drop (S n) O (CHead x0 (Bind Void) x1) 
(CHead d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 
d1)))) (ex_intro2 C (\lambda (d2: C).(drop (S n) O (CHead x0 (Bind Void) x1) 
(CHead d2 (Bind Abst) u))) (\lambda (d2: C).(csuba g d2 d1)) x (drop_drop 
(Bind Void) n x0 (CHead x (Bind Abst) u) H13 x1) H14))))) H12)) (\lambda 
(H12: (ex2_2 C T (\lambda (d2: C).(\lambda (u2: T).(drop n O x0 (CHead d2 
(Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 
d1))))).(ex2_2_ind C T (\lambda (d2: C).(\lambda (u2: T).(drop n O x0 (CHead 
d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1))) (or 
(ex2 C (\lambda (d2: C).(drop (S n) O (CHead x0 (Bind Void) x1) (CHead d2 
(Bind Abst) u))) (\lambda (d2: C).(csuba g d2 d1))) (ex2_2 C T (\lambda (d2: 
C).(\lambda (u2: T).(drop (S n) O (CHead x0 (Bind Void) x1) (CHead d2 (Bind 
Void) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1))))) (\lambda 
(x2: C).(\lambda (x3: T).(\lambda (H13: (drop n O x0 (CHead x2 (Bind Void) 
x3))).(\lambda (H14: (csuba g x2 d1)).(or_intror (ex2 C (\lambda (d2: 
C).(drop (S n) O (CHead x0 (Bind Void) x1) (CHead d2 (Bind Abst) u))) 
(\lambda (d2: C).(csuba g d2 d1))) (ex2_2 C T (\lambda (d2: C).(\lambda (u2: 
T).(drop (S n) O (CHead x0 (Bind Void) x1) (CHead d2 (Bind Void) u2)))) 
(\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1)))) (ex2_2_intro C T (\lambda 
(d2: C).(\lambda (u2: T).(drop (S n) O (CHead x0 (Bind Void) x1) (CHead d2 
(Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1))) x2 x3 
(drop_drop (Bind Void) n x0 (CHead x2 (Bind Void) x3) H13 x1) H14)))))) H12)) 
H11)) c2 H9))))) H8)) H7))))) (\lambda (H5: (csuba g c2 (CHead c (Bind Void) 
t))).(\lambda (H6: (drop (r (Bind Void) n) O c (CHead d1 (Bind Abst) 
u))).(let H_x \def (csuba_gen_void_rev g c c2 t H5) in (let H7 \def H_x in 
(ex2_ind C (\lambda (d2: C).(eq C c2 (CHead d2 (Bind Void) t))) (\lambda (d2: 
C).(csuba g d2 c)) (or (ex2 C (\lambda (d2: C).(drop (S n) O c2 (CHead d2 
(Bind Abst) u))) (\lambda (d2: C).(csuba g d2 d1))) (ex2_2 C T (\lambda (d2: 
C).(\lambda (u2: T).(drop (S n) O c2 (CHead d2 (Bind Void) u2)))) (\lambda 
(d2: C).(\lambda (_: T).(csuba g d2 d1))))) (\lambda (x: C).(\lambda (H8: (eq 
C c2 (CHead x (Bind Void) t))).(\lambda (H9: (csuba g x c)).(eq_ind_r C 
(CHead x (Bind Void) t) (\lambda (c0: C).(or (ex2 C (\lambda (d2: C).(drop (S 
n) O c0 (CHead d2 (Bind Abst) u))) (\lambda (d2: C).(csuba g d2 d1))) (ex2_2 
C T (\lambda (d2: C).(\lambda (u2: T).(drop (S n) O c0 (CHead d2 (Bind Void) 
u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1)))))) (let H10 \def (H 
c d1 u H6 g x H9) in (or_ind (ex2 C (\lambda (d2: C).(drop n O x (CHead d2 
(Bind Abst) u))) (\lambda (d2: C).(csuba g d2 d1))) (ex2_2 C T (\lambda (d2: 
C).(\lambda (u2: T).(drop n O x (CHead d2 (Bind Void) u2)))) (\lambda (d2: 
C).(\lambda (_: T).(csuba g d2 d1)))) (or (ex2 C (\lambda (d2: C).(drop (S n) 
O (CHead x (Bind Void) t) (CHead d2 (Bind Abst) u))) (\lambda (d2: C).(csuba 
g d2 d1))) (ex2_2 C T (\lambda (d2: C).(\lambda (u2: T).(drop (S n) O (CHead 
x (Bind Void) t) (CHead d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: 
T).(csuba g d2 d1))))) (\lambda (H11: (ex2 C (\lambda (d2: C).(drop n O x 
(CHead d2 (Bind Abst) u))) (\lambda (d2: C).(csuba g d2 d1)))).(ex2_ind C 
(\lambda (d2: C).(drop n O x (CHead d2 (Bind Abst) u))) (\lambda (d2: 
C).(csuba g d2 d1)) (or (ex2 C (\lambda (d2: C).(drop (S n) O (CHead x (Bind 
Void) t) (CHead d2 (Bind Abst) u))) (\lambda (d2: C).(csuba g d2 d1))) (ex2_2 
C T (\lambda (d2: C).(\lambda (u2: T).(drop (S n) O (CHead x (Bind Void) t) 
(CHead d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 
d1))))) (\lambda (x0: C).(\lambda (H12: (drop n O x (CHead x0 (Bind Abst) 
u))).(\lambda (H13: (csuba g x0 d1)).(or_introl (ex2 C (\lambda (d2: C).(drop 
(S n) O (CHead x (Bind Void) t) (CHead d2 (Bind Abst) u))) (\lambda (d2: 
C).(csuba g d2 d1))) (ex2_2 C T (\lambda (d2: C).(\lambda (u2: T).(drop (S n) 
O (CHead x (Bind Void) t) (CHead d2 (Bind Void) u2)))) (\lambda (d2: 
C).(\lambda (_: T).(csuba g d2 d1)))) (ex_intro2 C (\lambda (d2: C).(drop (S 
n) O (CHead x (Bind Void) t) (CHead d2 (Bind Abst) u))) (\lambda (d2: 
C).(csuba g d2 d1)) x0 (drop_drop (Bind Void) n x (CHead x0 (Bind Abst) u) 
H12 t) H13))))) H11)) (\lambda (H11: (ex2_2 C T (\lambda (d2: C).(\lambda 
(u2: T).(drop n O x (CHead d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda 
(_: T).(csuba g d2 d1))))).(ex2_2_ind C T (\lambda (d2: C).(\lambda (u2: 
T).(drop n O x (CHead d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: 
T).(csuba g d2 d1))) (or (ex2 C (\lambda (d2: C).(drop (S n) O (CHead x (Bind 
Void) t) (CHead d2 (Bind Abst) u))) (\lambda (d2: C).(csuba g d2 d1))) (ex2_2 
C T (\lambda (d2: C).(\lambda (u2: T).(drop (S n) O (CHead x (Bind Void) t) 
(CHead d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 
d1))))) (\lambda (x0: C).(\lambda (x1: T).(\lambda (H12: (drop n O x (CHead 
x0 (Bind Void) x1))).(\lambda (H13: (csuba g x0 d1)).(or_intror (ex2 C 
(\lambda (d2: C).(drop (S n) O (CHead x (Bind Void) t) (CHead d2 (Bind Abst) 
u))) (\lambda (d2: C).(csuba g d2 d1))) (ex2_2 C T (\lambda (d2: C).(\lambda 
(u2: T).(drop (S n) O (CHead x (Bind Void) t) (CHead d2 (Bind Void) u2)))) 
(\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1)))) (ex2_2_intro C T (\lambda 
(d2: C).(\lambda (u2: T).(drop (S n) O (CHead x (Bind Void) t) (CHead d2 
(Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1))) x0 x1 
(drop_drop (Bind Void) n x (CHead x0 (Bind Void) x1) H12 t) H13)))))) H11)) 
H10)) c2 H8)))) H7))))) b H3 H4)))) (\lambda (f: F).(\lambda (H3: (csuba g c2 
(CHead c (Flat f) t))).(\lambda (H4: (drop (r (Flat f) n) O c (CHead d1 (Bind 
Abst) u))).(let H_x \def (csuba_gen_flat_rev g c c2 t f H3) in (let H5 \def 
H_x in (ex2_2_ind C T (\lambda (d2: C).(\lambda (u2: T).(eq C c2 (CHead d2 
(Flat f) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 c))) (or (ex2 C 
(\lambda (d2: C).(drop (S n) O c2 (CHead d2 (Bind Abst) u))) (\lambda (d2: 
C).(csuba g d2 d1))) (ex2_2 C T (\lambda (d2: C).(\lambda (u2: T).(drop (S n) 
O c2 (CHead d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g 
d2 d1))))) (\lambda (x0: C).(\lambda (x1: T).(\lambda (H6: (eq C c2 (CHead x0 
(Flat f) x1))).(\lambda (H7: (csuba g x0 c)).(eq_ind_r C (CHead x0 (Flat f) 
x1) (\lambda (c0: C).(or (ex2 C (\lambda (d2: C).(drop (S n) O c0 (CHead d2 
(Bind Abst) u))) (\lambda (d2: C).(csuba g d2 d1))) (ex2_2 C T (\lambda (d2: 
C).(\lambda (u2: T).(drop (S n) O c0 (CHead d2 (Bind Void) u2)))) (\lambda 
(d2: C).(\lambda (_: T).(csuba g d2 d1)))))) (let H8 \def (H0 d1 u H4 g x0 
H7) in (or_ind (ex2 C (\lambda (d2: C).(drop (S n) O x0 (CHead d2 (Bind Abst) 
u))) (\lambda (d2: C).(csuba g d2 d1))) (ex2_2 C T (\lambda (d2: C).(\lambda 
(u2: T).(drop (S n) O x0 (CHead d2 (Bind Void) u2)))) (\lambda (d2: 
C).(\lambda (_: T).(csuba g d2 d1)))) (or (ex2 C (\lambda (d2: C).(drop (S n) 
O (CHead x0 (Flat f) x1) (CHead d2 (Bind Abst) u))) (\lambda (d2: C).(csuba g 
d2 d1))) (ex2_2 C T (\lambda (d2: C).(\lambda (u2: T).(drop (S n) O (CHead x0 
(Flat f) x1) (CHead d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: 
T).(csuba g d2 d1))))) (\lambda (H9: (ex2 C (\lambda (d2: C).(drop (S n) O x0 
(CHead d2 (Bind Abst) u))) (\lambda (d2: C).(csuba g d2 d1)))).(ex2_ind C 
(\lambda (d2: C).(drop (S n) O x0 (CHead d2 (Bind Abst) u))) (\lambda (d2: 
C).(csuba g d2 d1)) (or (ex2 C (\lambda (d2: C).(drop (S n) O (CHead x0 (Flat 
f) x1) (CHead d2 (Bind Abst) u))) (\lambda (d2: C).(csuba g d2 d1))) (ex2_2 C 
T (\lambda (d2: C).(\lambda (u2: T).(drop (S n) O (CHead x0 (Flat f) x1) 
(CHead d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 
d1))))) (\lambda (x: C).(\lambda (H10: (drop (S n) O x0 (CHead x (Bind Abst) 
u))).(\lambda (H11: (csuba g x d1)).(or_introl (ex2 C (\lambda (d2: C).(drop 
(S n) O (CHead x0 (Flat f) x1) (CHead d2 (Bind Abst) u))) (\lambda (d2: 
C).(csuba g d2 d1))) (ex2_2 C T (\lambda (d2: C).(\lambda (u2: T).(drop (S n) 
O (CHead x0 (Flat f) x1) (CHead d2 (Bind Void) u2)))) (\lambda (d2: 
C).(\lambda (_: T).(csuba g d2 d1)))) (ex_intro2 C (\lambda (d2: C).(drop (S 
n) O (CHead x0 (Flat f) x1) (CHead d2 (Bind Abst) u))) (\lambda (d2: 
C).(csuba g d2 d1)) x (drop_drop (Flat f) n x0 (CHead x (Bind Abst) u) H10 
x1) H11))))) H9)) (\lambda (H9: (ex2_2 C T (\lambda (d2: C).(\lambda (u2: 
T).(drop (S n) O x0 (CHead d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda 
(_: T).(csuba g d2 d1))))).(ex2_2_ind C T (\lambda (d2: C).(\lambda (u2: 
T).(drop (S n) O x0 (CHead d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda 
(_: T).(csuba g d2 d1))) (or (ex2 C (\lambda (d2: C).(drop (S n) O (CHead x0 
(Flat f) x1) (CHead d2 (Bind Abst) u))) (\lambda (d2: C).(csuba g d2 d1))) 
(ex2_2 C T (\lambda (d2: C).(\lambda (u2: T).(drop (S n) O (CHead x0 (Flat f) 
x1) (CHead d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 
d1))))) (\lambda (x2: C).(\lambda (x3: T).(\lambda (H10: (drop (S n) O x0 
(CHead x2 (Bind Void) x3))).(\lambda (H11: (csuba g x2 d1)).(or_intror (ex2 C 
(\lambda (d2: C).(drop (S n) O (CHead x0 (Flat f) x1) (CHead d2 (Bind Abst) 
u))) (\lambda (d2: C).(csuba g d2 d1))) (ex2_2 C T (\lambda (d2: C).(\lambda 
(u2: T).(drop (S n) O (CHead x0 (Flat f) x1) (CHead d2 (Bind Void) u2)))) 
(\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1)))) (ex2_2_intro C T (\lambda 
(d2: C).(\lambda (u2: T).(drop (S n) O (CHead x0 (Flat f) x1) (CHead d2 (Bind 
Void) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1))) x2 x3 
(drop_drop (Flat f) n x0 (CHead x2 (Bind Void) x3) H10 x1) H11)))))) H9)) 
H8)) c2 H6))))) H5)))))) k H2 (drop_gen_drop k c (CHead d1 (Bind Abst) u) t n 
H1)))))))))))) c1)))) i).
(* COMMENTS
Initial nodes: 11438
END *)

theorem csuba_drop_abbr_rev:
 \forall (i: nat).(\forall (c1: C).(\forall (d1: C).(\forall (u1: T).((drop i 
O c1 (CHead d1 (Bind Abbr) u1)) \to (\forall (g: G).(\forall (c2: C).((csuba 
g c2 c1) \to (or3 (ex2 C (\lambda (d2: C).(drop i O c2 (CHead d2 (Bind Abbr) 
u1))) (\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C T A (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (_: A).(drop i O c2 (CHead d2 (Bind Abst) 
u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 d1)))) 
(\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 (asucc g 
a))))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 a))))) 
(ex2_2 C T (\lambda (d2: C).(\lambda (u2: T).(drop i O c2 (CHead d2 (Bind 
Void) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1))))))))))))
\def
 \lambda (i: nat).(nat_ind (\lambda (n: nat).(\forall (c1: C).(\forall (d1: 
C).(\forall (u1: T).((drop n O c1 (CHead d1 (Bind Abbr) u1)) \to (\forall (g: 
G).(\forall (c2: C).((csuba g c2 c1) \to (or3 (ex2 C (\lambda (d2: C).(drop n 
O c2 (CHead d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C 
T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(drop n O c2 (CHead d2 
(Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g 
d2 d1)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 
(asucc g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 
u1 a))))) (ex2_2 C T (\lambda (d2: C).(\lambda (u2: T).(drop n O c2 (CHead d2 
(Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 
d1))))))))))))) (\lambda (c1: C).(\lambda (d1: C).(\lambda (u1: T).(\lambda 
(H: (drop O O c1 (CHead d1 (Bind Abbr) u1))).(\lambda (g: G).(\lambda (c2: 
C).(\lambda (H0: (csuba g c2 c1)).(let H1 \def (eq_ind C c1 (\lambda (c: 
C).(csuba g c2 c)) H0 (CHead d1 (Bind Abbr) u1) (drop_gen_refl c1 (CHead d1 
(Bind Abbr) u1) H)) in (let H_x \def (csuba_gen_abbr_rev g d1 c2 u1 H1) in 
(let H2 \def H_x in (or3_ind (ex2 C (\lambda (d2: C).(eq C c2 (CHead d2 (Bind 
Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C T A (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (_: A).(eq C c2 (CHead d2 (Bind Abst) u2))))) 
(\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda 
(d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) 
(\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 a))))) (ex2_2 
C T (\lambda (d2: C).(\lambda (u2: T).(eq C c2 (CHead d2 (Bind Void) u2)))) 
(\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1)))) (or3 (ex2 C (\lambda (d2: 
C).(drop O O c2 (CHead d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 
d1))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(drop O 
O c2 (CHead d2 (Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda 
(_: A).(csuba g d2 d1)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: 
A).(arity g d2 u2 (asucc g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda 
(a: A).(arity g d1 u1 a))))) (ex2_2 C T (\lambda (d2: C).(\lambda (u2: 
T).(drop O O c2 (CHead d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: 
T).(csuba g d2 d1))))) (\lambda (H3: (ex2 C (\lambda (d2: C).(eq C c2 (CHead 
d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1)))).(ex2_ind C (\lambda 
(d2: C).(eq C c2 (CHead d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 
d1)) (or3 (ex2 C (\lambda (d2: C).(drop O O c2 (CHead d2 (Bind Abbr) u1))) 
(\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C T A (\lambda (d2: C).(\lambda 
(u2: T).(\lambda (_: A).(drop O O c2 (CHead d2 (Bind Abst) u2))))) (\lambda 
(d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) (\lambda 
(_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 a))))) (ex2_2 C T 
(\lambda (d2: C).(\lambda (u2: T).(drop O O c2 (CHead d2 (Bind Void) u2)))) 
(\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1))))) (\lambda (x: C).(\lambda 
(H4: (eq C c2 (CHead x (Bind Abbr) u1))).(\lambda (H5: (csuba g x 
d1)).(eq_ind_r C (CHead x (Bind Abbr) u1) (\lambda (c: C).(or3 (ex2 C 
(\lambda (d2: C).(drop O O c (CHead d2 (Bind Abbr) u1))) (\lambda (d2: 
C).(csuba g d2 d1))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda 
(_: A).(drop O O c (CHead d2 (Bind Abst) u2))))) (\lambda (d2: C).(\lambda 
(_: T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda (d2: C).(\lambda (u2: 
T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) (\lambda (_: C).(\lambda 
(_: T).(\lambda (a: A).(arity g d1 u1 a))))) (ex2_2 C T (\lambda (d2: 
C).(\lambda (u2: T).(drop O O c (CHead d2 (Bind Void) u2)))) (\lambda (d2: 
C).(\lambda (_: T).(csuba g d2 d1)))))) (or3_intro0 (ex2 C (\lambda (d2: 
C).(drop O O (CHead x (Bind Abbr) u1) (CHead d2 (Bind Abbr) u1))) (\lambda 
(d2: C).(csuba g d2 d1))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: 
T).(\lambda (_: A).(drop O O (CHead x (Bind Abbr) u1) (CHead d2 (Bind Abst) 
u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 d1)))) 
(\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 (asucc g 
a))))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 a))))) 
(ex2_2 C T (\lambda (d2: C).(\lambda (u2: T).(drop O O (CHead x (Bind Abbr) 
u1) (CHead d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 
d1)))) (ex_intro2 C (\lambda (d2: C).(drop O O (CHead x (Bind Abbr) u1) 
(CHead d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1)) x (drop_refl 
(CHead x (Bind Abbr) u1)) H5)) c2 H4)))) H3)) (\lambda (H3: (ex4_3 C T A 
(\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(eq C c2 (CHead d2 (Bind 
Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 
d1)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 
(asucc g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 
u1 a)))))).(ex4_3_ind C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: 
A).(eq C c2 (CHead d2 (Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: 
T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda (d2: C).(\lambda (u2: 
T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) (\lambda (_: C).(\lambda 
(_: T).(\lambda (a: A).(arity g d1 u1 a)))) (or3 (ex2 C (\lambda (d2: 
C).(drop O O c2 (CHead d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 
d1))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(drop O 
O c2 (CHead d2 (Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda 
(_: A).(csuba g d2 d1)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: 
A).(arity g d2 u2 (asucc g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda 
(a: A).(arity g d1 u1 a))))) (ex2_2 C T (\lambda (d2: C).(\lambda (u2: 
T).(drop O O c2 (CHead d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: 
T).(csuba g d2 d1))))) (\lambda (x0: C).(\lambda (x1: T).(\lambda (x2: 
A).(\lambda (H4: (eq C c2 (CHead x0 (Bind Abst) x1))).(\lambda (H5: (csuba g 
x0 d1)).(\lambda (H6: (arity g x0 x1 (asucc g x2))).(\lambda (H7: (arity g d1 
u1 x2)).(eq_ind_r C (CHead x0 (Bind Abst) x1) (\lambda (c: C).(or3 (ex2 C 
(\lambda (d2: C).(drop O O c (CHead d2 (Bind Abbr) u1))) (\lambda (d2: 
C).(csuba g d2 d1))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda 
(_: A).(drop O O c (CHead d2 (Bind Abst) u2))))) (\lambda (d2: C).(\lambda 
(_: T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda (d2: C).(\lambda (u2: 
T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) (\lambda (_: C).(\lambda 
(_: T).(\lambda (a: A).(arity g d1 u1 a))))) (ex2_2 C T (\lambda (d2: 
C).(\lambda (u2: T).(drop O O c (CHead d2 (Bind Void) u2)))) (\lambda (d2: 
C).(\lambda (_: T).(csuba g d2 d1)))))) (or3_intro1 (ex2 C (\lambda (d2: 
C).(drop O O (CHead x0 (Bind Abst) x1) (CHead d2 (Bind Abbr) u1))) (\lambda 
(d2: C).(csuba g d2 d1))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: 
T).(\lambda (_: A).(drop O O (CHead x0 (Bind Abst) x1) (CHead d2 (Bind Abst) 
u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 d1)))) 
(\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 (asucc g 
a))))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 a))))) 
(ex2_2 C T (\lambda (d2: C).(\lambda (u2: T).(drop O O (CHead x0 (Bind Abst) 
x1) (CHead d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 
d1)))) (ex4_3_intro C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: 
A).(drop O O (CHead x0 (Bind Abst) x1) (CHead d2 (Bind Abst) u2))))) (\lambda 
(d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) (\lambda 
(_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 a)))) x0 x1 x2 
(drop_refl (CHead x0 (Bind Abst) x1)) H5 H6 H7)) c2 H4)))))))) H3)) (\lambda 
(H3: (ex2_2 C T (\lambda (d2: C).(\lambda (u2: T).(eq C c2 (CHead d2 (Bind 
Void) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1))))).(ex2_2_ind 
C T (\lambda (d2: C).(\lambda (u2: T).(eq C c2 (CHead d2 (Bind Void) u2)))) 
(\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1))) (or3 (ex2 C (\lambda (d2: 
C).(drop O O c2 (CHead d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 
d1))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(drop O 
O c2 (CHead d2 (Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda 
(_: A).(csuba g d2 d1)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: 
A).(arity g d2 u2 (asucc g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda 
(a: A).(arity g d1 u1 a))))) (ex2_2 C T (\lambda (d2: C).(\lambda (u2: 
T).(drop O O c2 (CHead d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: 
T).(csuba g d2 d1))))) (\lambda (x0: C).(\lambda (x1: T).(\lambda (H4: (eq C 
c2 (CHead x0 (Bind Void) x1))).(\lambda (H5: (csuba g x0 d1)).(eq_ind_r C 
(CHead x0 (Bind Void) x1) (\lambda (c: C).(or3 (ex2 C (\lambda (d2: C).(drop 
O O c (CHead d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C 
T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(drop O O c (CHead d2 
(Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g 
d2 d1)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 
(asucc g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 
u1 a))))) (ex2_2 C T (\lambda (d2: C).(\lambda (u2: T).(drop O O c (CHead d2 
(Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1)))))) 
(or3_intro2 (ex2 C (\lambda (d2: C).(drop O O (CHead x0 (Bind Void) x1) 
(CHead d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C T A 
(\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(drop O O (CHead x0 (Bind 
Void) x1) (CHead d2 (Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: 
T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda (d2: C).(\lambda (u2: 
T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) (\lambda (_: C).(\lambda 
(_: T).(\lambda (a: A).(arity g d1 u1 a))))) (ex2_2 C T (\lambda (d2: 
C).(\lambda (u2: T).(drop O O (CHead x0 (Bind Void) x1) (CHead d2 (Bind Void) 
u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1)))) (ex2_2_intro C T 
(\lambda (d2: C).(\lambda (u2: T).(drop O O (CHead x0 (Bind Void) x1) (CHead 
d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1))) x0 
x1 (drop_refl (CHead x0 (Bind Void) x1)) H5)) c2 H4))))) H3)) H2))))))))))) 
(\lambda (n: nat).(\lambda (H: ((\forall (c1: C).(\forall (d1: C).(\forall 
(u1: T).((drop n O c1 (CHead d1 (Bind Abbr) u1)) \to (\forall (g: G).(\forall 
(c2: C).((csuba g c2 c1) \to (or3 (ex2 C (\lambda (d2: C).(drop n O c2 (CHead 
d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C T A (\lambda 
(d2: C).(\lambda (u2: T).(\lambda (_: A).(drop n O c2 (CHead d2 (Bind Abst) 
u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 d1)))) 
(\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 (asucc g 
a))))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 a))))) 
(ex2_2 C T (\lambda (d2: C).(\lambda (u2: T).(drop n O c2 (CHead d2 (Bind 
Void) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 
d1)))))))))))))).(\lambda (c1: C).(C_ind (\lambda (c: C).(\forall (d1: 
C).(\forall (u1: T).((drop (S n) O c (CHead d1 (Bind Abbr) u1)) \to (\forall 
(g: G).(\forall (c2: C).((csuba g c2 c) \to (or3 (ex2 C (\lambda (d2: 
C).(drop (S n) O c2 (CHead d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 
d1))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(drop (S 
n) O c2 (CHead d2 (Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: 
T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda (d2: C).(\lambda (u2: 
T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) (\lambda (_: C).(\lambda 
(_: T).(\lambda (a: A).(arity g d1 u1 a))))) (ex2_2 C T (\lambda (d2: 
C).(\lambda (u2: T).(drop (S n) O c2 (CHead d2 (Bind Void) u2)))) (\lambda 
(d2: C).(\lambda (_: T).(csuba g d2 d1)))))))))))) (\lambda (n0: 
nat).(\lambda (d1: C).(\lambda (u1: T).(\lambda (H0: (drop (S n) O (CSort n0) 
(CHead d1 (Bind Abbr) u1))).(\lambda (g: G).(\lambda (c2: C).(\lambda (_: 
(csuba g c2 (CSort n0))).(and3_ind (eq C (CHead d1 (Bind Abbr) u1) (CSort 
n0)) (eq nat (S n) O) (eq nat O O) (or3 (ex2 C (\lambda (d2: C).(drop (S n) O 
c2 (CHead d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C T 
A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(drop (S n) O c2 (CHead 
d2 (Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: 
A).(csuba g d2 d1)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: 
A).(arity g d2 u2 (asucc g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda 
(a: A).(arity g d1 u1 a))))) (ex2_2 C T (\lambda (d2: C).(\lambda (u2: 
T).(drop (S n) O c2 (CHead d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda 
(_: T).(csuba g d2 d1))))) (\lambda (_: (eq C (CHead d1 (Bind Abbr) u1) 
(CSort n0))).(\lambda (H3: (eq nat (S n) O)).(\lambda (_: (eq nat O O)).(let 
H5 \def (eq_ind nat (S n) (\lambda (ee: nat).(match ee in nat return (\lambda 
(_: nat).Prop) with [O \Rightarrow False | (S _) \Rightarrow True])) I O H3) 
in (False_ind (or3 (ex2 C (\lambda (d2: C).(drop (S n) O c2 (CHead d2 (Bind 
Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C T A (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (_: A).(drop (S n) O c2 (CHead d2 (Bind Abst) 
u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 d1)))) 
(\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 (asucc g 
a))))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 a))))) 
(ex2_2 C T (\lambda (d2: C).(\lambda (u2: T).(drop (S n) O c2 (CHead d2 (Bind 
Void) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1))))) H5))))) 
(drop_gen_sort n0 (S n) O (CHead d1 (Bind Abbr) u1) H0))))))))) (\lambda (c: 
C).(\lambda (H0: ((\forall (d1: C).(\forall (u1: T).((drop (S n) O c (CHead 
d1 (Bind Abbr) u1)) \to (\forall (g: G).(\forall (c2: C).((csuba g c2 c) \to 
(or3 (ex2 C (\lambda (d2: C).(drop (S n) O c2 (CHead d2 (Bind Abbr) u1))) 
(\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C T A (\lambda (d2: C).(\lambda 
(u2: T).(\lambda (_: A).(drop (S n) O c2 (CHead d2 (Bind Abst) u2))))) 
(\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda 
(d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) 
(\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 a))))) (ex2_2 
C T (\lambda (d2: C).(\lambda (u2: T).(drop (S n) O c2 (CHead d2 (Bind Void) 
u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1))))))))))))).(\lambda 
(k: K).(\lambda (t: T).(\lambda (d1: C).(\lambda (u1: T).(\lambda (H1: (drop 
(S n) O (CHead c k t) (CHead d1 (Bind Abbr) u1))).(\lambda (g: G).(\lambda 
(c2: C).(\lambda (H2: (csuba g c2 (CHead c k t))).(K_ind (\lambda (k0: 
K).((csuba g c2 (CHead c k0 t)) \to ((drop (r k0 n) O c (CHead d1 (Bind Abbr) 
u1)) \to (or3 (ex2 C (\lambda (d2: C).(drop (S n) O c2 (CHead d2 (Bind Abbr) 
u1))) (\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C T A (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (_: A).(drop (S n) O c2 (CHead d2 (Bind Abst) 
u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 d1)))) 
(\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 (asucc g 
a))))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 a))))) 
(ex2_2 C T (\lambda (d2: C).(\lambda (u2: T).(drop (S n) O c2 (CHead d2 (Bind 
Void) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1)))))))) (\lambda 
(b: B).(\lambda (H3: (csuba g c2 (CHead c (Bind b) t))).(\lambda (H4: (drop 
(r (Bind b) n) O c (CHead d1 (Bind Abbr) u1))).(B_ind (\lambda (b0: 
B).((csuba g c2 (CHead c (Bind b0) t)) \to ((drop (r (Bind b0) n) O c (CHead 
d1 (Bind Abbr) u1)) \to (or3 (ex2 C (\lambda (d2: C).(drop (S n) O c2 (CHead 
d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C T A (\lambda 
(d2: C).(\lambda (u2: T).(\lambda (_: A).(drop (S n) O c2 (CHead d2 (Bind 
Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 
d1)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 
(asucc g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 
u1 a))))) (ex2_2 C T (\lambda (d2: C).(\lambda (u2: T).(drop (S n) O c2 
(CHead d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 
d1)))))))) (\lambda (H5: (csuba g c2 (CHead c (Bind Abbr) t))).(\lambda (H6: 
(drop (r (Bind Abbr) n) O c (CHead d1 (Bind Abbr) u1))).(let H_x \def 
(csuba_gen_abbr_rev g c c2 t H5) in (let H7 \def H_x in (or3_ind (ex2 C 
(\lambda (d2: C).(eq C c2 (CHead d2 (Bind Abbr) t))) (\lambda (d2: C).(csuba 
g d2 c))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(eq 
C c2 (CHead d2 (Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda 
(_: A).(csuba g d2 c)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: 
A).(arity g d2 u2 (asucc g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda 
(a: A).(arity g c t a))))) (ex2_2 C T (\lambda (d2: C).(\lambda (u2: T).(eq C 
c2 (CHead d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 
c)))) (or3 (ex2 C (\lambda (d2: C).(drop (S n) O c2 (CHead d2 (Bind Abbr) 
u1))) (\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C T A (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (_: A).(drop (S n) O c2 (CHead d2 (Bind Abst) 
u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 d1)))) 
(\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 (asucc g 
a))))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 a))))) 
(ex2_2 C T (\lambda (d2: C).(\lambda (u2: T).(drop (S n) O c2 (CHead d2 (Bind 
Void) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1))))) (\lambda 
(H8: (ex2 C (\lambda (d2: C).(eq C c2 (CHead d2 (Bind Abbr) t))) (\lambda 
(d2: C).(csuba g d2 c)))).(ex2_ind C (\lambda (d2: C).(eq C c2 (CHead d2 
(Bind Abbr) t))) (\lambda (d2: C).(csuba g d2 c)) (or3 (ex2 C (\lambda (d2: 
C).(drop (S n) O c2 (CHead d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 
d1))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(drop (S 
n) O c2 (CHead d2 (Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: 
T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda (d2: C).(\lambda (u2: 
T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) (\lambda (_: C).(\lambda 
(_: T).(\lambda (a: A).(arity g d1 u1 a))))) (ex2_2 C T (\lambda (d2: 
C).(\lambda (u2: T).(drop (S n) O c2 (CHead d2 (Bind Void) u2)))) (\lambda 
(d2: C).(\lambda (_: T).(csuba g d2 d1))))) (\lambda (x: C).(\lambda (H9: (eq 
C c2 (CHead x (Bind Abbr) t))).(\lambda (H10: (csuba g x c)).(eq_ind_r C 
(CHead x (Bind Abbr) t) (\lambda (c0: C).(or3 (ex2 C (\lambda (d2: C).(drop 
(S n) O c0 (CHead d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1))) 
(ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(drop (S n) O 
c0 (CHead d2 (Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda 
(_: A).(csuba g d2 d1)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: 
A).(arity g d2 u2 (asucc g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda 
(a: A).(arity g d1 u1 a))))) (ex2_2 C T (\lambda (d2: C).(\lambda (u2: 
T).(drop (S n) O c0 (CHead d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda 
(_: T).(csuba g d2 d1)))))) (let H11 \def (H c d1 u1 H6 g x H10) in (or3_ind 
(ex2 C (\lambda (d2: C).(drop n O x (CHead d2 (Bind Abbr) u1))) (\lambda (d2: 
C).(csuba g d2 d1))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda 
(_: A).(drop n O x (CHead d2 (Bind Abst) u2))))) (\lambda (d2: C).(\lambda 
(_: T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda (d2: C).(\lambda (u2: 
T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) (\lambda (_: C).(\lambda 
(_: T).(\lambda (a: A).(arity g d1 u1 a))))) (ex2_2 C T (\lambda (d2: 
C).(\lambda (u2: T).(drop n O x (CHead d2 (Bind Void) u2)))) (\lambda (d2: 
C).(\lambda (_: T).(csuba g d2 d1)))) (or3 (ex2 C (\lambda (d2: C).(drop (S 
n) O (CHead x (Bind Abbr) t) (CHead d2 (Bind Abbr) u1))) (\lambda (d2: 
C).(csuba g d2 d1))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda 
(_: A).(drop (S n) O (CHead x (Bind Abbr) t) (CHead d2 (Bind Abst) u2))))) 
(\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda 
(d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) 
(\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 a))))) (ex2_2 
C T (\lambda (d2: C).(\lambda (u2: T).(drop (S n) O (CHead x (Bind Abbr) t) 
(CHead d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 
d1))))) (\lambda (H12: (ex2 C (\lambda (d2: C).(drop n O x (CHead d2 (Bind 
Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1)))).(ex2_ind C (\lambda (d2: 
C).(drop n O x (CHead d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1)) 
(or3 (ex2 C (\lambda (d2: C).(drop (S n) O (CHead x (Bind Abbr) t) (CHead d2 
(Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C T A (\lambda 
(d2: C).(\lambda (u2: T).(\lambda (_: A).(drop (S n) O (CHead x (Bind Abbr) 
t) (CHead d2 (Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda 
(_: A).(csuba g d2 d1)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: 
A).(arity g d2 u2 (asucc g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda 
(a: A).(arity g d1 u1 a))))) (ex2_2 C T (\lambda (d2: C).(\lambda (u2: 
T).(drop (S n) O (CHead x (Bind Abbr) t) (CHead d2 (Bind Void) u2)))) 
(\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1))))) (\lambda (x0: 
C).(\lambda (H13: (drop n O x (CHead x0 (Bind Abbr) u1))).(\lambda (H14: 
(csuba g x0 d1)).(or3_intro0 (ex2 C (\lambda (d2: C).(drop (S n) O (CHead x 
(Bind Abbr) t) (CHead d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1))) 
(ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(drop (S n) O 
(CHead x (Bind Abbr) t) (CHead d2 (Bind Abst) u2))))) (\lambda (d2: 
C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) (\lambda 
(_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 a))))) (ex2_2 C T 
(\lambda (d2: C).(\lambda (u2: T).(drop (S n) O (CHead x (Bind Abbr) t) 
(CHead d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 
d1)))) (ex_intro2 C (\lambda (d2: C).(drop (S n) O (CHead x (Bind Abbr) t) 
(CHead d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1)) x0 (drop_drop 
(Bind Abbr) n x (CHead x0 (Bind Abbr) u1) H13 t) H14))))) H12)) (\lambda 
(H12: (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(drop n 
O x (CHead d2 (Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda 
(_: A).(csuba g d2 d1)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: 
A).(arity g d2 u2 (asucc g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda 
(a: A).(arity g d1 u1 a)))))).(ex4_3_ind C T A (\lambda (d2: C).(\lambda (u2: 
T).(\lambda (_: A).(drop n O x (CHead d2 (Bind Abst) u2))))) (\lambda (d2: 
C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) (\lambda 
(_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 a)))) (or3 (ex2 C 
(\lambda (d2: C).(drop (S n) O (CHead x (Bind Abbr) t) (CHead d2 (Bind Abbr) 
u1))) (\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C T A (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (_: A).(drop (S n) O (CHead x (Bind Abbr) t) 
(CHead d2 (Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: 
A).(csuba g d2 d1)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: 
A).(arity g d2 u2 (asucc g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda 
(a: A).(arity g d1 u1 a))))) (ex2_2 C T (\lambda (d2: C).(\lambda (u2: 
T).(drop (S n) O (CHead x (Bind Abbr) t) (CHead d2 (Bind Void) u2)))) 
(\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1))))) (\lambda (x0: 
C).(\lambda (x1: T).(\lambda (x2: A).(\lambda (H13: (drop n O x (CHead x0 
(Bind Abst) x1))).(\lambda (H14: (csuba g x0 d1)).(\lambda (H15: (arity g x0 
x1 (asucc g x2))).(\lambda (H16: (arity g d1 u1 x2)).(or3_intro1 (ex2 C 
(\lambda (d2: C).(drop (S n) O (CHead x (Bind Abbr) t) (CHead d2 (Bind Abbr) 
u1))) (\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C T A (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (_: A).(drop (S n) O (CHead x (Bind Abbr) t) 
(CHead d2 (Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: 
A).(csuba g d2 d1)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: 
A).(arity g d2 u2 (asucc g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda 
(a: A).(arity g d1 u1 a))))) (ex2_2 C T (\lambda (d2: C).(\lambda (u2: 
T).(drop (S n) O (CHead x (Bind Abbr) t) (CHead d2 (Bind Void) u2)))) 
(\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1)))) (ex4_3_intro C T A 
(\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(drop (S n) O (CHead x 
(Bind Abbr) t) (CHead d2 (Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: 
T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda (d2: C).(\lambda (u2: 
T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) (\lambda (_: C).(\lambda 
(_: T).(\lambda (a: A).(arity g d1 u1 a)))) x0 x1 x2 (drop_drop (Bind Abbr) n 
x (CHead x0 (Bind Abst) x1) H13 t) H14 H15 H16))))))))) H12)) (\lambda (H12: 
(ex2_2 C T (\lambda (d2: C).(\lambda (u2: T).(drop n O x (CHead d2 (Bind 
Void) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1))))).(ex2_2_ind 
C T (\lambda (d2: C).(\lambda (u2: T).(drop n O x (CHead d2 (Bind Void) 
u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1))) (or3 (ex2 C 
(\lambda (d2: C).(drop (S n) O (CHead x (Bind Abbr) t) (CHead d2 (Bind Abbr) 
u1))) (\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C T A (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (_: A).(drop (S n) O (CHead x (Bind Abbr) t) 
(CHead d2 (Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: 
A).(csuba g d2 d1)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: 
A).(arity g d2 u2 (asucc g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda 
(a: A).(arity g d1 u1 a))))) (ex2_2 C T (\lambda (d2: C).(\lambda (u2: 
T).(drop (S n) O (CHead x (Bind Abbr) t) (CHead d2 (Bind Void) u2)))) 
(\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1))))) (\lambda (x0: 
C).(\lambda (x1: T).(\lambda (H13: (drop n O x (CHead x0 (Bind Void) 
x1))).(\lambda (H14: (csuba g x0 d1)).(or3_intro2 (ex2 C (\lambda (d2: 
C).(drop (S n) O (CHead x (Bind Abbr) t) (CHead d2 (Bind Abbr) u1))) (\lambda 
(d2: C).(csuba g d2 d1))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: 
T).(\lambda (_: A).(drop (S n) O (CHead x (Bind Abbr) t) (CHead d2 (Bind 
Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 
d1)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 
(asucc g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 
u1 a))))) (ex2_2 C T (\lambda (d2: C).(\lambda (u2: T).(drop (S n) O (CHead x 
(Bind Abbr) t) (CHead d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: 
T).(csuba g d2 d1)))) (ex2_2_intro C T (\lambda (d2: C).(\lambda (u2: 
T).(drop (S n) O (CHead x (Bind Abbr) t) (CHead d2 (Bind Void) u2)))) 
(\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1))) x0 x1 (drop_drop (Bind 
Abbr) n x (CHead x0 (Bind Void) x1) H13 t) H14)))))) H12)) H11)) c2 H9)))) 
H8)) (\lambda (H8: (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda 
(_: A).(eq C c2 (CHead d2 (Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: 
T).(\lambda (_: A).(csuba g d2 c)))) (\lambda (d2: C).(\lambda (u2: 
T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) (\lambda (_: C).(\lambda 
(_: T).(\lambda (a: A).(arity g c t a)))))).(ex4_3_ind C T A (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (_: A).(eq C c2 (CHead d2 (Bind Abst) u2))))) 
(\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 c)))) (\lambda 
(d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) 
(\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g c t a)))) (or3 (ex2 
C (\lambda (d2: C).(drop (S n) O c2 (CHead d2 (Bind Abbr) u1))) (\lambda (d2: 
C).(csuba g d2 d1))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda 
(_: A).(drop (S n) O c2 (CHead d2 (Bind Abst) u2))))) (\lambda (d2: 
C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) (\lambda 
(_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 a))))) (ex2_2 C T 
(\lambda (d2: C).(\lambda (u2: T).(drop (S n) O c2 (CHead d2 (Bind Void) 
u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1))))) (\lambda (x0: 
C).(\lambda (x1: T).(\lambda (x2: A).(\lambda (H9: (eq C c2 (CHead x0 (Bind 
Abst) x1))).(\lambda (H10: (csuba g x0 c)).(\lambda (_: (arity g x0 x1 (asucc 
g x2))).(\lambda (_: (arity g c t x2)).(eq_ind_r C (CHead x0 (Bind Abst) x1) 
(\lambda (c0: C).(or3 (ex2 C (\lambda (d2: C).(drop (S n) O c0 (CHead d2 
(Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C T A (\lambda 
(d2: C).(\lambda (u2: T).(\lambda (_: A).(drop (S n) O c0 (CHead d2 (Bind 
Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 
d1)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 
(asucc g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 
u1 a))))) (ex2_2 C T (\lambda (d2: C).(\lambda (u2: T).(drop (S n) O c0 
(CHead d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 
d1)))))) (let H13 \def (H c d1 u1 H6 g x0 H10) in (or3_ind (ex2 C (\lambda 
(d2: C).(drop n O x0 (CHead d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 
d1))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(drop n 
O x0 (CHead d2 (Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda 
(_: A).(csuba g d2 d1)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: 
A).(arity g d2 u2 (asucc g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda 
(a: A).(arity g d1 u1 a))))) (ex2_2 C T (\lambda (d2: C).(\lambda (u2: 
T).(drop n O x0 (CHead d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: 
T).(csuba g d2 d1)))) (or3 (ex2 C (\lambda (d2: C).(drop (S n) O (CHead x0 
(Bind Abst) x1) (CHead d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 
d1))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(drop (S 
n) O (CHead x0 (Bind Abst) x1) (CHead d2 (Bind Abst) u2))))) (\lambda (d2: 
C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) (\lambda 
(_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 a))))) (ex2_2 C T 
(\lambda (d2: C).(\lambda (u2: T).(drop (S n) O (CHead x0 (Bind Abst) x1) 
(CHead d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 
d1))))) (\lambda (H14: (ex2 C (\lambda (d2: C).(drop n O x0 (CHead d2 (Bind 
Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1)))).(ex2_ind C (\lambda (d2: 
C).(drop n O x0 (CHead d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1)) 
(or3 (ex2 C (\lambda (d2: C).(drop (S n) O (CHead x0 (Bind Abst) x1) (CHead 
d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C T A (\lambda 
(d2: C).(\lambda (u2: T).(\lambda (_: A).(drop (S n) O (CHead x0 (Bind Abst) 
x1) (CHead d2 (Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda 
(_: A).(csuba g d2 d1)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: 
A).(arity g d2 u2 (asucc g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda 
(a: A).(arity g d1 u1 a))))) (ex2_2 C T (\lambda (d2: C).(\lambda (u2: 
T).(drop (S n) O (CHead x0 (Bind Abst) x1) (CHead d2 (Bind Void) u2)))) 
(\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1))))) (\lambda (x: C).(\lambda 
(H15: (drop n O x0 (CHead x (Bind Abbr) u1))).(\lambda (H16: (csuba g x 
d1)).(or3_intro0 (ex2 C (\lambda (d2: C).(drop (S n) O (CHead x0 (Bind Abst) 
x1) (CHead d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C T 
A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(drop (S n) O (CHead x0 
(Bind Abst) x1) (CHead d2 (Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: 
T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda (d2: C).(\lambda (u2: 
T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) (\lambda (_: C).(\lambda 
(_: T).(\lambda (a: A).(arity g d1 u1 a))))) (ex2_2 C T (\lambda (d2: 
C).(\lambda (u2: T).(drop (S n) O (CHead x0 (Bind Abst) x1) (CHead d2 (Bind 
Void) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1)))) (ex_intro2 C 
(\lambda (d2: C).(drop (S n) O (CHead x0 (Bind Abst) x1) (CHead d2 (Bind 
Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1)) x (drop_drop (Bind Abst) n x0 
(CHead x (Bind Abbr) u1) H15 x1) H16))))) H14)) (\lambda (H14: (ex4_3 C T A 
(\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(drop n O x0 (CHead d2 
(Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g 
d2 d1)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 
(asucc g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 
u1 a)))))).(ex4_3_ind C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: 
A).(drop n O x0 (CHead d2 (Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: 
T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda (d2: C).(\lambda (u2: 
T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) (\lambda (_: C).(\lambda 
(_: T).(\lambda (a: A).(arity g d1 u1 a)))) (or3 (ex2 C (\lambda (d2: 
C).(drop (S n) O (CHead x0 (Bind Abst) x1) (CHead d2 (Bind Abbr) u1))) 
(\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C T A (\lambda (d2: C).(\lambda 
(u2: T).(\lambda (_: A).(drop (S n) O (CHead x0 (Bind Abst) x1) (CHead d2 
(Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g 
d2 d1)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 
(asucc g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 
u1 a))))) (ex2_2 C T (\lambda (d2: C).(\lambda (u2: T).(drop (S n) O (CHead 
x0 (Bind Abst) x1) (CHead d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: 
T).(csuba g d2 d1))))) (\lambda (x3: C).(\lambda (x4: T).(\lambda (x5: 
A).(\lambda (H15: (drop n O x0 (CHead x3 (Bind Abst) x4))).(\lambda (H16: 
(csuba g x3 d1)).(\lambda (H17: (arity g x3 x4 (asucc g x5))).(\lambda (H18: 
(arity g d1 u1 x5)).(or3_intro1 (ex2 C (\lambda (d2: C).(drop (S n) O (CHead 
x0 (Bind Abst) x1) (CHead d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 
d1))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(drop (S 
n) O (CHead x0 (Bind Abst) x1) (CHead d2 (Bind Abst) u2))))) (\lambda (d2: 
C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) (\lambda 
(_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 a))))) (ex2_2 C T 
(\lambda (d2: C).(\lambda (u2: T).(drop (S n) O (CHead x0 (Bind Abst) x1) 
(CHead d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 
d1)))) (ex4_3_intro C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: 
A).(drop (S n) O (CHead x0 (Bind Abst) x1) (CHead d2 (Bind Abst) u2))))) 
(\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda 
(d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) 
(\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 a)))) x3 x4 x5 
(drop_drop (Bind Abst) n x0 (CHead x3 (Bind Abst) x4) H15 x1) H16 H17 
H18))))))))) H14)) (\lambda (H14: (ex2_2 C T (\lambda (d2: C).(\lambda (u2: 
T).(drop n O x0 (CHead d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: 
T).(csuba g d2 d1))))).(ex2_2_ind C T (\lambda (d2: C).(\lambda (u2: T).(drop 
n O x0 (CHead d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g 
d2 d1))) (or3 (ex2 C (\lambda (d2: C).(drop (S n) O (CHead x0 (Bind Abst) x1) 
(CHead d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C T A 
(\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(drop (S n) O (CHead x0 
(Bind Abst) x1) (CHead d2 (Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: 
T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda (d2: C).(\lambda (u2: 
T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) (\lambda (_: C).(\lambda 
(_: T).(\lambda (a: A).(arity g d1 u1 a))))) (ex2_2 C T (\lambda (d2: 
C).(\lambda (u2: T).(drop (S n) O (CHead x0 (Bind Abst) x1) (CHead d2 (Bind 
Void) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1))))) (\lambda 
(x3: C).(\lambda (x4: T).(\lambda (H15: (drop n O x0 (CHead x3 (Bind Void) 
x4))).(\lambda (H16: (csuba g x3 d1)).(or3_intro2 (ex2 C (\lambda (d2: 
C).(drop (S n) O (CHead x0 (Bind Abst) x1) (CHead d2 (Bind Abbr) u1))) 
(\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C T A (\lambda (d2: C).(\lambda 
(u2: T).(\lambda (_: A).(drop (S n) O (CHead x0 (Bind Abst) x1) (CHead d2 
(Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g 
d2 d1)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 
(asucc g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 
u1 a))))) (ex2_2 C T (\lambda (d2: C).(\lambda (u2: T).(drop (S n) O (CHead 
x0 (Bind Abst) x1) (CHead d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: 
T).(csuba g d2 d1)))) (ex2_2_intro C T (\lambda (d2: C).(\lambda (u2: 
T).(drop (S n) O (CHead x0 (Bind Abst) x1) (CHead d2 (Bind Void) u2)))) 
(\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1))) x3 x4 (drop_drop (Bind 
Abst) n x0 (CHead x3 (Bind Void) x4) H15 x1) H16)))))) H14)) H13)) c2 
H9)))))))) H8)) (\lambda (H8: (ex2_2 C T (\lambda (d2: C).(\lambda (u2: 
T).(eq C c2 (CHead d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: 
T).(csuba g d2 c))))).(ex2_2_ind C T (\lambda (d2: C).(\lambda (u2: T).(eq C 
c2 (CHead d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 
c))) (or3 (ex2 C (\lambda (d2: C).(drop (S n) O c2 (CHead d2 (Bind Abbr) 
u1))) (\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C T A (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (_: A).(drop (S n) O c2 (CHead d2 (Bind Abst) 
u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 d1)))) 
(\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 (asucc g 
a))))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 a))))) 
(ex2_2 C T (\lambda (d2: C).(\lambda (u2: T).(drop (S n) O c2 (CHead d2 (Bind 
Void) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1))))) (\lambda 
(x0: C).(\lambda (x1: T).(\lambda (H9: (eq C c2 (CHead x0 (Bind Void) 
x1))).(\lambda (H10: (csuba g x0 c)).(eq_ind_r C (CHead x0 (Bind Void) x1) 
(\lambda (c0: C).(or3 (ex2 C (\lambda (d2: C).(drop (S n) O c0 (CHead d2 
(Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C T A (\lambda 
(d2: C).(\lambda (u2: T).(\lambda (_: A).(drop (S n) O c0 (CHead d2 (Bind 
Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 
d1)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 
(asucc g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 
u1 a))))) (ex2_2 C T (\lambda (d2: C).(\lambda (u2: T).(drop (S n) O c0 
(CHead d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 
d1)))))) (let H11 \def (H c d1 u1 H6 g x0 H10) in (or3_ind (ex2 C (\lambda 
(d2: C).(drop n O x0 (CHead d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 
d1))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(drop n 
O x0 (CHead d2 (Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda 
(_: A).(csuba g d2 d1)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: 
A).(arity g d2 u2 (asucc g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda 
(a: A).(arity g d1 u1 a))))) (ex2_2 C T (\lambda (d2: C).(\lambda (u2: 
T).(drop n O x0 (CHead d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: 
T).(csuba g d2 d1)))) (or3 (ex2 C (\lambda (d2: C).(drop (S n) O (CHead x0 
(Bind Void) x1) (CHead d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 
d1))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(drop (S 
n) O (CHead x0 (Bind Void) x1) (CHead d2 (Bind Abst) u2))))) (\lambda (d2: 
C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) (\lambda 
(_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 a))))) (ex2_2 C T 
(\lambda (d2: C).(\lambda (u2: T).(drop (S n) O (CHead x0 (Bind Void) x1) 
(CHead d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 
d1))))) (\lambda (H12: (ex2 C (\lambda (d2: C).(drop n O x0 (CHead d2 (Bind 
Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1)))).(ex2_ind C (\lambda (d2: 
C).(drop n O x0 (CHead d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1)) 
(or3 (ex2 C (\lambda (d2: C).(drop (S n) O (CHead x0 (Bind Void) x1) (CHead 
d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C T A (\lambda 
(d2: C).(\lambda (u2: T).(\lambda (_: A).(drop (S n) O (CHead x0 (Bind Void) 
x1) (CHead d2 (Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda 
(_: A).(csuba g d2 d1)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: 
A).(arity g d2 u2 (asucc g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda 
(a: A).(arity g d1 u1 a))))) (ex2_2 C T (\lambda (d2: C).(\lambda (u2: 
T).(drop (S n) O (CHead x0 (Bind Void) x1) (CHead d2 (Bind Void) u2)))) 
(\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1))))) (\lambda (x: C).(\lambda 
(H13: (drop n O x0 (CHead x (Bind Abbr) u1))).(\lambda (H14: (csuba g x 
d1)).(or3_intro0 (ex2 C (\lambda (d2: C).(drop (S n) O (CHead x0 (Bind Void) 
x1) (CHead d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C T 
A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(drop (S n) O (CHead x0 
(Bind Void) x1) (CHead d2 (Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: 
T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda (d2: C).(\lambda (u2: 
T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) (\lambda (_: C).(\lambda 
(_: T).(\lambda (a: A).(arity g d1 u1 a))))) (ex2_2 C T (\lambda (d2: 
C).(\lambda (u2: T).(drop (S n) O (CHead x0 (Bind Void) x1) (CHead d2 (Bind 
Void) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1)))) (ex_intro2 C 
(\lambda (d2: C).(drop (S n) O (CHead x0 (Bind Void) x1) (CHead d2 (Bind 
Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1)) x (drop_drop (Bind Void) n x0 
(CHead x (Bind Abbr) u1) H13 x1) H14))))) H12)) (\lambda (H12: (ex4_3 C T A 
(\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(drop n O x0 (CHead d2 
(Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g 
d2 d1)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 
(asucc g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 
u1 a)))))).(ex4_3_ind C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: 
A).(drop n O x0 (CHead d2 (Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: 
T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda (d2: C).(\lambda (u2: 
T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) (\lambda (_: C).(\lambda 
(_: T).(\lambda (a: A).(arity g d1 u1 a)))) (or3 (ex2 C (\lambda (d2: 
C).(drop (S n) O (CHead x0 (Bind Void) x1) (CHead d2 (Bind Abbr) u1))) 
(\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C T A (\lambda (d2: C).(\lambda 
(u2: T).(\lambda (_: A).(drop (S n) O (CHead x0 (Bind Void) x1) (CHead d2 
(Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g 
d2 d1)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 
(asucc g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 
u1 a))))) (ex2_2 C T (\lambda (d2: C).(\lambda (u2: T).(drop (S n) O (CHead 
x0 (Bind Void) x1) (CHead d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: 
T).(csuba g d2 d1))))) (\lambda (x2: C).(\lambda (x3: T).(\lambda (x4: 
A).(\lambda (H13: (drop n O x0 (CHead x2 (Bind Abst) x3))).(\lambda (H14: 
(csuba g x2 d1)).(\lambda (H15: (arity g x2 x3 (asucc g x4))).(\lambda (H16: 
(arity g d1 u1 x4)).(or3_intro1 (ex2 C (\lambda (d2: C).(drop (S n) O (CHead 
x0 (Bind Void) x1) (CHead d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 
d1))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(drop (S 
n) O (CHead x0 (Bind Void) x1) (CHead d2 (Bind Abst) u2))))) (\lambda (d2: 
C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) (\lambda 
(_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 a))))) (ex2_2 C T 
(\lambda (d2: C).(\lambda (u2: T).(drop (S n) O (CHead x0 (Bind Void) x1) 
(CHead d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 
d1)))) (ex4_3_intro C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: 
A).(drop (S n) O (CHead x0 (Bind Void) x1) (CHead d2 (Bind Abst) u2))))) 
(\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda 
(d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) 
(\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 a)))) x2 x3 x4 
(drop_drop (Bind Void) n x0 (CHead x2 (Bind Abst) x3) H13 x1) H14 H15 
H16))))))))) H12)) (\lambda (H12: (ex2_2 C T (\lambda (d2: C).(\lambda (u2: 
T).(drop n O x0 (CHead d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: 
T).(csuba g d2 d1))))).(ex2_2_ind C T (\lambda (d2: C).(\lambda (u2: T).(drop 
n O x0 (CHead d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g 
d2 d1))) (or3 (ex2 C (\lambda (d2: C).(drop (S n) O (CHead x0 (Bind Void) x1) 
(CHead d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C T A 
(\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(drop (S n) O (CHead x0 
(Bind Void) x1) (CHead d2 (Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: 
T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda (d2: C).(\lambda (u2: 
T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) (\lambda (_: C).(\lambda 
(_: T).(\lambda (a: A).(arity g d1 u1 a))))) (ex2_2 C T (\lambda (d2: 
C).(\lambda (u2: T).(drop (S n) O (CHead x0 (Bind Void) x1) (CHead d2 (Bind 
Void) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1))))) (\lambda 
(x2: C).(\lambda (x3: T).(\lambda (H13: (drop n O x0 (CHead x2 (Bind Void) 
x3))).(\lambda (H14: (csuba g x2 d1)).(or3_intro2 (ex2 C (\lambda (d2: 
C).(drop (S n) O (CHead x0 (Bind Void) x1) (CHead d2 (Bind Abbr) u1))) 
(\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C T A (\lambda (d2: C).(\lambda 
(u2: T).(\lambda (_: A).(drop (S n) O (CHead x0 (Bind Void) x1) (CHead d2 
(Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g 
d2 d1)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 
(asucc g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 
u1 a))))) (ex2_2 C T (\lambda (d2: C).(\lambda (u2: T).(drop (S n) O (CHead 
x0 (Bind Void) x1) (CHead d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: 
T).(csuba g d2 d1)))) (ex2_2_intro C T (\lambda (d2: C).(\lambda (u2: 
T).(drop (S n) O (CHead x0 (Bind Void) x1) (CHead d2 (Bind Void) u2)))) 
(\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1))) x2 x3 (drop_drop (Bind 
Void) n x0 (CHead x2 (Bind Void) x3) H13 x1) H14)))))) H12)) H11)) c2 H9))))) 
H8)) H7))))) (\lambda (H5: (csuba g c2 (CHead c (Bind Abst) t))).(\lambda 
(H6: (drop (r (Bind Abst) n) O c (CHead d1 (Bind Abbr) u1))).(let H_x \def 
(csuba_gen_abst_rev g c c2 t H5) in (let H7 \def H_x in (or_ind (ex2 C 
(\lambda (d2: C).(eq C c2 (CHead d2 (Bind Abst) t))) (\lambda (d2: C).(csuba 
g d2 c))) (ex2_2 C T (\lambda (d2: C).(\lambda (u2: T).(eq C c2 (CHead d2 
(Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 c)))) (or3 
(ex2 C (\lambda (d2: C).(drop (S n) O c2 (CHead d2 (Bind Abbr) u1))) (\lambda 
(d2: C).(csuba g d2 d1))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: 
T).(\lambda (_: A).(drop (S n) O c2 (CHead d2 (Bind Abst) u2))))) (\lambda 
(d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) (\lambda 
(_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 a))))) (ex2_2 C T 
(\lambda (d2: C).(\lambda (u2: T).(drop (S n) O c2 (CHead d2 (Bind Void) 
u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1))))) (\lambda (H8: 
(ex2 C (\lambda (d2: C).(eq C c2 (CHead d2 (Bind Abst) t))) (\lambda (d2: 
C).(csuba g d2 c)))).(ex2_ind C (\lambda (d2: C).(eq C c2 (CHead d2 (Bind 
Abst) t))) (\lambda (d2: C).(csuba g d2 c)) (or3 (ex2 C (\lambda (d2: 
C).(drop (S n) O c2 (CHead d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 
d1))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(drop (S 
n) O c2 (CHead d2 (Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: 
T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda (d2: C).(\lambda (u2: 
T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) (\lambda (_: C).(\lambda 
(_: T).(\lambda (a: A).(arity g d1 u1 a))))) (ex2_2 C T (\lambda (d2: 
C).(\lambda (u2: T).(drop (S n) O c2 (CHead d2 (Bind Void) u2)))) (\lambda 
(d2: C).(\lambda (_: T).(csuba g d2 d1))))) (\lambda (x: C).(\lambda (H9: (eq 
C c2 (CHead x (Bind Abst) t))).(\lambda (H10: (csuba g x c)).(eq_ind_r C 
(CHead x (Bind Abst) t) (\lambda (c0: C).(or3 (ex2 C (\lambda (d2: C).(drop 
(S n) O c0 (CHead d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1))) 
(ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(drop (S n) O 
c0 (CHead d2 (Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda 
(_: A).(csuba g d2 d1)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: 
A).(arity g d2 u2 (asucc g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda 
(a: A).(arity g d1 u1 a))))) (ex2_2 C T (\lambda (d2: C).(\lambda (u2: 
T).(drop (S n) O c0 (CHead d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda 
(_: T).(csuba g d2 d1)))))) (let H11 \def (H c d1 u1 H6 g x H10) in (or3_ind 
(ex2 C (\lambda (d2: C).(drop n O x (CHead d2 (Bind Abbr) u1))) (\lambda (d2: 
C).(csuba g d2 d1))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda 
(_: A).(drop n O x (CHead d2 (Bind Abst) u2))))) (\lambda (d2: C).(\lambda 
(_: T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda (d2: C).(\lambda (u2: 
T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) (\lambda (_: C).(\lambda 
(_: T).(\lambda (a: A).(arity g d1 u1 a))))) (ex2_2 C T (\lambda (d2: 
C).(\lambda (u2: T).(drop n O x (CHead d2 (Bind Void) u2)))) (\lambda (d2: 
C).(\lambda (_: T).(csuba g d2 d1)))) (or3 (ex2 C (\lambda (d2: C).(drop (S 
n) O (CHead x (Bind Abst) t) (CHead d2 (Bind Abbr) u1))) (\lambda (d2: 
C).(csuba g d2 d1))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda 
(_: A).(drop (S n) O (CHead x (Bind Abst) t) (CHead d2 (Bind Abst) u2))))) 
(\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda 
(d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) 
(\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 a))))) (ex2_2 
C T (\lambda (d2: C).(\lambda (u2: T).(drop (S n) O (CHead x (Bind Abst) t) 
(CHead d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 
d1))))) (\lambda (H12: (ex2 C (\lambda (d2: C).(drop n O x (CHead d2 (Bind 
Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1)))).(ex2_ind C (\lambda (d2: 
C).(drop n O x (CHead d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1)) 
(or3 (ex2 C (\lambda (d2: C).(drop (S n) O (CHead x (Bind Abst) t) (CHead d2 
(Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C T A (\lambda 
(d2: C).(\lambda (u2: T).(\lambda (_: A).(drop (S n) O (CHead x (Bind Abst) 
t) (CHead d2 (Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda 
(_: A).(csuba g d2 d1)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: 
A).(arity g d2 u2 (asucc g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda 
(a: A).(arity g d1 u1 a))))) (ex2_2 C T (\lambda (d2: C).(\lambda (u2: 
T).(drop (S n) O (CHead x (Bind Abst) t) (CHead d2 (Bind Void) u2)))) 
(\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1))))) (\lambda (x0: 
C).(\lambda (H13: (drop n O x (CHead x0 (Bind Abbr) u1))).(\lambda (H14: 
(csuba g x0 d1)).(or3_intro0 (ex2 C (\lambda (d2: C).(drop (S n) O (CHead x 
(Bind Abst) t) (CHead d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1))) 
(ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(drop (S n) O 
(CHead x (Bind Abst) t) (CHead d2 (Bind Abst) u2))))) (\lambda (d2: 
C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) (\lambda 
(_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 a))))) (ex2_2 C T 
(\lambda (d2: C).(\lambda (u2: T).(drop (S n) O (CHead x (Bind Abst) t) 
(CHead d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 
d1)))) (ex_intro2 C (\lambda (d2: C).(drop (S n) O (CHead x (Bind Abst) t) 
(CHead d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1)) x0 (drop_drop 
(Bind Abst) n x (CHead x0 (Bind Abbr) u1) H13 t) H14))))) H12)) (\lambda 
(H12: (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(drop n 
O x (CHead d2 (Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda 
(_: A).(csuba g d2 d1)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: 
A).(arity g d2 u2 (asucc g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda 
(a: A).(arity g d1 u1 a)))))).(ex4_3_ind C T A (\lambda (d2: C).(\lambda (u2: 
T).(\lambda (_: A).(drop n O x (CHead d2 (Bind Abst) u2))))) (\lambda (d2: 
C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) (\lambda 
(_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 a)))) (or3 (ex2 C 
(\lambda (d2: C).(drop (S n) O (CHead x (Bind Abst) t) (CHead d2 (Bind Abbr) 
u1))) (\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C T A (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (_: A).(drop (S n) O (CHead x (Bind Abst) t) 
(CHead d2 (Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: 
A).(csuba g d2 d1)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: 
A).(arity g d2 u2 (asucc g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda 
(a: A).(arity g d1 u1 a))))) (ex2_2 C T (\lambda (d2: C).(\lambda (u2: 
T).(drop (S n) O (CHead x (Bind Abst) t) (CHead d2 (Bind Void) u2)))) 
(\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1))))) (\lambda (x0: 
C).(\lambda (x1: T).(\lambda (x2: A).(\lambda (H13: (drop n O x (CHead x0 
(Bind Abst) x1))).(\lambda (H14: (csuba g x0 d1)).(\lambda (H15: (arity g x0 
x1 (asucc g x2))).(\lambda (H16: (arity g d1 u1 x2)).(or3_intro1 (ex2 C 
(\lambda (d2: C).(drop (S n) O (CHead x (Bind Abst) t) (CHead d2 (Bind Abbr) 
u1))) (\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C T A (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (_: A).(drop (S n) O (CHead x (Bind Abst) t) 
(CHead d2 (Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: 
A).(csuba g d2 d1)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: 
A).(arity g d2 u2 (asucc g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda 
(a: A).(arity g d1 u1 a))))) (ex2_2 C T (\lambda (d2: C).(\lambda (u2: 
T).(drop (S n) O (CHead x (Bind Abst) t) (CHead d2 (Bind Void) u2)))) 
(\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1)))) (ex4_3_intro C T A 
(\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(drop (S n) O (CHead x 
(Bind Abst) t) (CHead d2 (Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: 
T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda (d2: C).(\lambda (u2: 
T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) (\lambda (_: C).(\lambda 
(_: T).(\lambda (a: A).(arity g d1 u1 a)))) x0 x1 x2 (drop_drop (Bind Abst) n 
x (CHead x0 (Bind Abst) x1) H13 t) H14 H15 H16))))))))) H12)) (\lambda (H12: 
(ex2_2 C T (\lambda (d2: C).(\lambda (u2: T).(drop n O x (CHead d2 (Bind 
Void) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1))))).(ex2_2_ind 
C T (\lambda (d2: C).(\lambda (u2: T).(drop n O x (CHead d2 (Bind Void) 
u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1))) (or3 (ex2 C 
(\lambda (d2: C).(drop (S n) O (CHead x (Bind Abst) t) (CHead d2 (Bind Abbr) 
u1))) (\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C T A (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (_: A).(drop (S n) O (CHead x (Bind Abst) t) 
(CHead d2 (Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: 
A).(csuba g d2 d1)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: 
A).(arity g d2 u2 (asucc g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda 
(a: A).(arity g d1 u1 a))))) (ex2_2 C T (\lambda (d2: C).(\lambda (u2: 
T).(drop (S n) O (CHead x (Bind Abst) t) (CHead d2 (Bind Void) u2)))) 
(\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1))))) (\lambda (x0: 
C).(\lambda (x1: T).(\lambda (H13: (drop n O x (CHead x0 (Bind Void) 
x1))).(\lambda (H14: (csuba g x0 d1)).(or3_intro2 (ex2 C (\lambda (d2: 
C).(drop (S n) O (CHead x (Bind Abst) t) (CHead d2 (Bind Abbr) u1))) (\lambda 
(d2: C).(csuba g d2 d1))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: 
T).(\lambda (_: A).(drop (S n) O (CHead x (Bind Abst) t) (CHead d2 (Bind 
Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 
d1)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 
(asucc g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 
u1 a))))) (ex2_2 C T (\lambda (d2: C).(\lambda (u2: T).(drop (S n) O (CHead x 
(Bind Abst) t) (CHead d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: 
T).(csuba g d2 d1)))) (ex2_2_intro C T (\lambda (d2: C).(\lambda (u2: 
T).(drop (S n) O (CHead x (Bind Abst) t) (CHead d2 (Bind Void) u2)))) 
(\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1))) x0 x1 (drop_drop (Bind 
Abst) n x (CHead x0 (Bind Void) x1) H13 t) H14)))))) H12)) H11)) c2 H9)))) 
H8)) (\lambda (H8: (ex2_2 C T (\lambda (d2: C).(\lambda (u2: T).(eq C c2 
(CHead d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 
c))))).(ex2_2_ind C T (\lambda (d2: C).(\lambda (u2: T).(eq C c2 (CHead d2 
(Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 c))) (or3 
(ex2 C (\lambda (d2: C).(drop (S n) O c2 (CHead d2 (Bind Abbr) u1))) (\lambda 
(d2: C).(csuba g d2 d1))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: 
T).(\lambda (_: A).(drop (S n) O c2 (CHead d2 (Bind Abst) u2))))) (\lambda 
(d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) (\lambda 
(_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 a))))) (ex2_2 C T 
(\lambda (d2: C).(\lambda (u2: T).(drop (S n) O c2 (CHead d2 (Bind Void) 
u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1))))) (\lambda (x0: 
C).(\lambda (x1: T).(\lambda (H9: (eq C c2 (CHead x0 (Bind Void) 
x1))).(\lambda (H10: (csuba g x0 c)).(eq_ind_r C (CHead x0 (Bind Void) x1) 
(\lambda (c0: C).(or3 (ex2 C (\lambda (d2: C).(drop (S n) O c0 (CHead d2 
(Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C T A (\lambda 
(d2: C).(\lambda (u2: T).(\lambda (_: A).(drop (S n) O c0 (CHead d2 (Bind 
Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 
d1)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 
(asucc g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 
u1 a))))) (ex2_2 C T (\lambda (d2: C).(\lambda (u2: T).(drop (S n) O c0 
(CHead d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 
d1)))))) (let H11 \def (H c d1 u1 H6 g x0 H10) in (or3_ind (ex2 C (\lambda 
(d2: C).(drop n O x0 (CHead d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 
d1))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(drop n 
O x0 (CHead d2 (Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda 
(_: A).(csuba g d2 d1)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: 
A).(arity g d2 u2 (asucc g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda 
(a: A).(arity g d1 u1 a))))) (ex2_2 C T (\lambda (d2: C).(\lambda (u2: 
T).(drop n O x0 (CHead d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: 
T).(csuba g d2 d1)))) (or3 (ex2 C (\lambda (d2: C).(drop (S n) O (CHead x0 
(Bind Void) x1) (CHead d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 
d1))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(drop (S 
n) O (CHead x0 (Bind Void) x1) (CHead d2 (Bind Abst) u2))))) (\lambda (d2: 
C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) (\lambda 
(_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 a))))) (ex2_2 C T 
(\lambda (d2: C).(\lambda (u2: T).(drop (S n) O (CHead x0 (Bind Void) x1) 
(CHead d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 
d1))))) (\lambda (H12: (ex2 C (\lambda (d2: C).(drop n O x0 (CHead d2 (Bind 
Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1)))).(ex2_ind C (\lambda (d2: 
C).(drop n O x0 (CHead d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1)) 
(or3 (ex2 C (\lambda (d2: C).(drop (S n) O (CHead x0 (Bind Void) x1) (CHead 
d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C T A (\lambda 
(d2: C).(\lambda (u2: T).(\lambda (_: A).(drop (S n) O (CHead x0 (Bind Void) 
x1) (CHead d2 (Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda 
(_: A).(csuba g d2 d1)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: 
A).(arity g d2 u2 (asucc g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda 
(a: A).(arity g d1 u1 a))))) (ex2_2 C T (\lambda (d2: C).(\lambda (u2: 
T).(drop (S n) O (CHead x0 (Bind Void) x1) (CHead d2 (Bind Void) u2)))) 
(\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1))))) (\lambda (x: C).(\lambda 
(H13: (drop n O x0 (CHead x (Bind Abbr) u1))).(\lambda (H14: (csuba g x 
d1)).(or3_intro0 (ex2 C (\lambda (d2: C).(drop (S n) O (CHead x0 (Bind Void) 
x1) (CHead d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C T 
A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(drop (S n) O (CHead x0 
(Bind Void) x1) (CHead d2 (Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: 
T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda (d2: C).(\lambda (u2: 
T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) (\lambda (_: C).(\lambda 
(_: T).(\lambda (a: A).(arity g d1 u1 a))))) (ex2_2 C T (\lambda (d2: 
C).(\lambda (u2: T).(drop (S n) O (CHead x0 (Bind Void) x1) (CHead d2 (Bind 
Void) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1)))) (ex_intro2 C 
(\lambda (d2: C).(drop (S n) O (CHead x0 (Bind Void) x1) (CHead d2 (Bind 
Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1)) x (drop_drop (Bind Void) n x0 
(CHead x (Bind Abbr) u1) H13 x1) H14))))) H12)) (\lambda (H12: (ex4_3 C T A 
(\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(drop n O x0 (CHead d2 
(Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g 
d2 d1)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 
(asucc g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 
u1 a)))))).(ex4_3_ind C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: 
A).(drop n O x0 (CHead d2 (Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: 
T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda (d2: C).(\lambda (u2: 
T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) (\lambda (_: C).(\lambda 
(_: T).(\lambda (a: A).(arity g d1 u1 a)))) (or3 (ex2 C (\lambda (d2: 
C).(drop (S n) O (CHead x0 (Bind Void) x1) (CHead d2 (Bind Abbr) u1))) 
(\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C T A (\lambda (d2: C).(\lambda 
(u2: T).(\lambda (_: A).(drop (S n) O (CHead x0 (Bind Void) x1) (CHead d2 
(Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g 
d2 d1)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 
(asucc g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 
u1 a))))) (ex2_2 C T (\lambda (d2: C).(\lambda (u2: T).(drop (S n) O (CHead 
x0 (Bind Void) x1) (CHead d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: 
T).(csuba g d2 d1))))) (\lambda (x2: C).(\lambda (x3: T).(\lambda (x4: 
A).(\lambda (H13: (drop n O x0 (CHead x2 (Bind Abst) x3))).(\lambda (H14: 
(csuba g x2 d1)).(\lambda (H15: (arity g x2 x3 (asucc g x4))).(\lambda (H16: 
(arity g d1 u1 x4)).(or3_intro1 (ex2 C (\lambda (d2: C).(drop (S n) O (CHead 
x0 (Bind Void) x1) (CHead d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 
d1))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(drop (S 
n) O (CHead x0 (Bind Void) x1) (CHead d2 (Bind Abst) u2))))) (\lambda (d2: 
C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) (\lambda 
(_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 a))))) (ex2_2 C T 
(\lambda (d2: C).(\lambda (u2: T).(drop (S n) O (CHead x0 (Bind Void) x1) 
(CHead d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 
d1)))) (ex4_3_intro C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: 
A).(drop (S n) O (CHead x0 (Bind Void) x1) (CHead d2 (Bind Abst) u2))))) 
(\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda 
(d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) 
(\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 a)))) x2 x3 x4 
(drop_drop (Bind Void) n x0 (CHead x2 (Bind Abst) x3) H13 x1) H14 H15 
H16))))))))) H12)) (\lambda (H12: (ex2_2 C T (\lambda (d2: C).(\lambda (u2: 
T).(drop n O x0 (CHead d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: 
T).(csuba g d2 d1))))).(ex2_2_ind C T (\lambda (d2: C).(\lambda (u2: T).(drop 
n O x0 (CHead d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g 
d2 d1))) (or3 (ex2 C (\lambda (d2: C).(drop (S n) O (CHead x0 (Bind Void) x1) 
(CHead d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C T A 
(\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(drop (S n) O (CHead x0 
(Bind Void) x1) (CHead d2 (Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: 
T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda (d2: C).(\lambda (u2: 
T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) (\lambda (_: C).(\lambda 
(_: T).(\lambda (a: A).(arity g d1 u1 a))))) (ex2_2 C T (\lambda (d2: 
C).(\lambda (u2: T).(drop (S n) O (CHead x0 (Bind Void) x1) (CHead d2 (Bind 
Void) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1))))) (\lambda 
(x2: C).(\lambda (x3: T).(\lambda (H13: (drop n O x0 (CHead x2 (Bind Void) 
x3))).(\lambda (H14: (csuba g x2 d1)).(or3_intro2 (ex2 C (\lambda (d2: 
C).(drop (S n) O (CHead x0 (Bind Void) x1) (CHead d2 (Bind Abbr) u1))) 
(\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C T A (\lambda (d2: C).(\lambda 
(u2: T).(\lambda (_: A).(drop (S n) O (CHead x0 (Bind Void) x1) (CHead d2 
(Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g 
d2 d1)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 
(asucc g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 
u1 a))))) (ex2_2 C T (\lambda (d2: C).(\lambda (u2: T).(drop (S n) O (CHead 
x0 (Bind Void) x1) (CHead d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: 
T).(csuba g d2 d1)))) (ex2_2_intro C T (\lambda (d2: C).(\lambda (u2: 
T).(drop (S n) O (CHead x0 (Bind Void) x1) (CHead d2 (Bind Void) u2)))) 
(\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1))) x2 x3 (drop_drop (Bind 
Void) n x0 (CHead x2 (Bind Void) x3) H13 x1) H14)))))) H12)) H11)) c2 H9))))) 
H8)) H7))))) (\lambda (H5: (csuba g c2 (CHead c (Bind Void) t))).(\lambda 
(H6: (drop (r (Bind Void) n) O c (CHead d1 (Bind Abbr) u1))).(let H_x \def 
(csuba_gen_void_rev g c c2 t H5) in (let H7 \def H_x in (ex2_ind C (\lambda 
(d2: C).(eq C c2 (CHead d2 (Bind Void) t))) (\lambda (d2: C).(csuba g d2 c)) 
(or3 (ex2 C (\lambda (d2: C).(drop (S n) O c2 (CHead d2 (Bind Abbr) u1))) 
(\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C T A (\lambda (d2: C).(\lambda 
(u2: T).(\lambda (_: A).(drop (S n) O c2 (CHead d2 (Bind Abst) u2))))) 
(\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda 
(d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) 
(\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 a))))) (ex2_2 
C T (\lambda (d2: C).(\lambda (u2: T).(drop (S n) O c2 (CHead d2 (Bind Void) 
u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1))))) (\lambda (x: 
C).(\lambda (H8: (eq C c2 (CHead x (Bind Void) t))).(\lambda (H9: (csuba g x 
c)).(eq_ind_r C (CHead x (Bind Void) t) (\lambda (c0: C).(or3 (ex2 C (\lambda 
(d2: C).(drop (S n) O c0 (CHead d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba 
g d2 d1))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: 
A).(drop (S n) O c0 (CHead d2 (Bind Abst) u2))))) (\lambda (d2: C).(\lambda 
(_: T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda (d2: C).(\lambda (u2: 
T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) (\lambda (_: C).(\lambda 
(_: T).(\lambda (a: A).(arity g d1 u1 a))))) (ex2_2 C T (\lambda (d2: 
C).(\lambda (u2: T).(drop (S n) O c0 (CHead d2 (Bind Void) u2)))) (\lambda 
(d2: C).(\lambda (_: T).(csuba g d2 d1)))))) (let H10 \def (H c d1 u1 H6 g x 
H9) in (or3_ind (ex2 C (\lambda (d2: C).(drop n O x (CHead d2 (Bind Abbr) 
u1))) (\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C T A (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (_: A).(drop n O x (CHead d2 (Bind Abst) u2))))) 
(\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda 
(d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) 
(\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 a))))) (ex2_2 
C T (\lambda (d2: C).(\lambda (u2: T).(drop n O x (CHead d2 (Bind Void) 
u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1)))) (or3 (ex2 C 
(\lambda (d2: C).(drop (S n) O (CHead x (Bind Void) t) (CHead d2 (Bind Abbr) 
u1))) (\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C T A (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (_: A).(drop (S n) O (CHead x (Bind Void) t) 
(CHead d2 (Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: 
A).(csuba g d2 d1)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: 
A).(arity g d2 u2 (asucc g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda 
(a: A).(arity g d1 u1 a))))) (ex2_2 C T (\lambda (d2: C).(\lambda (u2: 
T).(drop (S n) O (CHead x (Bind Void) t) (CHead d2 (Bind Void) u2)))) 
(\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1))))) (\lambda (H11: (ex2 C 
(\lambda (d2: C).(drop n O x (CHead d2 (Bind Abbr) u1))) (\lambda (d2: 
C).(csuba g d2 d1)))).(ex2_ind C (\lambda (d2: C).(drop n O x (CHead d2 (Bind 
Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1)) (or3 (ex2 C (\lambda (d2: 
C).(drop (S n) O (CHead x (Bind Void) t) (CHead d2 (Bind Abbr) u1))) (\lambda 
(d2: C).(csuba g d2 d1))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: 
T).(\lambda (_: A).(drop (S n) O (CHead x (Bind Void) t) (CHead d2 (Bind 
Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 
d1)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 
(asucc g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 
u1 a))))) (ex2_2 C T (\lambda (d2: C).(\lambda (u2: T).(drop (S n) O (CHead x 
(Bind Void) t) (CHead d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: 
T).(csuba g d2 d1))))) (\lambda (x0: C).(\lambda (H12: (drop n O x (CHead x0 
(Bind Abbr) u1))).(\lambda (H13: (csuba g x0 d1)).(or3_intro0 (ex2 C (\lambda 
(d2: C).(drop (S n) O (CHead x (Bind Void) t) (CHead d2 (Bind Abbr) u1))) 
(\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C T A (\lambda (d2: C).(\lambda 
(u2: T).(\lambda (_: A).(drop (S n) O (CHead x (Bind Void) t) (CHead d2 (Bind 
Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 
d1)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 
(asucc g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 
u1 a))))) (ex2_2 C T (\lambda (d2: C).(\lambda (u2: T).(drop (S n) O (CHead x 
(Bind Void) t) (CHead d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: 
T).(csuba g d2 d1)))) (ex_intro2 C (\lambda (d2: C).(drop (S n) O (CHead x 
(Bind Void) t) (CHead d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1)) 
x0 (drop_drop (Bind Void) n x (CHead x0 (Bind Abbr) u1) H12 t) H13))))) H11)) 
(\lambda (H11: (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: 
A).(drop n O x (CHead d2 (Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: 
T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda (d2: C).(\lambda (u2: 
T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) (\lambda (_: C).(\lambda 
(_: T).(\lambda (a: A).(arity g d1 u1 a)))))).(ex4_3_ind C T A (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (_: A).(drop n O x (CHead d2 (Bind Abst) u2))))) 
(\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda 
(d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) 
(\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 a)))) (or3 
(ex2 C (\lambda (d2: C).(drop (S n) O (CHead x (Bind Void) t) (CHead d2 (Bind 
Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C T A (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (_: A).(drop (S n) O (CHead x (Bind Void) t) 
(CHead d2 (Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: 
A).(csuba g d2 d1)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: 
A).(arity g d2 u2 (asucc g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda 
(a: A).(arity g d1 u1 a))))) (ex2_2 C T (\lambda (d2: C).(\lambda (u2: 
T).(drop (S n) O (CHead x (Bind Void) t) (CHead d2 (Bind Void) u2)))) 
(\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1))))) (\lambda (x0: 
C).(\lambda (x1: T).(\lambda (x2: A).(\lambda (H12: (drop n O x (CHead x0 
(Bind Abst) x1))).(\lambda (H13: (csuba g x0 d1)).(\lambda (H14: (arity g x0 
x1 (asucc g x2))).(\lambda (H15: (arity g d1 u1 x2)).(or3_intro1 (ex2 C 
(\lambda (d2: C).(drop (S n) O (CHead x (Bind Void) t) (CHead d2 (Bind Abbr) 
u1))) (\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C T A (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (_: A).(drop (S n) O (CHead x (Bind Void) t) 
(CHead d2 (Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: 
A).(csuba g d2 d1)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: 
A).(arity g d2 u2 (asucc g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda 
(a: A).(arity g d1 u1 a))))) (ex2_2 C T (\lambda (d2: C).(\lambda (u2: 
T).(drop (S n) O (CHead x (Bind Void) t) (CHead d2 (Bind Void) u2)))) 
(\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1)))) (ex4_3_intro C T A 
(\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(drop (S n) O (CHead x 
(Bind Void) t) (CHead d2 (Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: 
T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda (d2: C).(\lambda (u2: 
T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) (\lambda (_: C).(\lambda 
(_: T).(\lambda (a: A).(arity g d1 u1 a)))) x0 x1 x2 (drop_drop (Bind Void) n 
x (CHead x0 (Bind Abst) x1) H12 t) H13 H14 H15))))))))) H11)) (\lambda (H11: 
(ex2_2 C T (\lambda (d2: C).(\lambda (u2: T).(drop n O x (CHead d2 (Bind 
Void) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1))))).(ex2_2_ind 
C T (\lambda (d2: C).(\lambda (u2: T).(drop n O x (CHead d2 (Bind Void) 
u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1))) (or3 (ex2 C 
(\lambda (d2: C).(drop (S n) O (CHead x (Bind Void) t) (CHead d2 (Bind Abbr) 
u1))) (\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C T A (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (_: A).(drop (S n) O (CHead x (Bind Void) t) 
(CHead d2 (Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: 
A).(csuba g d2 d1)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: 
A).(arity g d2 u2 (asucc g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda 
(a: A).(arity g d1 u1 a))))) (ex2_2 C T (\lambda (d2: C).(\lambda (u2: 
T).(drop (S n) O (CHead x (Bind Void) t) (CHead d2 (Bind Void) u2)))) 
(\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1))))) (\lambda (x0: 
C).(\lambda (x1: T).(\lambda (H12: (drop n O x (CHead x0 (Bind Void) 
x1))).(\lambda (H13: (csuba g x0 d1)).(or3_intro2 (ex2 C (\lambda (d2: 
C).(drop (S n) O (CHead x (Bind Void) t) (CHead d2 (Bind Abbr) u1))) (\lambda 
(d2: C).(csuba g d2 d1))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: 
T).(\lambda (_: A).(drop (S n) O (CHead x (Bind Void) t) (CHead d2 (Bind 
Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 
d1)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 
(asucc g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 
u1 a))))) (ex2_2 C T (\lambda (d2: C).(\lambda (u2: T).(drop (S n) O (CHead x 
(Bind Void) t) (CHead d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: 
T).(csuba g d2 d1)))) (ex2_2_intro C T (\lambda (d2: C).(\lambda (u2: 
T).(drop (S n) O (CHead x (Bind Void) t) (CHead d2 (Bind Void) u2)))) 
(\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1))) x0 x1 (drop_drop (Bind 
Void) n x (CHead x0 (Bind Void) x1) H12 t) H13)))))) H11)) H10)) c2 H8)))) 
H7))))) b H3 H4)))) (\lambda (f: F).(\lambda (H3: (csuba g c2 (CHead c (Flat 
f) t))).(\lambda (H4: (drop (r (Flat f) n) O c (CHead d1 (Bind Abbr) 
u1))).(let H_x \def (csuba_gen_flat_rev g c c2 t f H3) in (let H5 \def H_x in 
(ex2_2_ind C T (\lambda (d2: C).(\lambda (u2: T).(eq C c2 (CHead d2 (Flat f) 
u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 c))) (or3 (ex2 C (\lambda 
(d2: C).(drop (S n) O c2 (CHead d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba 
g d2 d1))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: 
A).(drop (S n) O c2 (CHead d2 (Bind Abst) u2))))) (\lambda (d2: C).(\lambda 
(_: T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda (d2: C).(\lambda (u2: 
T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) (\lambda (_: C).(\lambda 
(_: T).(\lambda (a: A).(arity g d1 u1 a))))) (ex2_2 C T (\lambda (d2: 
C).(\lambda (u2: T).(drop (S n) O c2 (CHead d2 (Bind Void) u2)))) (\lambda 
(d2: C).(\lambda (_: T).(csuba g d2 d1))))) (\lambda (x0: C).(\lambda (x1: 
T).(\lambda (H6: (eq C c2 (CHead x0 (Flat f) x1))).(\lambda (H7: (csuba g x0 
c)).(eq_ind_r C (CHead x0 (Flat f) x1) (\lambda (c0: C).(or3 (ex2 C (\lambda 
(d2: C).(drop (S n) O c0 (CHead d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba 
g d2 d1))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: 
A).(drop (S n) O c0 (CHead d2 (Bind Abst) u2))))) (\lambda (d2: C).(\lambda 
(_: T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda (d2: C).(\lambda (u2: 
T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) (\lambda (_: C).(\lambda 
(_: T).(\lambda (a: A).(arity g d1 u1 a))))) (ex2_2 C T (\lambda (d2: 
C).(\lambda (u2: T).(drop (S n) O c0 (CHead d2 (Bind Void) u2)))) (\lambda 
(d2: C).(\lambda (_: T).(csuba g d2 d1)))))) (let H8 \def (H0 d1 u1 H4 g x0 
H7) in (or3_ind (ex2 C (\lambda (d2: C).(drop (S n) O x0 (CHead d2 (Bind 
Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C T A (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (_: A).(drop (S n) O x0 (CHead d2 (Bind Abst) 
u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 d1)))) 
(\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 (asucc g 
a))))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 a))))) 
(ex2_2 C T (\lambda (d2: C).(\lambda (u2: T).(drop (S n) O x0 (CHead d2 (Bind 
Void) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1)))) (or3 (ex2 C 
(\lambda (d2: C).(drop (S n) O (CHead x0 (Flat f) x1) (CHead d2 (Bind Abbr) 
u1))) (\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C T A (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (_: A).(drop (S n) O (CHead x0 (Flat f) x1) 
(CHead d2 (Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: 
A).(csuba g d2 d1)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: 
A).(arity g d2 u2 (asucc g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda 
(a: A).(arity g d1 u1 a))))) (ex2_2 C T (\lambda (d2: C).(\lambda (u2: 
T).(drop (S n) O (CHead x0 (Flat f) x1) (CHead d2 (Bind Void) u2)))) (\lambda 
(d2: C).(\lambda (_: T).(csuba g d2 d1))))) (\lambda (H9: (ex2 C (\lambda 
(d2: C).(drop (S n) O x0 (CHead d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba 
g d2 d1)))).(ex2_ind C (\lambda (d2: C).(drop (S n) O x0 (CHead d2 (Bind 
Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1)) (or3 (ex2 C (\lambda (d2: 
C).(drop (S n) O (CHead x0 (Flat f) x1) (CHead d2 (Bind Abbr) u1))) (\lambda 
(d2: C).(csuba g d2 d1))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: 
T).(\lambda (_: A).(drop (S n) O (CHead x0 (Flat f) x1) (CHead d2 (Bind Abst) 
u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 d1)))) 
(\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 (asucc g 
a))))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 a))))) 
(ex2_2 C T (\lambda (d2: C).(\lambda (u2: T).(drop (S n) O (CHead x0 (Flat f) 
x1) (CHead d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 
d1))))) (\lambda (x: C).(\lambda (H10: (drop (S n) O x0 (CHead x (Bind Abbr) 
u1))).(\lambda (H11: (csuba g x d1)).(or3_intro0 (ex2 C (\lambda (d2: 
C).(drop (S n) O (CHead x0 (Flat f) x1) (CHead d2 (Bind Abbr) u1))) (\lambda 
(d2: C).(csuba g d2 d1))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: 
T).(\lambda (_: A).(drop (S n) O (CHead x0 (Flat f) x1) (CHead d2 (Bind Abst) 
u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 d1)))) 
(\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 (asucc g 
a))))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 a))))) 
(ex2_2 C T (\lambda (d2: C).(\lambda (u2: T).(drop (S n) O (CHead x0 (Flat f) 
x1) (CHead d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 
d1)))) (ex_intro2 C (\lambda (d2: C).(drop (S n) O (CHead x0 (Flat f) x1) 
(CHead d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1)) x (drop_drop 
(Flat f) n x0 (CHead x (Bind Abbr) u1) H10 x1) H11))))) H9)) (\lambda (H9: 
(ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(drop (S n) O 
x0 (CHead d2 (Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda 
(_: A).(csuba g d2 d1)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: 
A).(arity g d2 u2 (asucc g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda 
(a: A).(arity g d1 u1 a)))))).(ex4_3_ind C T A (\lambda (d2: C).(\lambda (u2: 
T).(\lambda (_: A).(drop (S n) O x0 (CHead d2 (Bind Abst) u2))))) (\lambda 
(d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) (\lambda 
(_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 a)))) (or3 (ex2 C 
(\lambda (d2: C).(drop (S n) O (CHead x0 (Flat f) x1) (CHead d2 (Bind Abbr) 
u1))) (\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C T A (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (_: A).(drop (S n) O (CHead x0 (Flat f) x1) 
(CHead d2 (Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: 
A).(csuba g d2 d1)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: 
A).(arity g d2 u2 (asucc g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda 
(a: A).(arity g d1 u1 a))))) (ex2_2 C T (\lambda (d2: C).(\lambda (u2: 
T).(drop (S n) O (CHead x0 (Flat f) x1) (CHead d2 (Bind Void) u2)))) (\lambda 
(d2: C).(\lambda (_: T).(csuba g d2 d1))))) (\lambda (x2: C).(\lambda (x3: 
T).(\lambda (x4: A).(\lambda (H10: (drop (S n) O x0 (CHead x2 (Bind Abst) 
x3))).(\lambda (H11: (csuba g x2 d1)).(\lambda (H12: (arity g x2 x3 (asucc g 
x4))).(\lambda (H13: (arity g d1 u1 x4)).(or3_intro1 (ex2 C (\lambda (d2: 
C).(drop (S n) O (CHead x0 (Flat f) x1) (CHead d2 (Bind Abbr) u1))) (\lambda 
(d2: C).(csuba g d2 d1))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: 
T).(\lambda (_: A).(drop (S n) O (CHead x0 (Flat f) x1) (CHead d2 (Bind Abst) 
u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 d1)))) 
(\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 (asucc g 
a))))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 a))))) 
(ex2_2 C T (\lambda (d2: C).(\lambda (u2: T).(drop (S n) O (CHead x0 (Flat f) 
x1) (CHead d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 
d1)))) (ex4_3_intro C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: 
A).(drop (S n) O (CHead x0 (Flat f) x1) (CHead d2 (Bind Abst) u2))))) 
(\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda 
(d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) 
(\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 a)))) x2 x3 x4 
(drop_drop (Flat f) n x0 (CHead x2 (Bind Abst) x3) H10 x1) H11 H12 
H13))))))))) H9)) (\lambda (H9: (ex2_2 C T (\lambda (d2: C).(\lambda (u2: 
T).(drop (S n) O x0 (CHead d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda 
(_: T).(csuba g d2 d1))))).(ex2_2_ind C T (\lambda (d2: C).(\lambda (u2: 
T).(drop (S n) O x0 (CHead d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda 
(_: T).(csuba g d2 d1))) (or3 (ex2 C (\lambda (d2: C).(drop (S n) O (CHead x0 
(Flat f) x1) (CHead d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1))) 
(ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(drop (S n) O 
(CHead x0 (Flat f) x1) (CHead d2 (Bind Abst) u2))))) (\lambda (d2: 
C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) (\lambda 
(_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 a))))) (ex2_2 C T 
(\lambda (d2: C).(\lambda (u2: T).(drop (S n) O (CHead x0 (Flat f) x1) (CHead 
d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1))))) 
(\lambda (x2: C).(\lambda (x3: T).(\lambda (H10: (drop (S n) O x0 (CHead x2 
(Bind Void) x3))).(\lambda (H11: (csuba g x2 d1)).(or3_intro2 (ex2 C (\lambda 
(d2: C).(drop (S n) O (CHead x0 (Flat f) x1) (CHead d2 (Bind Abbr) u1))) 
(\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C T A (\lambda (d2: C).(\lambda 
(u2: T).(\lambda (_: A).(drop (S n) O (CHead x0 (Flat f) x1) (CHead d2 (Bind 
Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 
d1)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 
(asucc g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 
u1 a))))) (ex2_2 C T (\lambda (d2: C).(\lambda (u2: T).(drop (S n) O (CHead 
x0 (Flat f) x1) (CHead d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: 
T).(csuba g d2 d1)))) (ex2_2_intro C T (\lambda (d2: C).(\lambda (u2: 
T).(drop (S n) O (CHead x0 (Flat f) x1) (CHead d2 (Bind Void) u2)))) (\lambda 
(d2: C).(\lambda (_: T).(csuba g d2 d1))) x2 x3 (drop_drop (Flat f) n x0 
(CHead x2 (Bind Void) x3) H10 x1) H11)))))) H9)) H8)) c2 H6))))) H5)))))) k 
H2 (drop_gen_drop k c (CHead d1 (Bind Abbr) u1) t n H1)))))))))))) c1)))) i).
(* COMMENTS
Initial nodes: 23852
END *)

