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

include "Basic-1/csubt/fwd.ma".

include "Basic-1/drop/fwd.ma".

theorem csubt_drop_flat:
 \forall (g: G).(\forall (f: F).(\forall (n: nat).(\forall (c1: C).(\forall 
(c2: C).((csubt g c1 c2) \to (\forall (d1: C).(\forall (u: T).((drop n O c1 
(CHead d1 (Flat f) u)) \to (ex2 C (\lambda (d2: C).(csubt g d1 d2)) (\lambda 
(d2: C).(drop n O c2 (CHead d2 (Flat f) u))))))))))))
\def
 \lambda (g: G).(\lambda (f: F).(\lambda (n: nat).(nat_ind (\lambda (n0: 
nat).(\forall (c1: C).(\forall (c2: C).((csubt g c1 c2) \to (\forall (d1: 
C).(\forall (u: T).((drop n0 O c1 (CHead d1 (Flat f) u)) \to (ex2 C (\lambda 
(d2: C).(csubt g d1 d2)) (\lambda (d2: C).(drop n0 O c2 (CHead d2 (Flat f) 
u))))))))))) (\lambda (c1: C).(\lambda (c2: C).(\lambda (H: (csubt g c1 
c2)).(\lambda (d1: C).(\lambda (u: T).(\lambda (H0: (drop O O c1 (CHead d1 
(Flat f) u))).(let H1 \def (eq_ind C c1 (\lambda (c: C).(csubt g c c2)) H 
(CHead d1 (Flat f) u) (drop_gen_refl c1 (CHead d1 (Flat f) u) H0)) in (let 
H_x \def (csubt_gen_flat g d1 c2 u f H1) in (let H2 \def H_x in (ex2_ind C 
(\lambda (e2: C).(eq C c2 (CHead e2 (Flat f) u))) (\lambda (e2: C).(csubt g 
d1 e2)) (ex2 C (\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: C).(drop O O 
c2 (CHead d2 (Flat f) u)))) (\lambda (x: C).(\lambda (H3: (eq C c2 (CHead x 
(Flat f) u))).(\lambda (H4: (csubt g d1 x)).(eq_ind_r C (CHead x (Flat f) u) 
(\lambda (c: C).(ex2 C (\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: 
C).(drop O O c (CHead d2 (Flat f) u))))) (ex_intro2 C (\lambda (d2: C).(csubt 
g d1 d2)) (\lambda (d2: C).(drop O O (CHead x (Flat f) u) (CHead d2 (Flat f) 
u))) x H4 (drop_refl (CHead x (Flat f) u))) c2 H3)))) H2)))))))))) (\lambda 
(n0: nat).(\lambda (H: ((\forall (c1: C).(\forall (c2: C).((csubt g c1 c2) 
\to (\forall (d1: C).(\forall (u: T).((drop n0 O c1 (CHead d1 (Flat f) u)) 
\to (ex2 C (\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: C).(drop n0 O c2 
(CHead d2 (Flat f) u)))))))))))).(\lambda (c1: C).(\lambda (c2: C).(\lambda 
(H0: (csubt g c1 c2)).(csubt_ind g (\lambda (c: C).(\lambda (c0: C).(\forall 
(d1: C).(\forall (u: T).((drop (S n0) O c (CHead d1 (Flat f) u)) \to (ex2 C 
(\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: C).(drop (S n0) O c0 (CHead 
d2 (Flat f) u))))))))) (\lambda (n1: nat).(\lambda (d1: C).(\lambda (u: 
T).(\lambda (H1: (drop (S n0) O (CSort n1) (CHead d1 (Flat f) u))).(and3_ind 
(eq C (CHead d1 (Flat f) u) (CSort n1)) (eq nat (S n0) O) (eq nat O O) (ex2 C 
(\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: C).(drop (S n0) O (CSort n1) 
(CHead d2 (Flat f) u)))) (\lambda (_: (eq C (CHead d1 (Flat f) u) (CSort 
n1))).(\lambda (H3: (eq nat (S n0) O)).(\lambda (_: (eq nat O O)).(let H5 
\def (eq_ind nat (S n0) (\lambda (ee: nat).(match ee in nat return (\lambda 
(_: nat).Prop) with [O \Rightarrow False | (S _) \Rightarrow True])) I O H3) 
in (False_ind (ex2 C (\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: C).(drop 
(S n0) O (CSort n1) (CHead d2 (Flat f) u)))) H5))))) (drop_gen_sort n1 (S n0) 
O (CHead d1 (Flat f) u) H1)))))) (\lambda (c0: C).(\lambda (c3: C).(\lambda 
(H1: (csubt g c0 c3)).(\lambda (H2: ((\forall (d1: C).(\forall (u: T).((drop 
(S n0) O c0 (CHead d1 (Flat f) u)) \to (ex2 C (\lambda (d2: C).(csubt g d1 
d2)) (\lambda (d2: C).(drop (S n0) O c3 (CHead d2 (Flat f) 
u))))))))).(\lambda (k: K).(K_ind (\lambda (k0: K).(\forall (u: T).(\forall 
(d1: C).(\forall (u0: T).((drop (S n0) O (CHead c0 k0 u) (CHead d1 (Flat f) 
u0)) \to (ex2 C (\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: C).(drop (S 
n0) O (CHead c3 k0 u) (CHead d2 (Flat f) u0))))))))) (\lambda (b: B).(\lambda 
(u: T).(\lambda (d1: C).(\lambda (u0: T).(\lambda (H3: (drop (S n0) O (CHead 
c0 (Bind b) u) (CHead d1 (Flat f) u0))).(ex2_ind C (\lambda (d2: C).(csubt g 
d1 d2)) (\lambda (d2: C).(drop n0 O c3 (CHead d2 (Flat f) u0))) (ex2 C 
(\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: C).(drop (S n0) O (CHead c3 
(Bind b) u) (CHead d2 (Flat f) u0)))) (\lambda (x: C).(\lambda (H4: (csubt g 
d1 x)).(\lambda (H5: (drop n0 O c3 (CHead x (Flat f) u0))).(ex_intro2 C 
(\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: C).(drop (S n0) O (CHead c3 
(Bind b) u) (CHead d2 (Flat f) u0))) x H4 (drop_drop (Bind b) n0 c3 (CHead x 
(Flat f) u0) H5 u))))) (H c0 c3 H1 d1 u0 (drop_gen_drop (Bind b) c0 (CHead d1 
(Flat f) u0) u n0 H3)))))))) (\lambda (f0: F).(\lambda (u: T).(\lambda (d1: 
C).(\lambda (u0: T).(\lambda (H3: (drop (S n0) O (CHead c0 (Flat f0) u) 
(CHead d1 (Flat f) u0))).(ex2_ind C (\lambda (d2: C).(csubt g d1 d2)) 
(\lambda (d2: C).(drop (S n0) O c3 (CHead d2 (Flat f) u0))) (ex2 C (\lambda 
(d2: C).(csubt g d1 d2)) (\lambda (d2: C).(drop (S n0) O (CHead c3 (Flat f0) 
u) (CHead d2 (Flat f) u0)))) (\lambda (x: C).(\lambda (H4: (csubt g d1 
x)).(\lambda (H5: (drop (S n0) O c3 (CHead x (Flat f) u0))).(ex_intro2 C 
(\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: C).(drop (S n0) O (CHead c3 
(Flat f0) u) (CHead d2 (Flat f) u0))) x H4 (drop_drop (Flat f0) n0 c3 (CHead 
x (Flat f) u0) H5 u))))) (H2 d1 u0 (drop_gen_drop (Flat f0) c0 (CHead d1 
(Flat f) u0) u n0 H3)))))))) k)))))) (\lambda (c0: C).(\lambda (c3: 
C).(\lambda (H1: (csubt g c0 c3)).(\lambda (_: ((\forall (d1: C).(\forall (u: 
T).((drop (S n0) O c0 (CHead d1 (Flat f) u)) \to (ex2 C (\lambda (d2: 
C).(csubt g d1 d2)) (\lambda (d2: C).(drop (S n0) O c3 (CHead d2 (Flat f) 
u))))))))).(\lambda (b: B).(\lambda (_: (not (eq B b Void))).(\lambda (u1: 
T).(\lambda (u2: T).(\lambda (d1: C).(\lambda (u: T).(\lambda (H4: (drop (S 
n0) O (CHead c0 (Bind Void) u1) (CHead d1 (Flat f) u))).(ex2_ind C (\lambda 
(d2: C).(csubt g d1 d2)) (\lambda (d2: C).(drop n0 O c3 (CHead d2 (Flat f) 
u))) (ex2 C (\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: C).(drop (S n0) O 
(CHead c3 (Bind b) u2) (CHead d2 (Flat f) u)))) (\lambda (x: C).(\lambda (H5: 
(csubt g d1 x)).(\lambda (H6: (drop n0 O c3 (CHead x (Flat f) u))).(ex_intro2 
C (\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: C).(drop (S n0) O (CHead c3 
(Bind b) u2) (CHead d2 (Flat f) u))) x H5 (drop_drop (Bind b) n0 c3 (CHead x 
(Flat f) u) H6 u2))))) (H c0 c3 H1 d1 u (drop_gen_drop (Bind Void) c0 (CHead 
d1 (Flat f) u) u1 n0 H4)))))))))))))) (\lambda (c0: C).(\lambda (c3: 
C).(\lambda (H1: (csubt g c0 c3)).(\lambda (_: ((\forall (d1: C).(\forall (u: 
T).((drop (S n0) O c0 (CHead d1 (Flat f) u)) \to (ex2 C (\lambda (d2: 
C).(csubt g d1 d2)) (\lambda (d2: C).(drop (S n0) O c3 (CHead d2 (Flat f) 
u))))))))).(\lambda (u: T).(\lambda (t: T).(\lambda (_: (ty3 g c0 u 
t)).(\lambda (_: (ty3 g c3 u t)).(\lambda (d1: C).(\lambda (u0: T).(\lambda 
(H5: (drop (S n0) O (CHead c0 (Bind Abst) t) (CHead d1 (Flat f) 
u0))).(ex2_ind C (\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: C).(drop n0 
O c3 (CHead d2 (Flat f) u0))) (ex2 C (\lambda (d2: C).(csubt g d1 d2)) 
(\lambda (d2: C).(drop (S n0) O (CHead c3 (Bind Abbr) u) (CHead d2 (Flat f) 
u0)))) (\lambda (x: C).(\lambda (H6: (csubt g d1 x)).(\lambda (H7: (drop n0 O 
c3 (CHead x (Flat f) u0))).(ex_intro2 C (\lambda (d2: C).(csubt g d1 d2)) 
(\lambda (d2: C).(drop (S n0) O (CHead c3 (Bind Abbr) u) (CHead d2 (Flat f) 
u0))) x H6 (drop_drop (Bind Abbr) n0 c3 (CHead x (Flat f) u0) H7 u))))) (H c0 
c3 H1 d1 u0 (drop_gen_drop (Bind Abst) c0 (CHead d1 (Flat f) u0) t n0 
H5)))))))))))))) c1 c2 H0)))))) n))).
(* COMMENTS
Initial nodes: 2090
END *)

theorem csubt_drop_abbr:
 \forall (g: G).(\forall (n: nat).(\forall (c1: C).(\forall (c2: C).((csubt g 
c1 c2) \to (\forall (d1: C).(\forall (u: T).((drop n O c1 (CHead d1 (Bind 
Abbr) u)) \to (ex2 C (\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: C).(drop 
n O c2 (CHead d2 (Bind Abbr) u)))))))))))
\def
 \lambda (g: G).(\lambda (n: nat).(nat_ind (\lambda (n0: nat).(\forall (c1: 
C).(\forall (c2: C).((csubt g c1 c2) \to (\forall (d1: C).(\forall (u: 
T).((drop n0 O c1 (CHead d1 (Bind Abbr) u)) \to (ex2 C (\lambda (d2: 
C).(csubt g d1 d2)) (\lambda (d2: C).(drop n0 O c2 (CHead d2 (Bind Abbr) 
u))))))))))) (\lambda (c1: C).(\lambda (c2: C).(\lambda (H: (csubt g c1 
c2)).(\lambda (d1: C).(\lambda (u: T).(\lambda (H0: (drop O O c1 (CHead d1 
(Bind Abbr) u))).(let H1 \def (eq_ind C c1 (\lambda (c: C).(csubt g c c2)) H 
(CHead d1 (Bind Abbr) u) (drop_gen_refl c1 (CHead d1 (Bind Abbr) u) H0)) in 
(let H2 \def (csubt_gen_abbr g d1 c2 u H1) in (ex2_ind C (\lambda (e2: C).(eq 
C c2 (CHead e2 (Bind Abbr) u))) (\lambda (e2: C).(csubt g d1 e2)) (ex2 C 
(\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: C).(drop O O c2 (CHead d2 
(Bind Abbr) u)))) (\lambda (x: C).(\lambda (H3: (eq C c2 (CHead x (Bind Abbr) 
u))).(\lambda (H4: (csubt g d1 x)).(eq_ind_r C (CHead x (Bind Abbr) u) 
(\lambda (c: C).(ex2 C (\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: 
C).(drop O O c (CHead d2 (Bind Abbr) u))))) (ex_intro2 C (\lambda (d2: 
C).(csubt g d1 d2)) (\lambda (d2: C).(drop O O (CHead x (Bind Abbr) u) (CHead 
d2 (Bind Abbr) u))) x H4 (drop_refl (CHead x (Bind Abbr) u))) c2 H3)))) 
H2))))))))) (\lambda (n0: nat).(\lambda (H: ((\forall (c1: C).(\forall (c2: 
C).((csubt g c1 c2) \to (\forall (d1: C).(\forall (u: T).((drop n0 O c1 
(CHead d1 (Bind Abbr) u)) \to (ex2 C (\lambda (d2: C).(csubt g d1 d2)) 
(\lambda (d2: C).(drop n0 O c2 (CHead d2 (Bind Abbr) u)))))))))))).(\lambda 
(c1: C).(\lambda (c2: C).(\lambda (H0: (csubt g c1 c2)).(csubt_ind g (\lambda 
(c: C).(\lambda (c0: C).(\forall (d1: C).(\forall (u: T).((drop (S n0) O c 
(CHead d1 (Bind Abbr) u)) \to (ex2 C (\lambda (d2: C).(csubt g d1 d2)) 
(\lambda (d2: C).(drop (S n0) O c0 (CHead d2 (Bind Abbr) u))))))))) (\lambda 
(n1: nat).(\lambda (d1: C).(\lambda (u: T).(\lambda (H1: (drop (S n0) O 
(CSort n1) (CHead d1 (Bind Abbr) u))).(and3_ind (eq C (CHead d1 (Bind Abbr) 
u) (CSort n1)) (eq nat (S n0) O) (eq nat O O) (ex2 C (\lambda (d2: C).(csubt 
g d1 d2)) (\lambda (d2: C).(drop (S n0) O (CSort n1) (CHead d2 (Bind Abbr) 
u)))) (\lambda (_: (eq C (CHead d1 (Bind Abbr) u) (CSort n1))).(\lambda (H3: 
(eq nat (S n0) O)).(\lambda (_: (eq nat O O)).(let H5 \def (eq_ind nat (S n0) 
(\lambda (ee: nat).(match ee in nat return (\lambda (_: nat).Prop) with [O 
\Rightarrow False | (S _) \Rightarrow True])) I O H3) in (False_ind (ex2 C 
(\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: C).(drop (S n0) O (CSort n1) 
(CHead d2 (Bind Abbr) u)))) H5))))) (drop_gen_sort n1 (S n0) O (CHead d1 
(Bind Abbr) u) H1)))))) (\lambda (c0: C).(\lambda (c3: C).(\lambda (H1: 
(csubt g c0 c3)).(\lambda (H2: ((\forall (d1: C).(\forall (u: T).((drop (S 
n0) O c0 (CHead d1 (Bind Abbr) u)) \to (ex2 C (\lambda (d2: C).(csubt g d1 
d2)) (\lambda (d2: C).(drop (S n0) O c3 (CHead d2 (Bind Abbr) 
u))))))))).(\lambda (k: K).(K_ind (\lambda (k0: K).(\forall (u: T).(\forall 
(d1: C).(\forall (u0: T).((drop (S n0) O (CHead c0 k0 u) (CHead d1 (Bind 
Abbr) u0)) \to (ex2 C (\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: 
C).(drop (S n0) O (CHead c3 k0 u) (CHead d2 (Bind Abbr) u0))))))))) (\lambda 
(b: B).(\lambda (u: T).(\lambda (d1: C).(\lambda (u0: T).(\lambda (H3: (drop 
(S n0) O (CHead c0 (Bind b) u) (CHead d1 (Bind Abbr) u0))).(ex2_ind C 
(\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: C).(drop n0 O c3 (CHead d2 
(Bind Abbr) u0))) (ex2 C (\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: 
C).(drop (S n0) O (CHead c3 (Bind b) u) (CHead d2 (Bind Abbr) u0)))) (\lambda 
(x: C).(\lambda (H4: (csubt g d1 x)).(\lambda (H5: (drop n0 O c3 (CHead x 
(Bind Abbr) u0))).(ex_intro2 C (\lambda (d2: C).(csubt g d1 d2)) (\lambda 
(d2: C).(drop (S n0) O (CHead c3 (Bind b) u) (CHead d2 (Bind Abbr) u0))) x H4 
(drop_drop (Bind b) n0 c3 (CHead x (Bind Abbr) u0) H5 u))))) (H c0 c3 H1 d1 
u0 (drop_gen_drop (Bind b) c0 (CHead d1 (Bind Abbr) u0) u n0 H3)))))))) 
(\lambda (f: F).(\lambda (u: T).(\lambda (d1: C).(\lambda (u0: T).(\lambda 
(H3: (drop (S n0) O (CHead c0 (Flat f) u) (CHead d1 (Bind Abbr) 
u0))).(ex2_ind C (\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: C).(drop (S 
n0) O c3 (CHead d2 (Bind Abbr) u0))) (ex2 C (\lambda (d2: C).(csubt g d1 d2)) 
(\lambda (d2: C).(drop (S n0) O (CHead c3 (Flat f) u) (CHead d2 (Bind Abbr) 
u0)))) (\lambda (x: C).(\lambda (H4: (csubt g d1 x)).(\lambda (H5: (drop (S 
n0) O c3 (CHead x (Bind Abbr) u0))).(ex_intro2 C (\lambda (d2: C).(csubt g d1 
d2)) (\lambda (d2: C).(drop (S n0) O (CHead c3 (Flat f) u) (CHead d2 (Bind 
Abbr) u0))) x H4 (drop_drop (Flat f) n0 c3 (CHead x (Bind Abbr) u0) H5 u))))) 
(H2 d1 u0 (drop_gen_drop (Flat f) c0 (CHead d1 (Bind Abbr) u0) u n0 
H3)))))))) k)))))) (\lambda (c0: C).(\lambda (c3: C).(\lambda (H1: (csubt g 
c0 c3)).(\lambda (_: ((\forall (d1: C).(\forall (u: T).((drop (S n0) O c0 
(CHead d1 (Bind Abbr) u)) \to (ex2 C (\lambda (d2: C).(csubt g d1 d2)) 
(\lambda (d2: C).(drop (S n0) O c3 (CHead d2 (Bind Abbr) u))))))))).(\lambda 
(b: B).(\lambda (_: (not (eq B b Void))).(\lambda (u1: T).(\lambda (u2: 
T).(\lambda (d1: C).(\lambda (u: T).(\lambda (H4: (drop (S n0) O (CHead c0 
(Bind Void) u1) (CHead d1 (Bind Abbr) u))).(ex2_ind C (\lambda (d2: C).(csubt 
g d1 d2)) (\lambda (d2: C).(drop n0 O c3 (CHead d2 (Bind Abbr) u))) (ex2 C 
(\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: C).(drop (S n0) O (CHead c3 
(Bind b) u2) (CHead d2 (Bind Abbr) u)))) (\lambda (x: C).(\lambda (H5: (csubt 
g d1 x)).(\lambda (H6: (drop n0 O c3 (CHead x (Bind Abbr) u))).(ex_intro2 C 
(\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: C).(drop (S n0) O (CHead c3 
(Bind b) u2) (CHead d2 (Bind Abbr) u))) x H5 (drop_drop (Bind b) n0 c3 (CHead 
x (Bind Abbr) u) H6 u2))))) (H c0 c3 H1 d1 u (drop_gen_drop (Bind Void) c0 
(CHead d1 (Bind Abbr) u) u1 n0 H4)))))))))))))) (\lambda (c0: C).(\lambda 
(c3: C).(\lambda (H1: (csubt g c0 c3)).(\lambda (_: ((\forall (d1: 
C).(\forall (u: T).((drop (S n0) O c0 (CHead d1 (Bind Abbr) u)) \to (ex2 C 
(\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: C).(drop (S n0) O c3 (CHead 
d2 (Bind Abbr) u))))))))).(\lambda (u: T).(\lambda (t: T).(\lambda (_: (ty3 g 
c0 u t)).(\lambda (_: (ty3 g c3 u t)).(\lambda (d1: C).(\lambda (u0: 
T).(\lambda (H5: (drop (S n0) O (CHead c0 (Bind Abst) t) (CHead d1 (Bind 
Abbr) u0))).(ex2_ind C (\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: 
C).(drop n0 O c3 (CHead d2 (Bind Abbr) u0))) (ex2 C (\lambda (d2: C).(csubt g 
d1 d2)) (\lambda (d2: C).(drop (S n0) O (CHead c3 (Bind Abbr) u) (CHead d2 
(Bind Abbr) u0)))) (\lambda (x: C).(\lambda (H6: (csubt g d1 x)).(\lambda 
(H7: (drop n0 O c3 (CHead x (Bind Abbr) u0))).(ex_intro2 C (\lambda (d2: 
C).(csubt g d1 d2)) (\lambda (d2: C).(drop (S n0) O (CHead c3 (Bind Abbr) u) 
(CHead d2 (Bind Abbr) u0))) x H6 (drop_drop (Bind Abbr) n0 c3 (CHead x (Bind 
Abbr) u0) H7 u))))) (H c0 c3 H1 d1 u0 (drop_gen_drop (Bind Abst) c0 (CHead d1 
(Bind Abbr) u0) t n0 H5)))))))))))))) c1 c2 H0)))))) n)).
(* COMMENTS
Initial nodes: 2084
END *)

theorem csubt_drop_abst:
 \forall (g: G).(\forall (n: nat).(\forall (c1: C).(\forall (c2: C).((csubt g 
c1 c2) \to (\forall (d1: C).(\forall (t: T).((drop n O c1 (CHead d1 (Bind 
Abst) t)) \to (or (ex2 C (\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: 
C).(drop n O c2 (CHead d2 (Bind Abst) t)))) (ex4_2 C T (\lambda (d2: 
C).(\lambda (_: T).(csubt g d1 d2))) (\lambda (d2: C).(\lambda (u: T).(drop n 
O c2 (CHead d2 (Bind Abbr) u)))) (\lambda (_: C).(\lambda (u: T).(ty3 g d1 u 
t))) (\lambda (d2: C).(\lambda (u: T).(ty3 g d2 u t))))))))))))
\def
 \lambda (g: G).(\lambda (n: nat).(nat_ind (\lambda (n0: nat).(\forall (c1: 
C).(\forall (c2: C).((csubt g c1 c2) \to (\forall (d1: C).(\forall (t: 
T).((drop n0 O c1 (CHead d1 (Bind Abst) t)) \to (or (ex2 C (\lambda (d2: 
C).(csubt g d1 d2)) (\lambda (d2: C).(drop n0 O c2 (CHead d2 (Bind Abst) 
t)))) (ex4_2 C T (\lambda (d2: C).(\lambda (_: T).(csubt g d1 d2))) (\lambda 
(d2: C).(\lambda (u: T).(drop n0 O c2 (CHead d2 (Bind Abbr) u)))) (\lambda 
(_: C).(\lambda (u: T).(ty3 g d1 u t))) (\lambda (d2: C).(\lambda (u: T).(ty3 
g d2 u t)))))))))))) (\lambda (c1: C).(\lambda (c2: C).(\lambda (H: (csubt g 
c1 c2)).(\lambda (d1: C).(\lambda (t: T).(\lambda (H0: (drop O O c1 (CHead d1 
(Bind Abst) t))).(let H1 \def (eq_ind C c1 (\lambda (c: C).(csubt g c c2)) H 
(CHead d1 (Bind Abst) t) (drop_gen_refl c1 (CHead d1 (Bind Abst) t) H0)) in 
(let H2 \def (csubt_gen_abst g d1 c2 t H1) in (or_ind (ex2 C (\lambda (e2: 
C).(eq C c2 (CHead e2 (Bind Abst) t))) (\lambda (e2: C).(csubt g d1 e2))) 
(ex4_2 C T (\lambda (e2: C).(\lambda (v2: T).(eq C c2 (CHead e2 (Bind Abbr) 
v2)))) (\lambda (e2: C).(\lambda (_: T).(csubt g d1 e2))) (\lambda (_: 
C).(\lambda (v2: T).(ty3 g d1 v2 t))) (\lambda (e2: C).(\lambda (v2: T).(ty3 
g e2 v2 t)))) (or (ex2 C (\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: 
C).(drop O O c2 (CHead d2 (Bind Abst) t)))) (ex4_2 C T (\lambda (d2: 
C).(\lambda (_: T).(csubt g d1 d2))) (\lambda (d2: C).(\lambda (u: T).(drop O 
O c2 (CHead d2 (Bind Abbr) u)))) (\lambda (_: C).(\lambda (u: T).(ty3 g d1 u 
t))) (\lambda (d2: C).(\lambda (u: T).(ty3 g d2 u t))))) (\lambda (H3: (ex2 C 
(\lambda (e2: C).(eq C c2 (CHead e2 (Bind Abst) t))) (\lambda (e2: C).(csubt 
g d1 e2)))).(ex2_ind C (\lambda (e2: C).(eq C c2 (CHead e2 (Bind Abst) t))) 
(\lambda (e2: C).(csubt g d1 e2)) (or (ex2 C (\lambda (d2: C).(csubt g d1 
d2)) (\lambda (d2: C).(drop O O c2 (CHead d2 (Bind Abst) t)))) (ex4_2 C T 
(\lambda (d2: C).(\lambda (_: T).(csubt g d1 d2))) (\lambda (d2: C).(\lambda 
(u: T).(drop O O c2 (CHead d2 (Bind Abbr) u)))) (\lambda (_: C).(\lambda (u: 
T).(ty3 g d1 u t))) (\lambda (d2: C).(\lambda (u: T).(ty3 g d2 u t))))) 
(\lambda (x: C).(\lambda (H4: (eq C c2 (CHead x (Bind Abst) t))).(\lambda 
(H5: (csubt g d1 x)).(eq_ind_r C (CHead x (Bind Abst) t) (\lambda (c: C).(or 
(ex2 C (\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: C).(drop O O c (CHead 
d2 (Bind Abst) t)))) (ex4_2 C T (\lambda (d2: C).(\lambda (_: T).(csubt g d1 
d2))) (\lambda (d2: C).(\lambda (u: T).(drop O O c (CHead d2 (Bind Abbr) 
u)))) (\lambda (_: C).(\lambda (u: T).(ty3 g d1 u t))) (\lambda (d2: 
C).(\lambda (u: T).(ty3 g d2 u t)))))) (or_introl (ex2 C (\lambda (d2: 
C).(csubt g d1 d2)) (\lambda (d2: C).(drop O O (CHead x (Bind Abst) t) (CHead 
d2 (Bind Abst) t)))) (ex4_2 C T (\lambda (d2: C).(\lambda (_: T).(csubt g d1 
d2))) (\lambda (d2: C).(\lambda (u: T).(drop O O (CHead x (Bind Abst) t) 
(CHead d2 (Bind Abbr) u)))) (\lambda (_: C).(\lambda (u: T).(ty3 g d1 u t))) 
(\lambda (d2: C).(\lambda (u: T).(ty3 g d2 u t)))) (ex_intro2 C (\lambda (d2: 
C).(csubt g d1 d2)) (\lambda (d2: C).(drop O O (CHead x (Bind Abst) t) (CHead 
d2 (Bind Abst) t))) x H5 (drop_refl (CHead x (Bind Abst) t)))) c2 H4)))) H3)) 
(\lambda (H3: (ex4_2 C T (\lambda (e2: C).(\lambda (v2: T).(eq C c2 (CHead e2 
(Bind Abbr) v2)))) (\lambda (e2: C).(\lambda (_: T).(csubt g d1 e2))) 
(\lambda (_: C).(\lambda (v2: T).(ty3 g d1 v2 t))) (\lambda (e2: C).(\lambda 
(v2: T).(ty3 g e2 v2 t))))).(ex4_2_ind C T (\lambda (e2: C).(\lambda (v2: 
T).(eq C c2 (CHead e2 (Bind Abbr) v2)))) (\lambda (e2: C).(\lambda (_: 
T).(csubt g d1 e2))) (\lambda (_: C).(\lambda (v2: T).(ty3 g d1 v2 t))) 
(\lambda (e2: C).(\lambda (v2: T).(ty3 g e2 v2 t))) (or (ex2 C (\lambda (d2: 
C).(csubt g d1 d2)) (\lambda (d2: C).(drop O O c2 (CHead d2 (Bind Abst) t)))) 
(ex4_2 C T (\lambda (d2: C).(\lambda (_: T).(csubt g d1 d2))) (\lambda (d2: 
C).(\lambda (u: T).(drop O O c2 (CHead d2 (Bind Abbr) u)))) (\lambda (_: 
C).(\lambda (u: T).(ty3 g d1 u t))) (\lambda (d2: C).(\lambda (u: T).(ty3 g 
d2 u t))))) (\lambda (x0: C).(\lambda (x1: T).(\lambda (H4: (eq C c2 (CHead 
x0 (Bind Abbr) x1))).(\lambda (H5: (csubt g d1 x0)).(\lambda (H6: (ty3 g d1 
x1 t)).(\lambda (H7: (ty3 g x0 x1 t)).(eq_ind_r C (CHead x0 (Bind Abbr) x1) 
(\lambda (c: C).(or (ex2 C (\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: 
C).(drop O O c (CHead d2 (Bind Abst) t)))) (ex4_2 C T (\lambda (d2: 
C).(\lambda (_: T).(csubt g d1 d2))) (\lambda (d2: C).(\lambda (u: T).(drop O 
O c (CHead d2 (Bind Abbr) u)))) (\lambda (_: C).(\lambda (u: T).(ty3 g d1 u 
t))) (\lambda (d2: C).(\lambda (u: T).(ty3 g d2 u t)))))) (or_intror (ex2 C 
(\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: C).(drop O O (CHead x0 (Bind 
Abbr) x1) (CHead d2 (Bind Abst) t)))) (ex4_2 C T (\lambda (d2: C).(\lambda 
(_: T).(csubt g d1 d2))) (\lambda (d2: C).(\lambda (u: T).(drop O O (CHead x0 
(Bind Abbr) x1) (CHead d2 (Bind Abbr) u)))) (\lambda (_: C).(\lambda (u: 
T).(ty3 g d1 u t))) (\lambda (d2: C).(\lambda (u: T).(ty3 g d2 u t)))) 
(ex4_2_intro C T (\lambda (d2: C).(\lambda (_: T).(csubt g d1 d2))) (\lambda 
(d2: C).(\lambda (u: T).(drop O O (CHead x0 (Bind Abbr) x1) (CHead d2 (Bind 
Abbr) u)))) (\lambda (_: C).(\lambda (u: T).(ty3 g d1 u t))) (\lambda (d2: 
C).(\lambda (u: T).(ty3 g d2 u t))) x0 x1 H5 (drop_refl (CHead x0 (Bind Abbr) 
x1)) H6 H7)) c2 H4))))))) H3)) H2))))))))) (\lambda (n0: nat).(\lambda (H: 
((\forall (c1: C).(\forall (c2: C).((csubt g c1 c2) \to (\forall (d1: 
C).(\forall (t: T).((drop n0 O c1 (CHead d1 (Bind Abst) t)) \to (or (ex2 C 
(\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: C).(drop n0 O c2 (CHead d2 
(Bind Abst) t)))) (ex4_2 C T (\lambda (d2: C).(\lambda (_: T).(csubt g d1 
d2))) (\lambda (d2: C).(\lambda (u: T).(drop n0 O c2 (CHead d2 (Bind Abbr) 
u)))) (\lambda (_: C).(\lambda (u: T).(ty3 g d1 u t))) (\lambda (d2: 
C).(\lambda (u: T).(ty3 g d2 u t))))))))))))).(\lambda (c1: C).(\lambda (c2: 
C).(\lambda (H0: (csubt g c1 c2)).(csubt_ind g (\lambda (c: C).(\lambda (c0: 
C).(\forall (d1: C).(\forall (t: T).((drop (S n0) O c (CHead d1 (Bind Abst) 
t)) \to (or (ex2 C (\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: C).(drop 
(S n0) O c0 (CHead d2 (Bind Abst) t)))) (ex4_2 C T (\lambda (d2: C).(\lambda 
(_: T).(csubt g d1 d2))) (\lambda (d2: C).(\lambda (u: T).(drop (S n0) O c0 
(CHead d2 (Bind Abbr) u)))) (\lambda (_: C).(\lambda (u: T).(ty3 g d1 u t))) 
(\lambda (d2: C).(\lambda (u: T).(ty3 g d2 u t)))))))))) (\lambda (n1: 
nat).(\lambda (d1: C).(\lambda (t: T).(\lambda (H1: (drop (S n0) O (CSort n1) 
(CHead d1 (Bind Abst) t))).(and3_ind (eq C (CHead d1 (Bind Abst) t) (CSort 
n1)) (eq nat (S n0) O) (eq nat O O) (or (ex2 C (\lambda (d2: C).(csubt g d1 
d2)) (\lambda (d2: C).(drop (S n0) O (CSort n1) (CHead d2 (Bind Abst) t)))) 
(ex4_2 C T (\lambda (d2: C).(\lambda (_: T).(csubt g d1 d2))) (\lambda (d2: 
C).(\lambda (u: T).(drop (S n0) O (CSort n1) (CHead d2 (Bind Abbr) u)))) 
(\lambda (_: C).(\lambda (u: T).(ty3 g d1 u t))) (\lambda (d2: C).(\lambda 
(u: T).(ty3 g d2 u t))))) (\lambda (_: (eq C (CHead d1 (Bind Abst) t) (CSort 
n1))).(\lambda (H3: (eq nat (S n0) O)).(\lambda (_: (eq nat O O)).(let H5 
\def (eq_ind nat (S n0) (\lambda (ee: nat).(match ee in nat return (\lambda 
(_: nat).Prop) with [O \Rightarrow False | (S _) \Rightarrow True])) I O H3) 
in (False_ind (or (ex2 C (\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: 
C).(drop (S n0) O (CSort n1) (CHead d2 (Bind Abst) t)))) (ex4_2 C T (\lambda 
(d2: C).(\lambda (_: T).(csubt g d1 d2))) (\lambda (d2: C).(\lambda (u: 
T).(drop (S n0) O (CSort n1) (CHead d2 (Bind Abbr) u)))) (\lambda (_: 
C).(\lambda (u: T).(ty3 g d1 u t))) (\lambda (d2: C).(\lambda (u: T).(ty3 g 
d2 u t))))) H5))))) (drop_gen_sort n1 (S n0) O (CHead d1 (Bind Abst) t) 
H1)))))) (\lambda (c0: C).(\lambda (c3: C).(\lambda (H1: (csubt g c0 
c3)).(\lambda (H2: ((\forall (d1: C).(\forall (t: T).((drop (S n0) O c0 
(CHead d1 (Bind Abst) t)) \to (or (ex2 C (\lambda (d2: C).(csubt g d1 d2)) 
(\lambda (d2: C).(drop (S n0) O c3 (CHead d2 (Bind Abst) t)))) (ex4_2 C T 
(\lambda (d2: C).(\lambda (_: T).(csubt g d1 d2))) (\lambda (d2: C).(\lambda 
(u: T).(drop (S n0) O c3 (CHead d2 (Bind Abbr) u)))) (\lambda (_: C).(\lambda 
(u: T).(ty3 g d1 u t))) (\lambda (d2: C).(\lambda (u: T).(ty3 g d2 u 
t)))))))))).(\lambda (k: K).(K_ind (\lambda (k0: K).(\forall (u: T).(\forall 
(d1: C).(\forall (t: T).((drop (S n0) O (CHead c0 k0 u) (CHead d1 (Bind Abst) 
t)) \to (or (ex2 C (\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: C).(drop 
(S n0) O (CHead c3 k0 u) (CHead d2 (Bind Abst) t)))) (ex4_2 C T (\lambda (d2: 
C).(\lambda (_: T).(csubt g d1 d2))) (\lambda (d2: C).(\lambda (u0: T).(drop 
(S n0) O (CHead c3 k0 u) (CHead d2 (Bind Abbr) u0)))) (\lambda (_: 
C).(\lambda (u0: T).(ty3 g d1 u0 t))) (\lambda (d2: C).(\lambda (u0: T).(ty3 
g d2 u0 t)))))))))) (\lambda (b: B).(\lambda (u: T).(\lambda (d1: C).(\lambda 
(t: T).(\lambda (H3: (drop (S n0) O (CHead c0 (Bind b) u) (CHead d1 (Bind 
Abst) t))).(or_ind (ex2 C (\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: 
C).(drop n0 O c3 (CHead d2 (Bind Abst) t)))) (ex4_2 C T (\lambda (d2: 
C).(\lambda (_: T).(csubt g d1 d2))) (\lambda (d2: C).(\lambda (u0: T).(drop 
n0 O c3 (CHead d2 (Bind Abbr) u0)))) (\lambda (_: C).(\lambda (u0: T).(ty3 g 
d1 u0 t))) (\lambda (d2: C).(\lambda (u0: T).(ty3 g d2 u0 t)))) (or (ex2 C 
(\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: C).(drop (S n0) O (CHead c3 
(Bind b) u) (CHead d2 (Bind Abst) t)))) (ex4_2 C T (\lambda (d2: C).(\lambda 
(_: T).(csubt g d1 d2))) (\lambda (d2: C).(\lambda (u0: T).(drop (S n0) O 
(CHead c3 (Bind b) u) (CHead d2 (Bind Abbr) u0)))) (\lambda (_: C).(\lambda 
(u0: T).(ty3 g d1 u0 t))) (\lambda (d2: C).(\lambda (u0: T).(ty3 g d2 u0 
t))))) (\lambda (H4: (ex2 C (\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: 
C).(drop n0 O c3 (CHead d2 (Bind Abst) t))))).(ex2_ind C (\lambda (d2: 
C).(csubt g d1 d2)) (\lambda (d2: C).(drop n0 O c3 (CHead d2 (Bind Abst) t))) 
(or (ex2 C (\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: C).(drop (S n0) O 
(CHead c3 (Bind b) u) (CHead d2 (Bind Abst) t)))) (ex4_2 C T (\lambda (d2: 
C).(\lambda (_: T).(csubt g d1 d2))) (\lambda (d2: C).(\lambda (u0: T).(drop 
(S n0) O (CHead c3 (Bind b) u) (CHead d2 (Bind Abbr) u0)))) (\lambda (_: 
C).(\lambda (u0: T).(ty3 g d1 u0 t))) (\lambda (d2: C).(\lambda (u0: T).(ty3 
g d2 u0 t))))) (\lambda (x: C).(\lambda (H5: (csubt g d1 x)).(\lambda (H6: 
(drop n0 O c3 (CHead x (Bind Abst) t))).(or_introl (ex2 C (\lambda (d2: 
C).(csubt g d1 d2)) (\lambda (d2: C).(drop (S n0) O (CHead c3 (Bind b) u) 
(CHead d2 (Bind Abst) t)))) (ex4_2 C T (\lambda (d2: C).(\lambda (_: 
T).(csubt g d1 d2))) (\lambda (d2: C).(\lambda (u0: T).(drop (S n0) O (CHead 
c3 (Bind b) u) (CHead d2 (Bind Abbr) u0)))) (\lambda (_: C).(\lambda (u0: 
T).(ty3 g d1 u0 t))) (\lambda (d2: C).(\lambda (u0: T).(ty3 g d2 u0 t)))) 
(ex_intro2 C (\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: C).(drop (S n0) 
O (CHead c3 (Bind b) u) (CHead d2 (Bind Abst) t))) x H5 (drop_drop (Bind b) 
n0 c3 (CHead x (Bind Abst) t) H6 u)))))) H4)) (\lambda (H4: (ex4_2 C T 
(\lambda (d2: C).(\lambda (_: T).(csubt g d1 d2))) (\lambda (d2: C).(\lambda 
(u0: T).(drop n0 O c3 (CHead d2 (Bind Abbr) u0)))) (\lambda (_: C).(\lambda 
(u0: T).(ty3 g d1 u0 t))) (\lambda (d2: C).(\lambda (u0: T).(ty3 g d2 u0 
t))))).(ex4_2_ind C T (\lambda (d2: C).(\lambda (_: T).(csubt g d1 d2))) 
(\lambda (d2: C).(\lambda (u0: T).(drop n0 O c3 (CHead d2 (Bind Abbr) u0)))) 
(\lambda (_: C).(\lambda (u0: T).(ty3 g d1 u0 t))) (\lambda (d2: C).(\lambda 
(u0: T).(ty3 g d2 u0 t))) (or (ex2 C (\lambda (d2: C).(csubt g d1 d2)) 
(\lambda (d2: C).(drop (S n0) O (CHead c3 (Bind b) u) (CHead d2 (Bind Abst) 
t)))) (ex4_2 C T (\lambda (d2: C).(\lambda (_: T).(csubt g d1 d2))) (\lambda 
(d2: C).(\lambda (u0: T).(drop (S n0) O (CHead c3 (Bind b) u) (CHead d2 (Bind 
Abbr) u0)))) (\lambda (_: C).(\lambda (u0: T).(ty3 g d1 u0 t))) (\lambda (d2: 
C).(\lambda (u0: T).(ty3 g d2 u0 t))))) (\lambda (x0: C).(\lambda (x1: 
T).(\lambda (H5: (csubt g d1 x0)).(\lambda (H6: (drop n0 O c3 (CHead x0 (Bind 
Abbr) x1))).(\lambda (H7: (ty3 g d1 x1 t)).(\lambda (H8: (ty3 g x0 x1 
t)).(or_intror (ex2 C (\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: 
C).(drop (S n0) O (CHead c3 (Bind b) u) (CHead d2 (Bind Abst) t)))) (ex4_2 C 
T (\lambda (d2: C).(\lambda (_: T).(csubt g d1 d2))) (\lambda (d2: 
C).(\lambda (u0: T).(drop (S n0) O (CHead c3 (Bind b) u) (CHead d2 (Bind 
Abbr) u0)))) (\lambda (_: C).(\lambda (u0: T).(ty3 g d1 u0 t))) (\lambda (d2: 
C).(\lambda (u0: T).(ty3 g d2 u0 t)))) (ex4_2_intro C T (\lambda (d2: 
C).(\lambda (_: T).(csubt g d1 d2))) (\lambda (d2: C).(\lambda (u0: T).(drop 
(S n0) O (CHead c3 (Bind b) u) (CHead d2 (Bind Abbr) u0)))) (\lambda (_: 
C).(\lambda (u0: T).(ty3 g d1 u0 t))) (\lambda (d2: C).(\lambda (u0: T).(ty3 
g d2 u0 t))) x0 x1 H5 (drop_drop (Bind b) n0 c3 (CHead x0 (Bind Abbr) x1) H6 
u) H7 H8)))))))) H4)) (H c0 c3 H1 d1 t (drop_gen_drop (Bind b) c0 (CHead d1 
(Bind Abst) t) u n0 H3)))))))) (\lambda (f: F).(\lambda (u: T).(\lambda (d1: 
C).(\lambda (t: T).(\lambda (H3: (drop (S n0) O (CHead c0 (Flat f) u) (CHead 
d1 (Bind Abst) t))).(or_ind (ex2 C (\lambda (d2: C).(csubt g d1 d2)) (\lambda 
(d2: C).(drop (S n0) O c3 (CHead d2 (Bind Abst) t)))) (ex4_2 C T (\lambda 
(d2: C).(\lambda (_: T).(csubt g d1 d2))) (\lambda (d2: C).(\lambda (u0: 
T).(drop (S n0) O c3 (CHead d2 (Bind Abbr) u0)))) (\lambda (_: C).(\lambda 
(u0: T).(ty3 g d1 u0 t))) (\lambda (d2: C).(\lambda (u0: T).(ty3 g d2 u0 
t)))) (or (ex2 C (\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: C).(drop (S 
n0) O (CHead c3 (Flat f) u) (CHead d2 (Bind Abst) t)))) (ex4_2 C T (\lambda 
(d2: C).(\lambda (_: T).(csubt g d1 d2))) (\lambda (d2: C).(\lambda (u0: 
T).(drop (S n0) O (CHead c3 (Flat f) u) (CHead d2 (Bind Abbr) u0)))) (\lambda 
(_: C).(\lambda (u0: T).(ty3 g d1 u0 t))) (\lambda (d2: C).(\lambda (u0: 
T).(ty3 g d2 u0 t))))) (\lambda (H4: (ex2 C (\lambda (d2: C).(csubt g d1 d2)) 
(\lambda (d2: C).(drop (S n0) O c3 (CHead d2 (Bind Abst) t))))).(ex2_ind C 
(\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: C).(drop (S n0) O c3 (CHead 
d2 (Bind Abst) t))) (or (ex2 C (\lambda (d2: C).(csubt g d1 d2)) (\lambda 
(d2: C).(drop (S n0) O (CHead c3 (Flat f) u) (CHead d2 (Bind Abst) t)))) 
(ex4_2 C T (\lambda (d2: C).(\lambda (_: T).(csubt g d1 d2))) (\lambda (d2: 
C).(\lambda (u0: T).(drop (S n0) O (CHead c3 (Flat f) u) (CHead d2 (Bind 
Abbr) u0)))) (\lambda (_: C).(\lambda (u0: T).(ty3 g d1 u0 t))) (\lambda (d2: 
C).(\lambda (u0: T).(ty3 g d2 u0 t))))) (\lambda (x: C).(\lambda (H5: (csubt 
g d1 x)).(\lambda (H6: (drop (S n0) O c3 (CHead x (Bind Abst) t))).(or_introl 
(ex2 C (\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: C).(drop (S n0) O 
(CHead c3 (Flat f) u) (CHead d2 (Bind Abst) t)))) (ex4_2 C T (\lambda (d2: 
C).(\lambda (_: T).(csubt g d1 d2))) (\lambda (d2: C).(\lambda (u0: T).(drop 
(S n0) O (CHead c3 (Flat f) u) (CHead d2 (Bind Abbr) u0)))) (\lambda (_: 
C).(\lambda (u0: T).(ty3 g d1 u0 t))) (\lambda (d2: C).(\lambda (u0: T).(ty3 
g d2 u0 t)))) (ex_intro2 C (\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: 
C).(drop (S n0) O (CHead c3 (Flat f) u) (CHead d2 (Bind Abst) t))) x H5 
(drop_drop (Flat f) n0 c3 (CHead x (Bind Abst) t) H6 u)))))) H4)) (\lambda 
(H4: (ex4_2 C T (\lambda (d2: C).(\lambda (_: T).(csubt g d1 d2))) (\lambda 
(d2: C).(\lambda (u0: T).(drop (S n0) O c3 (CHead d2 (Bind Abbr) u0)))) 
(\lambda (_: C).(\lambda (u0: T).(ty3 g d1 u0 t))) (\lambda (d2: C).(\lambda 
(u0: T).(ty3 g d2 u0 t))))).(ex4_2_ind C T (\lambda (d2: C).(\lambda (_: 
T).(csubt g d1 d2))) (\lambda (d2: C).(\lambda (u0: T).(drop (S n0) O c3 
(CHead d2 (Bind Abbr) u0)))) (\lambda (_: C).(\lambda (u0: T).(ty3 g d1 u0 
t))) (\lambda (d2: C).(\lambda (u0: T).(ty3 g d2 u0 t))) (or (ex2 C (\lambda 
(d2: C).(csubt g d1 d2)) (\lambda (d2: C).(drop (S n0) O (CHead c3 (Flat f) 
u) (CHead d2 (Bind Abst) t)))) (ex4_2 C T (\lambda (d2: C).(\lambda (_: 
T).(csubt g d1 d2))) (\lambda (d2: C).(\lambda (u0: T).(drop (S n0) O (CHead 
c3 (Flat f) u) (CHead d2 (Bind Abbr) u0)))) (\lambda (_: C).(\lambda (u0: 
T).(ty3 g d1 u0 t))) (\lambda (d2: C).(\lambda (u0: T).(ty3 g d2 u0 t))))) 
(\lambda (x0: C).(\lambda (x1: T).(\lambda (H5: (csubt g d1 x0)).(\lambda 
(H6: (drop (S n0) O c3 (CHead x0 (Bind Abbr) x1))).(\lambda (H7: (ty3 g d1 x1 
t)).(\lambda (H8: (ty3 g x0 x1 t)).(or_intror (ex2 C (\lambda (d2: C).(csubt 
g d1 d2)) (\lambda (d2: C).(drop (S n0) O (CHead c3 (Flat f) u) (CHead d2 
(Bind Abst) t)))) (ex4_2 C T (\lambda (d2: C).(\lambda (_: T).(csubt g d1 
d2))) (\lambda (d2: C).(\lambda (u0: T).(drop (S n0) O (CHead c3 (Flat f) u) 
(CHead d2 (Bind Abbr) u0)))) (\lambda (_: C).(\lambda (u0: T).(ty3 g d1 u0 
t))) (\lambda (d2: C).(\lambda (u0: T).(ty3 g d2 u0 t)))) (ex4_2_intro C T 
(\lambda (d2: C).(\lambda (_: T).(csubt g d1 d2))) (\lambda (d2: C).(\lambda 
(u0: T).(drop (S n0) O (CHead c3 (Flat f) u) (CHead d2 (Bind Abbr) u0)))) 
(\lambda (_: C).(\lambda (u0: T).(ty3 g d1 u0 t))) (\lambda (d2: C).(\lambda 
(u0: T).(ty3 g d2 u0 t))) x0 x1 H5 (drop_drop (Flat f) n0 c3 (CHead x0 (Bind 
Abbr) x1) H6 u) H7 H8)))))))) H4)) (H2 d1 t (drop_gen_drop (Flat f) c0 (CHead 
d1 (Bind Abst) t) u n0 H3)))))))) k)))))) (\lambda (c0: C).(\lambda (c3: 
C).(\lambda (H1: (csubt g c0 c3)).(\lambda (_: ((\forall (d1: C).(\forall (t: 
T).((drop (S n0) O c0 (CHead d1 (Bind Abst) t)) \to (or (ex2 C (\lambda (d2: 
C).(csubt g d1 d2)) (\lambda (d2: C).(drop (S n0) O c3 (CHead d2 (Bind Abst) 
t)))) (ex4_2 C T (\lambda (d2: C).(\lambda (_: T).(csubt g d1 d2))) (\lambda 
(d2: C).(\lambda (u: T).(drop (S n0) O c3 (CHead d2 (Bind Abbr) u)))) 
(\lambda (_: C).(\lambda (u: T).(ty3 g d1 u t))) (\lambda (d2: C).(\lambda 
(u: T).(ty3 g d2 u t)))))))))).(\lambda (b: B).(\lambda (_: (not (eq B b 
Void))).(\lambda (u1: T).(\lambda (u2: T).(\lambda (d1: C).(\lambda (t: 
T).(\lambda (H4: (drop (S n0) O (CHead c0 (Bind Void) u1) (CHead d1 (Bind 
Abst) t))).(or_ind (ex2 C (\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: 
C).(drop n0 O c3 (CHead d2 (Bind Abst) t)))) (ex4_2 C T (\lambda (d2: 
C).(\lambda (_: T).(csubt g d1 d2))) (\lambda (d2: C).(\lambda (u: T).(drop 
n0 O c3 (CHead d2 (Bind Abbr) u)))) (\lambda (_: C).(\lambda (u: T).(ty3 g d1 
u t))) (\lambda (d2: C).(\lambda (u: T).(ty3 g d2 u t)))) (or (ex2 C (\lambda 
(d2: C).(csubt g d1 d2)) (\lambda (d2: C).(drop (S n0) O (CHead c3 (Bind b) 
u2) (CHead d2 (Bind Abst) t)))) (ex4_2 C T (\lambda (d2: C).(\lambda (_: 
T).(csubt g d1 d2))) (\lambda (d2: C).(\lambda (u: T).(drop (S n0) O (CHead 
c3 (Bind b) u2) (CHead d2 (Bind Abbr) u)))) (\lambda (_: C).(\lambda (u: 
T).(ty3 g d1 u t))) (\lambda (d2: C).(\lambda (u: T).(ty3 g d2 u t))))) 
(\lambda (H5: (ex2 C (\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: C).(drop 
n0 O c3 (CHead d2 (Bind Abst) t))))).(ex2_ind C (\lambda (d2: C).(csubt g d1 
d2)) (\lambda (d2: C).(drop n0 O c3 (CHead d2 (Bind Abst) t))) (or (ex2 C 
(\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: C).(drop (S n0) O (CHead c3 
(Bind b) u2) (CHead d2 (Bind Abst) t)))) (ex4_2 C T (\lambda (d2: C).(\lambda 
(_: T).(csubt g d1 d2))) (\lambda (d2: C).(\lambda (u: T).(drop (S n0) O 
(CHead c3 (Bind b) u2) (CHead d2 (Bind Abbr) u)))) (\lambda (_: C).(\lambda 
(u: T).(ty3 g d1 u t))) (\lambda (d2: C).(\lambda (u: T).(ty3 g d2 u t))))) 
(\lambda (x: C).(\lambda (H6: (csubt g d1 x)).(\lambda (H7: (drop n0 O c3 
(CHead x (Bind Abst) t))).(or_introl (ex2 C (\lambda (d2: C).(csubt g d1 d2)) 
(\lambda (d2: C).(drop (S n0) O (CHead c3 (Bind b) u2) (CHead d2 (Bind Abst) 
t)))) (ex4_2 C T (\lambda (d2: C).(\lambda (_: T).(csubt g d1 d2))) (\lambda 
(d2: C).(\lambda (u: T).(drop (S n0) O (CHead c3 (Bind b) u2) (CHead d2 (Bind 
Abbr) u)))) (\lambda (_: C).(\lambda (u: T).(ty3 g d1 u t))) (\lambda (d2: 
C).(\lambda (u: T).(ty3 g d2 u t)))) (ex_intro2 C (\lambda (d2: C).(csubt g 
d1 d2)) (\lambda (d2: C).(drop (S n0) O (CHead c3 (Bind b) u2) (CHead d2 
(Bind Abst) t))) x H6 (drop_drop (Bind b) n0 c3 (CHead x (Bind Abst) t) H7 
u2)))))) H5)) (\lambda (H5: (ex4_2 C T (\lambda (d2: C).(\lambda (_: 
T).(csubt g d1 d2))) (\lambda (d2: C).(\lambda (u: T).(drop n0 O c3 (CHead d2 
(Bind Abbr) u)))) (\lambda (_: C).(\lambda (u: T).(ty3 g d1 u t))) (\lambda 
(d2: C).(\lambda (u: T).(ty3 g d2 u t))))).(ex4_2_ind C T (\lambda (d2: 
C).(\lambda (_: T).(csubt g d1 d2))) (\lambda (d2: C).(\lambda (u: T).(drop 
n0 O c3 (CHead d2 (Bind Abbr) u)))) (\lambda (_: C).(\lambda (u: T).(ty3 g d1 
u t))) (\lambda (d2: C).(\lambda (u: T).(ty3 g d2 u t))) (or (ex2 C (\lambda 
(d2: C).(csubt g d1 d2)) (\lambda (d2: C).(drop (S n0) O (CHead c3 (Bind b) 
u2) (CHead d2 (Bind Abst) t)))) (ex4_2 C T (\lambda (d2: C).(\lambda (_: 
T).(csubt g d1 d2))) (\lambda (d2: C).(\lambda (u: T).(drop (S n0) O (CHead 
c3 (Bind b) u2) (CHead d2 (Bind Abbr) u)))) (\lambda (_: C).(\lambda (u: 
T).(ty3 g d1 u t))) (\lambda (d2: C).(\lambda (u: T).(ty3 g d2 u t))))) 
(\lambda (x0: C).(\lambda (x1: T).(\lambda (H6: (csubt g d1 x0)).(\lambda 
(H7: (drop n0 O c3 (CHead x0 (Bind Abbr) x1))).(\lambda (H8: (ty3 g d1 x1 
t)).(\lambda (H9: (ty3 g x0 x1 t)).(or_intror (ex2 C (\lambda (d2: C).(csubt 
g d1 d2)) (\lambda (d2: C).(drop (S n0) O (CHead c3 (Bind b) u2) (CHead d2 
(Bind Abst) t)))) (ex4_2 C T (\lambda (d2: C).(\lambda (_: T).(csubt g d1 
d2))) (\lambda (d2: C).(\lambda (u: T).(drop (S n0) O (CHead c3 (Bind b) u2) 
(CHead d2 (Bind Abbr) u)))) (\lambda (_: C).(\lambda (u: T).(ty3 g d1 u t))) 
(\lambda (d2: C).(\lambda (u: T).(ty3 g d2 u t)))) (ex4_2_intro C T (\lambda 
(d2: C).(\lambda (_: T).(csubt g d1 d2))) (\lambda (d2: C).(\lambda (u: 
T).(drop (S n0) O (CHead c3 (Bind b) u2) (CHead d2 (Bind Abbr) u)))) (\lambda 
(_: C).(\lambda (u: T).(ty3 g d1 u t))) (\lambda (d2: C).(\lambda (u: T).(ty3 
g d2 u t))) x0 x1 H6 (drop_drop (Bind b) n0 c3 (CHead x0 (Bind Abbr) x1) H7 
u2) H8 H9)))))))) H5)) (H c0 c3 H1 d1 t (drop_gen_drop (Bind Void) c0 (CHead 
d1 (Bind Abst) t) u1 n0 H4)))))))))))))) (\lambda (c0: C).(\lambda (c3: 
C).(\lambda (H1: (csubt g c0 c3)).(\lambda (_: ((\forall (d1: C).(\forall (t: 
T).((drop (S n0) O c0 (CHead d1 (Bind Abst) t)) \to (or (ex2 C (\lambda (d2: 
C).(csubt g d1 d2)) (\lambda (d2: C).(drop (S n0) O c3 (CHead d2 (Bind Abst) 
t)))) (ex4_2 C T (\lambda (d2: C).(\lambda (_: T).(csubt g d1 d2))) (\lambda 
(d2: C).(\lambda (u: T).(drop (S n0) O c3 (CHead d2 (Bind Abbr) u)))) 
(\lambda (_: C).(\lambda (u: T).(ty3 g d1 u t))) (\lambda (d2: C).(\lambda 
(u: T).(ty3 g d2 u t)))))))))).(\lambda (u: T).(\lambda (t: T).(\lambda (_: 
(ty3 g c0 u t)).(\lambda (_: (ty3 g c3 u t)).(\lambda (d1: C).(\lambda (t0: 
T).(\lambda (H5: (drop (S n0) O (CHead c0 (Bind Abst) t) (CHead d1 (Bind 
Abst) t0))).(or_ind (ex2 C (\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: 
C).(drop n0 O c3 (CHead d2 (Bind Abst) t0)))) (ex4_2 C T (\lambda (d2: 
C).(\lambda (_: T).(csubt g d1 d2))) (\lambda (d2: C).(\lambda (u0: T).(drop 
n0 O c3 (CHead d2 (Bind Abbr) u0)))) (\lambda (_: C).(\lambda (u0: T).(ty3 g 
d1 u0 t0))) (\lambda (d2: C).(\lambda (u0: T).(ty3 g d2 u0 t0)))) (or (ex2 C 
(\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: C).(drop (S n0) O (CHead c3 
(Bind Abbr) u) (CHead d2 (Bind Abst) t0)))) (ex4_2 C T (\lambda (d2: 
C).(\lambda (_: T).(csubt g d1 d2))) (\lambda (d2: C).(\lambda (u0: T).(drop 
(S n0) O (CHead c3 (Bind Abbr) u) (CHead d2 (Bind Abbr) u0)))) (\lambda (_: 
C).(\lambda (u0: T).(ty3 g d1 u0 t0))) (\lambda (d2: C).(\lambda (u0: T).(ty3 
g d2 u0 t0))))) (\lambda (H6: (ex2 C (\lambda (d2: C).(csubt g d1 d2)) 
(\lambda (d2: C).(drop n0 O c3 (CHead d2 (Bind Abst) t0))))).(ex2_ind C 
(\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: C).(drop n0 O c3 (CHead d2 
(Bind Abst) t0))) (or (ex2 C (\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: 
C).(drop (S n0) O (CHead c3 (Bind Abbr) u) (CHead d2 (Bind Abst) t0)))) 
(ex4_2 C T (\lambda (d2: C).(\lambda (_: T).(csubt g d1 d2))) (\lambda (d2: 
C).(\lambda (u0: T).(drop (S n0) O (CHead c3 (Bind Abbr) u) (CHead d2 (Bind 
Abbr) u0)))) (\lambda (_: C).(\lambda (u0: T).(ty3 g d1 u0 t0))) (\lambda 
(d2: C).(\lambda (u0: T).(ty3 g d2 u0 t0))))) (\lambda (x: C).(\lambda (H7: 
(csubt g d1 x)).(\lambda (H8: (drop n0 O c3 (CHead x (Bind Abst) 
t0))).(or_introl (ex2 C (\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: 
C).(drop (S n0) O (CHead c3 (Bind Abbr) u) (CHead d2 (Bind Abst) t0)))) 
(ex4_2 C T (\lambda (d2: C).(\lambda (_: T).(csubt g d1 d2))) (\lambda (d2: 
C).(\lambda (u0: T).(drop (S n0) O (CHead c3 (Bind Abbr) u) (CHead d2 (Bind 
Abbr) u0)))) (\lambda (_: C).(\lambda (u0: T).(ty3 g d1 u0 t0))) (\lambda 
(d2: C).(\lambda (u0: T).(ty3 g d2 u0 t0)))) (ex_intro2 C (\lambda (d2: 
C).(csubt g d1 d2)) (\lambda (d2: C).(drop (S n0) O (CHead c3 (Bind Abbr) u) 
(CHead d2 (Bind Abst) t0))) x H7 (drop_drop (Bind Abbr) n0 c3 (CHead x (Bind 
Abst) t0) H8 u)))))) H6)) (\lambda (H6: (ex4_2 C T (\lambda (d2: C).(\lambda 
(_: T).(csubt g d1 d2))) (\lambda (d2: C).(\lambda (u0: T).(drop n0 O c3 
(CHead d2 (Bind Abbr) u0)))) (\lambda (_: C).(\lambda (u0: T).(ty3 g d1 u0 
t0))) (\lambda (d2: C).(\lambda (u0: T).(ty3 g d2 u0 t0))))).(ex4_2_ind C T 
(\lambda (d2: C).(\lambda (_: T).(csubt g d1 d2))) (\lambda (d2: C).(\lambda 
(u0: T).(drop n0 O c3 (CHead d2 (Bind Abbr) u0)))) (\lambda (_: C).(\lambda 
(u0: T).(ty3 g d1 u0 t0))) (\lambda (d2: C).(\lambda (u0: T).(ty3 g d2 u0 
t0))) (or (ex2 C (\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: C).(drop (S 
n0) O (CHead c3 (Bind Abbr) u) (CHead d2 (Bind Abst) t0)))) (ex4_2 C T 
(\lambda (d2: C).(\lambda (_: T).(csubt g d1 d2))) (\lambda (d2: C).(\lambda 
(u0: T).(drop (S n0) O (CHead c3 (Bind Abbr) u) (CHead d2 (Bind Abbr) u0)))) 
(\lambda (_: C).(\lambda (u0: T).(ty3 g d1 u0 t0))) (\lambda (d2: C).(\lambda 
(u0: T).(ty3 g d2 u0 t0))))) (\lambda (x0: C).(\lambda (x1: T).(\lambda (H7: 
(csubt g d1 x0)).(\lambda (H8: (drop n0 O c3 (CHead x0 (Bind Abbr) 
x1))).(\lambda (H9: (ty3 g d1 x1 t0)).(\lambda (H10: (ty3 g x0 x1 
t0)).(or_intror (ex2 C (\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: 
C).(drop (S n0) O (CHead c3 (Bind Abbr) u) (CHead d2 (Bind Abst) t0)))) 
(ex4_2 C T (\lambda (d2: C).(\lambda (_: T).(csubt g d1 d2))) (\lambda (d2: 
C).(\lambda (u0: T).(drop (S n0) O (CHead c3 (Bind Abbr) u) (CHead d2 (Bind 
Abbr) u0)))) (\lambda (_: C).(\lambda (u0: T).(ty3 g d1 u0 t0))) (\lambda 
(d2: C).(\lambda (u0: T).(ty3 g d2 u0 t0)))) (ex4_2_intro C T (\lambda (d2: 
C).(\lambda (_: T).(csubt g d1 d2))) (\lambda (d2: C).(\lambda (u0: T).(drop 
(S n0) O (CHead c3 (Bind Abbr) u) (CHead d2 (Bind Abbr) u0)))) (\lambda (_: 
C).(\lambda (u0: T).(ty3 g d1 u0 t0))) (\lambda (d2: C).(\lambda (u0: T).(ty3 
g d2 u0 t0))) x0 x1 H7 (drop_drop (Bind Abbr) n0 c3 (CHead x0 (Bind Abbr) x1) 
H8 u) H9 H10)))))))) H6)) (H c0 c3 H1 d1 t0 (drop_gen_drop (Bind Abst) c0 
(CHead d1 (Bind Abst) t0) t n0 H5)))))))))))))) c1 c2 H0)))))) n)).
(* COMMENTS
Initial nodes: 7940
END *)

