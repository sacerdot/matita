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

set "baseuri" "cic:/matita/LAMBDA-TYPES/Level-1/LambdaDelta/csubt/drop".

include "csubt/defs.ma".

include "drop/fwd.ma".

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
(CHead d1 (Flat f) u) (drop_gen_refl c1 (CHead d1 (Flat f) u) H0)) in (let H2 
\def (match H1 in csubt return (\lambda (c: C).(\lambda (c0: C).(\lambda (_: 
(csubt ? c c0)).((eq C c (CHead d1 (Flat f) u)) \to ((eq C c0 c2) \to (ex2 C 
(\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: C).(drop O O c2 (CHead d2 
(Flat f) u))))))))) with [(csubt_sort n0) \Rightarrow (\lambda (H2: (eq C 
(CSort n0) (CHead d1 (Flat f) u))).(\lambda (H3: (eq C (CSort n0) c2)).((let 
H4 \def (eq_ind C (CSort n0) (\lambda (e: C).(match e in C return (\lambda 
(_: C).Prop) with [(CSort _) \Rightarrow True | (CHead _ _ _) \Rightarrow 
False])) I (CHead d1 (Flat f) u) H2) in (False_ind ((eq C (CSort n0) c2) \to 
(ex2 C (\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: C).(drop O O c2 (CHead 
d2 (Flat f) u))))) H4)) H3))) | (csubt_head c0 c3 H2 k u0) \Rightarrow 
(\lambda (H3: (eq C (CHead c0 k u0) (CHead d1 (Flat f) u))).(\lambda (H4: (eq 
C (CHead c3 k u0) c2)).((let H5 \def (f_equal C T (\lambda (e: C).(match e in 
C return (\lambda (_: C).T) with [(CSort _) \Rightarrow u0 | (CHead _ _ t) 
\Rightarrow t])) (CHead c0 k u0) (CHead d1 (Flat f) u) H3) in ((let H6 \def 
(f_equal C K (\lambda (e: C).(match e in C return (\lambda (_: C).K) with 
[(CSort _) \Rightarrow k | (CHead _ k0 _) \Rightarrow k0])) (CHead c0 k u0) 
(CHead d1 (Flat f) u) H3) in ((let H7 \def (f_equal C C (\lambda (e: 
C).(match e in C return (\lambda (_: C).C) with [(CSort _) \Rightarrow c0 | 
(CHead c _ _) \Rightarrow c])) (CHead c0 k u0) (CHead d1 (Flat f) u) H3) in 
(eq_ind C d1 (\lambda (c: C).((eq K k (Flat f)) \to ((eq T u0 u) \to ((eq C 
(CHead c3 k u0) c2) \to ((csubt g c c3) \to (ex2 C (\lambda (d2: C).(csubt g 
d1 d2)) (\lambda (d2: C).(drop O O c2 (CHead d2 (Flat f) u))))))))) (\lambda 
(H8: (eq K k (Flat f))).(eq_ind K (Flat f) (\lambda (k0: K).((eq T u0 u) \to 
((eq C (CHead c3 k0 u0) c2) \to ((csubt g d1 c3) \to (ex2 C (\lambda (d2: 
C).(csubt g d1 d2)) (\lambda (d2: C).(drop O O c2 (CHead d2 (Flat f) 
u)))))))) (\lambda (H9: (eq T u0 u)).(eq_ind T u (\lambda (t: T).((eq C 
(CHead c3 (Flat f) t) c2) \to ((csubt g d1 c3) \to (ex2 C (\lambda (d2: 
C).(csubt g d1 d2)) (\lambda (d2: C).(drop O O c2 (CHead d2 (Flat f) u))))))) 
(\lambda (H10: (eq C (CHead c3 (Flat f) u) c2)).(eq_ind C (CHead c3 (Flat f) 
u) (\lambda (c: C).((csubt g d1 c3) \to (ex2 C (\lambda (d2: C).(csubt g d1 
d2)) (\lambda (d2: C).(drop O O c (CHead d2 (Flat f) u)))))) (\lambda (H11: 
(csubt g d1 c3)).(ex_intro2 C (\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: 
C).(drop O O (CHead c3 (Flat f) u) (CHead d2 (Flat f) u))) c3 H11 (drop_refl 
(CHead c3 (Flat f) u)))) c2 H10)) u0 (sym_eq T u0 u H9))) k (sym_eq K k (Flat 
f) H8))) c0 (sym_eq C c0 d1 H7))) H6)) H5)) H4 H2))) | (csubt_void c0 c3 H2 b 
H3 u1 u2) \Rightarrow (\lambda (H4: (eq C (CHead c0 (Bind Void) u1) (CHead d1 
(Flat f) u))).(\lambda (H5: (eq C (CHead c3 (Bind b) u2) c2)).((let H6 \def 
(eq_ind C (CHead c0 (Bind Void) u1) (\lambda (e: C).(match e in C return 
(\lambda (_: C).Prop) with [(CSort _) \Rightarrow False | (CHead _ k _) 
\Rightarrow (match k in K return (\lambda (_: K).Prop) with [(Bind _) 
\Rightarrow True | (Flat _) \Rightarrow False])])) I (CHead d1 (Flat f) u) 
H4) in (False_ind ((eq C (CHead c3 (Bind b) u2) c2) \to ((csubt g c0 c3) \to 
((not (eq B b Void)) \to (ex2 C (\lambda (d2: C).(csubt g d1 d2)) (\lambda 
(d2: C).(drop O O c2 (CHead d2 (Flat f) u))))))) H6)) H5 H2 H3))) | 
(csubt_abst c0 c3 H2 u0 t H3) \Rightarrow (\lambda (H4: (eq C (CHead c0 (Bind 
Abst) t) (CHead d1 (Flat f) u))).(\lambda (H5: (eq C (CHead c3 (Bind Abbr) 
u0) c2)).((let H6 \def (eq_ind C (CHead c0 (Bind Abst) t) (\lambda (e: 
C).(match e in C return (\lambda (_: C).Prop) with [(CSort _) \Rightarrow 
False | (CHead _ k _) \Rightarrow (match k in K return (\lambda (_: K).Prop) 
with [(Bind _) \Rightarrow True | (Flat _) \Rightarrow False])])) I (CHead d1 
(Flat f) u) H4) in (False_ind ((eq C (CHead c3 (Bind Abbr) u0) c2) \to 
((csubt g c0 c3) \to ((ty3 g c3 u0 t) \to (ex2 C (\lambda (d2: C).(csubt g d1 
d2)) (\lambda (d2: C).(drop O O c2 (CHead d2 (Flat f) u))))))) H6)) H5 H2 
H3)))]) in (H2 (refl_equal C (CHead d1 (Flat f) u)) (refl_equal C 
c2)))))))))) (\lambda (n0: nat).(\lambda (H: ((\forall (c1: C).(\forall (c2: 
C).((csubt g c1 c2) \to (\forall (d1: C).(\forall (u: T).((drop n0 O c1 
(CHead d1 (Flat f) u)) \to (ex2 C (\lambda (d2: C).(csubt g d1 d2)) (\lambda 
(d2: C).(drop n0 O c2 (CHead d2 (Flat f) u)))))))))))).(\lambda (c1: 
C).(\lambda (c2: C).(\lambda (H0: (csubt g c1 c2)).(csubt_ind g (\lambda (c: 
C).(\lambda (c0: C).(\forall (d1: C).(\forall (u: T).((drop (S n0) O c (CHead 
d1 (Flat f) u)) \to (ex2 C (\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: 
C).(drop (S n0) O c0 (CHead d2 (Flat f) u))))))))) (\lambda (n1: 
nat).(\lambda (d1: C).(\lambda (u: T).(\lambda (H1: (drop (S n0) O (CSort n1) 
(CHead d1 (Flat f) u))).(let H2 \def (match H1 in drop return (\lambda (n2: 
nat).(\lambda (n3: nat).(\lambda (c: C).(\lambda (c0: C).(\lambda (_: (drop 
n2 n3 c c0)).((eq nat n2 (S n0)) \to ((eq nat n3 O) \to ((eq C c (CSort n1)) 
\to ((eq C c0 (CHead d1 (Flat f) u)) \to (ex2 C (\lambda (d2: C).(csubt g d1 
d2)) (\lambda (d2: C).(drop (S n0) O (CSort n1) (CHead d2 (Flat f) 
u))))))))))))) with [(drop_refl c) \Rightarrow (\lambda (H2: (eq nat O (S 
n0))).(\lambda (H3: (eq nat O O)).(\lambda (H4: (eq C c (CSort n1))).(\lambda 
(H5: (eq C c (CHead d1 (Flat f) u))).((let H6 \def (eq_ind nat O (\lambda (e: 
nat).(match e in nat return (\lambda (_: nat).Prop) with [O \Rightarrow True 
| (S _) \Rightarrow False])) I (S n0) H2) in (False_ind ((eq nat O O) \to 
((eq C c (CSort n1)) \to ((eq C c (CHead d1 (Flat f) u)) \to (ex2 C (\lambda 
(d2: C).(csubt g d1 d2)) (\lambda (d2: C).(drop (S n0) O (CSort n1) (CHead d2 
(Flat f) u))))))) H6)) H3 H4 H5))))) | (drop_drop k h c e H2 u0) \Rightarrow 
(\lambda (H3: (eq nat (S h) (S n0))).(\lambda (H4: (eq nat O O)).(\lambda 
(H5: (eq C (CHead c k u0) (CSort n1))).(\lambda (H6: (eq C e (CHead d1 (Flat 
f) u))).((let H7 \def (f_equal nat nat (\lambda (e0: nat).(match e0 in nat 
return (\lambda (_: nat).nat) with [O \Rightarrow h | (S n2) \Rightarrow 
n2])) (S h) (S n0) H3) in (eq_ind nat n0 (\lambda (n2: nat).((eq nat O O) \to 
((eq C (CHead c k u0) (CSort n1)) \to ((eq C e (CHead d1 (Flat f) u)) \to 
((drop (r k n2) O c e) \to (ex2 C (\lambda (d2: C).(csubt g d1 d2)) (\lambda 
(d2: C).(drop (S n0) O (CSort n1) (CHead d2 (Flat f) u))))))))) (\lambda (_: 
(eq nat O O)).(\lambda (H9: (eq C (CHead c k u0) (CSort n1))).(let H10 \def 
(eq_ind C (CHead c k u0) (\lambda (e0: C).(match e0 in C return (\lambda (_: 
C).Prop) with [(CSort _) \Rightarrow False | (CHead _ _ _) \Rightarrow 
True])) I (CSort n1) H9) in (False_ind ((eq C e (CHead d1 (Flat f) u)) \to 
((drop (r k n0) O c e) \to (ex2 C (\lambda (d2: C).(csubt g d1 d2)) (\lambda 
(d2: C).(drop (S n0) O (CSort n1) (CHead d2 (Flat f) u)))))) H10)))) h 
(sym_eq nat h n0 H7))) H4 H5 H6 H2))))) | (drop_skip k h d c e H2 u0) 
\Rightarrow (\lambda (H3: (eq nat h (S n0))).(\lambda (H4: (eq nat (S d) 
O)).(\lambda (H5: (eq C (CHead c k (lift h (r k d) u0)) (CSort n1))).(\lambda 
(H6: (eq C (CHead e k u0) (CHead d1 (Flat f) u))).(eq_ind nat (S n0) (\lambda 
(n2: nat).((eq nat (S d) O) \to ((eq C (CHead c k (lift n2 (r k d) u0)) 
(CSort n1)) \to ((eq C (CHead e k u0) (CHead d1 (Flat f) u)) \to ((drop n2 (r 
k d) c e) \to (ex2 C (\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: C).(drop 
(S n0) O (CSort n1) (CHead d2 (Flat f) u))))))))) (\lambda (H7: (eq nat (S d) 
O)).(let H8 \def (eq_ind nat (S d) (\lambda (e0: nat).(match e0 in nat return 
(\lambda (_: nat).Prop) with [O \Rightarrow False | (S _) \Rightarrow True])) 
I O H7) in (False_ind ((eq C (CHead c k (lift (S n0) (r k d) u0)) (CSort n1)) 
\to ((eq C (CHead e k u0) (CHead d1 (Flat f) u)) \to ((drop (S n0) (r k d) c 
e) \to (ex2 C (\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: C).(drop (S n0) 
O (CSort n1) (CHead d2 (Flat f) u))))))) H8))) h (sym_eq nat h (S n0) H3) H4 
H5 H6 H2)))))]) in (H2 (refl_equal nat (S n0)) (refl_equal nat O) (refl_equal 
C (CSort n1)) (refl_equal C (CHead d1 (Flat f) u)))))))) (\lambda (c0: 
C).(\lambda (c3: C).(\lambda (H1: (csubt g c0 c3)).(\lambda (H2: ((\forall 
(d1: C).(\forall (u: T).((drop (S n0) O c0 (CHead d1 (Flat f) u)) \to (ex2 C 
(\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: C).(drop (S n0) O c3 (CHead 
d2 (Flat f) u))))))))).(\lambda (k: K).(K_ind (\lambda (k0: K).(\forall (u: 
T).(\forall (d1: C).(\forall (u0: T).((drop (S n0) O (CHead c0 k0 u) (CHead 
d1 (Flat f) u0)) \to (ex2 C (\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: 
C).(drop (S n0) O (CHead c3 k0 u) (CHead d2 (Flat f) u0))))))))) (\lambda (b: 
B).(\lambda (u: T).(\lambda (d1: C).(\lambda (u0: T).(\lambda (H3: (drop (S 
n0) O (CHead c0 (Bind b) u) (CHead d1 (Flat f) u0))).(ex2_ind C (\lambda (d2: 
C).(csubt g d1 d2)) (\lambda (d2: C).(drop n0 O c3 (CHead d2 (Flat f) u0))) 
(ex2 C (\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: C).(drop (S n0) O 
(CHead c3 (Bind b) u) (CHead d2 (Flat f) u0)))) (\lambda (x: C).(\lambda (H4: 
(csubt g d1 x)).(\lambda (H5: (drop n0 O c3 (CHead x (Flat f) 
u0))).(ex_intro2 C (\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: C).(drop 
(S n0) O (CHead c3 (Bind b) u) (CHead d2 (Flat f) u0))) x H4 (drop_drop (Bind 
b) n0 c3 (CHead x (Flat f) u0) H5 u))))) (H c0 c3 H1 d1 u0 (drop_gen_drop 
(Bind b) c0 (CHead d1 (Flat f) u0) u n0 H3)))))))) (\lambda (f0: F).(\lambda 
(u: T).(\lambda (d1: C).(\lambda (u0: T).(\lambda (H3: (drop (S n0) O (CHead 
c0 (Flat f0) u) (CHead d1 (Flat f) u0))).(ex2_ind C (\lambda (d2: C).(csubt g 
d1 d2)) (\lambda (d2: C).(drop (S n0) O c3 (CHead d2 (Flat f) u0))) (ex2 C 
(\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: C).(drop (S n0) O (CHead c3 
(Flat f0) u) (CHead d2 (Flat f) u0)))) (\lambda (x: C).(\lambda (H4: (csubt g 
d1 x)).(\lambda (H5: (drop (S n0) O c3 (CHead x (Flat f) u0))).(ex_intro2 C 
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
u))))))))).(\lambda (u: T).(\lambda (t: T).(\lambda (_: (ty3 g c3 u 
t)).(\lambda (d1: C).(\lambda (u0: T).(\lambda (H4: (drop (S n0) O (CHead c0 
(Bind Abst) t) (CHead d1 (Flat f) u0))).(ex2_ind C (\lambda (d2: C).(csubt g 
d1 d2)) (\lambda (d2: C).(drop n0 O c3 (CHead d2 (Flat f) u0))) (ex2 C 
(\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: C).(drop (S n0) O (CHead c3 
(Bind Abbr) u) (CHead d2 (Flat f) u0)))) (\lambda (x: C).(\lambda (H5: (csubt 
g d1 x)).(\lambda (H6: (drop n0 O c3 (CHead x (Flat f) u0))).(ex_intro2 C 
(\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: C).(drop (S n0) O (CHead c3 
(Bind Abbr) u) (CHead d2 (Flat f) u0))) x H5 (drop_drop (Bind Abbr) n0 c3 
(CHead x (Flat f) u0) H6 u))))) (H c0 c3 H1 d1 u0 (drop_gen_drop (Bind Abst) 
c0 (CHead d1 (Flat f) u0) t n0 H4))))))))))))) c1 c2 H0)))))) n))).

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
(let H2 \def (match H1 in csubt return (\lambda (c: C).(\lambda (c0: 
C).(\lambda (_: (csubt ? c c0)).((eq C c (CHead d1 (Bind Abbr) u)) \to ((eq C 
c0 c2) \to (ex2 C (\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: C).(drop O 
O c2 (CHead d2 (Bind Abbr) u))))))))) with [(csubt_sort n0) \Rightarrow 
(\lambda (H2: (eq C (CSort n0) (CHead d1 (Bind Abbr) u))).(\lambda (H3: (eq C 
(CSort n0) c2)).((let H4 \def (eq_ind C (CSort n0) (\lambda (e: C).(match e 
in C return (\lambda (_: C).Prop) with [(CSort _) \Rightarrow True | (CHead _ 
_ _) \Rightarrow False])) I (CHead d1 (Bind Abbr) u) H2) in (False_ind ((eq C 
(CSort n0) c2) \to (ex2 C (\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: 
C).(drop O O c2 (CHead d2 (Bind Abbr) u))))) H4)) H3))) | (csubt_head c0 c3 
H2 k u0) \Rightarrow (\lambda (H3: (eq C (CHead c0 k u0) (CHead d1 (Bind 
Abbr) u))).(\lambda (H4: (eq C (CHead c3 k u0) c2)).((let H5 \def (f_equal C 
T (\lambda (e: C).(match e in C return (\lambda (_: C).T) with [(CSort _) 
\Rightarrow u0 | (CHead _ _ t) \Rightarrow t])) (CHead c0 k u0) (CHead d1 
(Bind Abbr) u) H3) in ((let H6 \def (f_equal C K (\lambda (e: C).(match e in 
C return (\lambda (_: C).K) with [(CSort _) \Rightarrow k | (CHead _ k0 _) 
\Rightarrow k0])) (CHead c0 k u0) (CHead d1 (Bind Abbr) u) H3) in ((let H7 
\def (f_equal C C (\lambda (e: C).(match e in C return (\lambda (_: C).C) 
with [(CSort _) \Rightarrow c0 | (CHead c _ _) \Rightarrow c])) (CHead c0 k 
u0) (CHead d1 (Bind Abbr) u) H3) in (eq_ind C d1 (\lambda (c: C).((eq K k 
(Bind Abbr)) \to ((eq T u0 u) \to ((eq C (CHead c3 k u0) c2) \to ((csubt g c 
c3) \to (ex2 C (\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: C).(drop O O 
c2 (CHead d2 (Bind Abbr) u))))))))) (\lambda (H8: (eq K k (Bind 
Abbr))).(eq_ind K (Bind Abbr) (\lambda (k0: K).((eq T u0 u) \to ((eq C (CHead 
c3 k0 u0) c2) \to ((csubt g d1 c3) \to (ex2 C (\lambda (d2: C).(csubt g d1 
d2)) (\lambda (d2: C).(drop O O c2 (CHead d2 (Bind Abbr) u)))))))) (\lambda 
(H9: (eq T u0 u)).(eq_ind T u (\lambda (t: T).((eq C (CHead c3 (Bind Abbr) t) 
c2) \to ((csubt g d1 c3) \to (ex2 C (\lambda (d2: C).(csubt g d1 d2)) 
(\lambda (d2: C).(drop O O c2 (CHead d2 (Bind Abbr) u))))))) (\lambda (H10: 
(eq C (CHead c3 (Bind Abbr) u) c2)).(eq_ind C (CHead c3 (Bind Abbr) u) 
(\lambda (c: C).((csubt g d1 c3) \to (ex2 C (\lambda (d2: C).(csubt g d1 d2)) 
(\lambda (d2: C).(drop O O c (CHead d2 (Bind Abbr) u)))))) (\lambda (H11: 
(csubt g d1 c3)).(ex_intro2 C (\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: 
C).(drop O O (CHead c3 (Bind Abbr) u) (CHead d2 (Bind Abbr) u))) c3 H11 
(drop_refl (CHead c3 (Bind Abbr) u)))) c2 H10)) u0 (sym_eq T u0 u H9))) k 
(sym_eq K k (Bind Abbr) H8))) c0 (sym_eq C c0 d1 H7))) H6)) H5)) H4 H2))) | 
(csubt_void c0 c3 H2 b H3 u1 u2) \Rightarrow (\lambda (H4: (eq C (CHead c0 
(Bind Void) u1) (CHead d1 (Bind Abbr) u))).(\lambda (H5: (eq C (CHead c3 
(Bind b) u2) c2)).((let H6 \def (eq_ind C (CHead c0 (Bind Void) u1) (\lambda 
(e: C).(match e in C return (\lambda (_: C).Prop) with [(CSort _) \Rightarrow 
False | (CHead _ k _) \Rightarrow (match k in K return (\lambda (_: K).Prop) 
with [(Bind b0) \Rightarrow (match b0 in B return (\lambda (_: B).Prop) with 
[Abbr \Rightarrow False | Abst \Rightarrow False | Void \Rightarrow True]) | 
(Flat _) \Rightarrow False])])) I (CHead d1 (Bind Abbr) u) H4) in (False_ind 
((eq C (CHead c3 (Bind b) u2) c2) \to ((csubt g c0 c3) \to ((not (eq B b 
Void)) \to (ex2 C (\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: C).(drop O 
O c2 (CHead d2 (Bind Abbr) u))))))) H6)) H5 H2 H3))) | (csubt_abst c0 c3 H2 
u0 t H3) \Rightarrow (\lambda (H4: (eq C (CHead c0 (Bind Abst) t) (CHead d1 
(Bind Abbr) u))).(\lambda (H5: (eq C (CHead c3 (Bind Abbr) u0) c2)).((let H6 
\def (eq_ind C (CHead c0 (Bind Abst) t) (\lambda (e: C).(match e in C return 
(\lambda (_: C).Prop) with [(CSort _) \Rightarrow False | (CHead _ k _) 
\Rightarrow (match k in K return (\lambda (_: K).Prop) with [(Bind b) 
\Rightarrow (match b in B return (\lambda (_: B).Prop) with [Abbr \Rightarrow 
False | Abst \Rightarrow True | Void \Rightarrow False]) | (Flat _) 
\Rightarrow False])])) I (CHead d1 (Bind Abbr) u) H4) in (False_ind ((eq C 
(CHead c3 (Bind Abbr) u0) c2) \to ((csubt g c0 c3) \to ((ty3 g c3 u0 t) \to 
(ex2 C (\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: C).(drop O O c2 (CHead 
d2 (Bind Abbr) u))))))) H6)) H5 H2 H3)))]) in (H2 (refl_equal C (CHead d1 
(Bind Abbr) u)) (refl_equal C c2)))))))))) (\lambda (n0: nat).(\lambda (H: 
((\forall (c1: C).(\forall (c2: C).((csubt g c1 c2) \to (\forall (d1: 
C).(\forall (u: T).((drop n0 O c1 (CHead d1 (Bind Abbr) u)) \to (ex2 C 
(\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: C).(drop n0 O c2 (CHead d2 
(Bind Abbr) u)))))))))))).(\lambda (c1: C).(\lambda (c2: C).(\lambda (H0: 
(csubt g c1 c2)).(csubt_ind g (\lambda (c: C).(\lambda (c0: C).(\forall (d1: 
C).(\forall (u: T).((drop (S n0) O c (CHead d1 (Bind Abbr) u)) \to (ex2 C 
(\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: C).(drop (S n0) O c0 (CHead 
d2 (Bind Abbr) u))))))))) (\lambda (n1: nat).(\lambda (d1: C).(\lambda (u: 
T).(\lambda (H1: (drop (S n0) O (CSort n1) (CHead d1 (Bind Abbr) u))).(let H2 
\def (match H1 in drop return (\lambda (n2: nat).(\lambda (n3: nat).(\lambda 
(c: C).(\lambda (c0: C).(\lambda (_: (drop n2 n3 c c0)).((eq nat n2 (S n0)) 
\to ((eq nat n3 O) \to ((eq C c (CSort n1)) \to ((eq C c0 (CHead d1 (Bind 
Abbr) u)) \to (ex2 C (\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: C).(drop 
(S n0) O (CSort n1) (CHead d2 (Bind Abbr) u))))))))))))) with [(drop_refl c) 
\Rightarrow (\lambda (H2: (eq nat O (S n0))).(\lambda (H3: (eq nat O 
O)).(\lambda (H4: (eq C c (CSort n1))).(\lambda (H5: (eq C c (CHead d1 (Bind 
Abbr) u))).((let H6 \def (eq_ind nat O (\lambda (e: nat).(match e in nat 
return (\lambda (_: nat).Prop) with [O \Rightarrow True | (S _) \Rightarrow 
False])) I (S n0) H2) in (False_ind ((eq nat O O) \to ((eq C c (CSort n1)) 
\to ((eq C c (CHead d1 (Bind Abbr) u)) \to (ex2 C (\lambda (d2: C).(csubt g 
d1 d2)) (\lambda (d2: C).(drop (S n0) O (CSort n1) (CHead d2 (Bind Abbr) 
u))))))) H6)) H3 H4 H5))))) | (drop_drop k h c e H2 u0) \Rightarrow (\lambda 
(H3: (eq nat (S h) (S n0))).(\lambda (H4: (eq nat O O)).(\lambda (H5: (eq C 
(CHead c k u0) (CSort n1))).(\lambda (H6: (eq C e (CHead d1 (Bind Abbr) 
u))).((let H7 \def (f_equal nat nat (\lambda (e0: nat).(match e0 in nat 
return (\lambda (_: nat).nat) with [O \Rightarrow h | (S n2) \Rightarrow 
n2])) (S h) (S n0) H3) in (eq_ind nat n0 (\lambda (n2: nat).((eq nat O O) \to 
((eq C (CHead c k u0) (CSort n1)) \to ((eq C e (CHead d1 (Bind Abbr) u)) \to 
((drop (r k n2) O c e) \to (ex2 C (\lambda (d2: C).(csubt g d1 d2)) (\lambda 
(d2: C).(drop (S n0) O (CSort n1) (CHead d2 (Bind Abbr) u))))))))) (\lambda 
(_: (eq nat O O)).(\lambda (H9: (eq C (CHead c k u0) (CSort n1))).(let H10 
\def (eq_ind C (CHead c k u0) (\lambda (e0: C).(match e0 in C return (\lambda 
(_: C).Prop) with [(CSort _) \Rightarrow False | (CHead _ _ _) \Rightarrow 
True])) I (CSort n1) H9) in (False_ind ((eq C e (CHead d1 (Bind Abbr) u)) \to 
((drop (r k n0) O c e) \to (ex2 C (\lambda (d2: C).(csubt g d1 d2)) (\lambda 
(d2: C).(drop (S n0) O (CSort n1) (CHead d2 (Bind Abbr) u)))))) H10)))) h 
(sym_eq nat h n0 H7))) H4 H5 H6 H2))))) | (drop_skip k h d c e H2 u0) 
\Rightarrow (\lambda (H3: (eq nat h (S n0))).(\lambda (H4: (eq nat (S d) 
O)).(\lambda (H5: (eq C (CHead c k (lift h (r k d) u0)) (CSort n1))).(\lambda 
(H6: (eq C (CHead e k u0) (CHead d1 (Bind Abbr) u))).(eq_ind nat (S n0) 
(\lambda (n2: nat).((eq nat (S d) O) \to ((eq C (CHead c k (lift n2 (r k d) 
u0)) (CSort n1)) \to ((eq C (CHead e k u0) (CHead d1 (Bind Abbr) u)) \to 
((drop n2 (r k d) c e) \to (ex2 C (\lambda (d2: C).(csubt g d1 d2)) (\lambda 
(d2: C).(drop (S n0) O (CSort n1) (CHead d2 (Bind Abbr) u))))))))) (\lambda 
(H7: (eq nat (S d) O)).(let H8 \def (eq_ind nat (S d) (\lambda (e0: 
nat).(match e0 in nat return (\lambda (_: nat).Prop) with [O \Rightarrow 
False | (S _) \Rightarrow True])) I O H7) in (False_ind ((eq C (CHead c k 
(lift (S n0) (r k d) u0)) (CSort n1)) \to ((eq C (CHead e k u0) (CHead d1 
(Bind Abbr) u)) \to ((drop (S n0) (r k d) c e) \to (ex2 C (\lambda (d2: 
C).(csubt g d1 d2)) (\lambda (d2: C).(drop (S n0) O (CSort n1) (CHead d2 
(Bind Abbr) u))))))) H8))) h (sym_eq nat h (S n0) H3) H4 H5 H6 H2)))))]) in 
(H2 (refl_equal nat (S n0)) (refl_equal nat O) (refl_equal C (CSort n1)) 
(refl_equal C (CHead d1 (Bind Abbr) u)))))))) (\lambda (c0: C).(\lambda (c3: 
C).(\lambda (H1: (csubt g c0 c3)).(\lambda (H2: ((\forall (d1: C).(\forall 
(u: T).((drop (S n0) O c0 (CHead d1 (Bind Abbr) u)) \to (ex2 C (\lambda (d2: 
C).(csubt g d1 d2)) (\lambda (d2: C).(drop (S n0) O c3 (CHead d2 (Bind Abbr) 
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
c3 u t)).(\lambda (d1: C).(\lambda (u0: T).(\lambda (H4: (drop (S n0) O 
(CHead c0 (Bind Abst) t) (CHead d1 (Bind Abbr) u0))).(ex2_ind C (\lambda (d2: 
C).(csubt g d1 d2)) (\lambda (d2: C).(drop n0 O c3 (CHead d2 (Bind Abbr) 
u0))) (ex2 C (\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: C).(drop (S n0) 
O (CHead c3 (Bind Abbr) u) (CHead d2 (Bind Abbr) u0)))) (\lambda (x: 
C).(\lambda (H5: (csubt g d1 x)).(\lambda (H6: (drop n0 O c3 (CHead x (Bind 
Abbr) u0))).(ex_intro2 C (\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: 
C).(drop (S n0) O (CHead c3 (Bind Abbr) u) (CHead d2 (Bind Abbr) u0))) x H5 
(drop_drop (Bind Abbr) n0 c3 (CHead x (Bind Abbr) u0) H6 u))))) (H c0 c3 H1 
d1 u0 (drop_gen_drop (Bind Abst) c0 (CHead d1 (Bind Abbr) u0) t n0 
H4))))))))))))) c1 c2 H0)))))) n)).

theorem csubt_drop_abst:
 \forall (g: G).(\forall (n: nat).(\forall (c1: C).(\forall (c2: C).((csubt g 
c1 c2) \to (\forall (d1: C).(\forall (t: T).((drop n O c1 (CHead d1 (Bind 
Abst) t)) \to (or (ex2 C (\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: 
C).(drop n O c2 (CHead d2 (Bind Abst) t)))) (ex3_2 C T (\lambda (d2: 
C).(\lambda (_: T).(csubt g d1 d2))) (\lambda (d2: C).(\lambda (u: T).(drop n 
O c2 (CHead d2 (Bind Abbr) u)))) (\lambda (d2: C).(\lambda (u: T).(ty3 g d2 u 
t))))))))))))
\def
 \lambda (g: G).(\lambda (n: nat).(nat_ind (\lambda (n0: nat).(\forall (c1: 
C).(\forall (c2: C).((csubt g c1 c2) \to (\forall (d1: C).(\forall (t: 
T).((drop n0 O c1 (CHead d1 (Bind Abst) t)) \to (or (ex2 C (\lambda (d2: 
C).(csubt g d1 d2)) (\lambda (d2: C).(drop n0 O c2 (CHead d2 (Bind Abst) 
t)))) (ex3_2 C T (\lambda (d2: C).(\lambda (_: T).(csubt g d1 d2))) (\lambda 
(d2: C).(\lambda (u: T).(drop n0 O c2 (CHead d2 (Bind Abbr) u)))) (\lambda 
(d2: C).(\lambda (u: T).(ty3 g d2 u t)))))))))))) (\lambda (c1: C).(\lambda 
(c2: C).(\lambda (H: (csubt g c1 c2)).(\lambda (d1: C).(\lambda (t: 
T).(\lambda (H0: (drop O O c1 (CHead d1 (Bind Abst) t))).(let H1 \def (eq_ind 
C c1 (\lambda (c: C).(csubt g c c2)) H (CHead d1 (Bind Abst) t) 
(drop_gen_refl c1 (CHead d1 (Bind Abst) t) H0)) in (let H2 \def (match H1 in 
csubt return (\lambda (c: C).(\lambda (c0: C).(\lambda (_: (csubt ? c 
c0)).((eq C c (CHead d1 (Bind Abst) t)) \to ((eq C c0 c2) \to (or (ex2 C 
(\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: C).(drop O O c2 (CHead d2 
(Bind Abst) t)))) (ex3_2 C T (\lambda (d2: C).(\lambda (_: T).(csubt g d1 
d2))) (\lambda (d2: C).(\lambda (u: T).(drop O O c2 (CHead d2 (Bind Abbr) 
u)))) (\lambda (d2: C).(\lambda (u: T).(ty3 g d2 u t)))))))))) with 
[(csubt_sort n0) \Rightarrow (\lambda (H2: (eq C (CSort n0) (CHead d1 (Bind 
Abst) t))).(\lambda (H3: (eq C (CSort n0) c2)).((let H4 \def (eq_ind C (CSort 
n0) (\lambda (e: C).(match e in C return (\lambda (_: C).Prop) with [(CSort 
_) \Rightarrow True | (CHead _ _ _) \Rightarrow False])) I (CHead d1 (Bind 
Abst) t) H2) in (False_ind ((eq C (CSort n0) c2) \to (or (ex2 C (\lambda (d2: 
C).(csubt g d1 d2)) (\lambda (d2: C).(drop O O c2 (CHead d2 (Bind Abst) t)))) 
(ex3_2 C T (\lambda (d2: C).(\lambda (_: T).(csubt g d1 d2))) (\lambda (d2: 
C).(\lambda (u: T).(drop O O c2 (CHead d2 (Bind Abbr) u)))) (\lambda (d2: 
C).(\lambda (u: T).(ty3 g d2 u t)))))) H4)) H3))) | (csubt_head c0 c3 H2 k u) 
\Rightarrow (\lambda (H3: (eq C (CHead c0 k u) (CHead d1 (Bind Abst) 
t))).(\lambda (H4: (eq C (CHead c3 k u) c2)).((let H5 \def (f_equal C T 
(\lambda (e: C).(match e in C return (\lambda (_: C).T) with [(CSort _) 
\Rightarrow u | (CHead _ _ t0) \Rightarrow t0])) (CHead c0 k u) (CHead d1 
(Bind Abst) t) H3) in ((let H6 \def (f_equal C K (\lambda (e: C).(match e in 
C return (\lambda (_: C).K) with [(CSort _) \Rightarrow k | (CHead _ k0 _) 
\Rightarrow k0])) (CHead c0 k u) (CHead d1 (Bind Abst) t) H3) in ((let H7 
\def (f_equal C C (\lambda (e: C).(match e in C return (\lambda (_: C).C) 
with [(CSort _) \Rightarrow c0 | (CHead c _ _) \Rightarrow c])) (CHead c0 k 
u) (CHead d1 (Bind Abst) t) H3) in (eq_ind C d1 (\lambda (c: C).((eq K k 
(Bind Abst)) \to ((eq T u t) \to ((eq C (CHead c3 k u) c2) \to ((csubt g c 
c3) \to (or (ex2 C (\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: C).(drop O 
O c2 (CHead d2 (Bind Abst) t)))) (ex3_2 C T (\lambda (d2: C).(\lambda (_: 
T).(csubt g d1 d2))) (\lambda (d2: C).(\lambda (u0: T).(drop O O c2 (CHead d2 
(Bind Abbr) u0)))) (\lambda (d2: C).(\lambda (u0: T).(ty3 g d2 u0 t)))))))))) 
(\lambda (H8: (eq K k (Bind Abst))).(eq_ind K (Bind Abst) (\lambda (k0: 
K).((eq T u t) \to ((eq C (CHead c3 k0 u) c2) \to ((csubt g d1 c3) \to (or 
(ex2 C (\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: C).(drop O O c2 (CHead 
d2 (Bind Abst) t)))) (ex3_2 C T (\lambda (d2: C).(\lambda (_: T).(csubt g d1 
d2))) (\lambda (d2: C).(\lambda (u0: T).(drop O O c2 (CHead d2 (Bind Abbr) 
u0)))) (\lambda (d2: C).(\lambda (u0: T).(ty3 g d2 u0 t))))))))) (\lambda 
(H9: (eq T u t)).(eq_ind T t (\lambda (t0: T).((eq C (CHead c3 (Bind Abst) 
t0) c2) \to ((csubt g d1 c3) \to (or (ex2 C (\lambda (d2: C).(csubt g d1 d2)) 
(\lambda (d2: C).(drop O O c2 (CHead d2 (Bind Abst) t)))) (ex3_2 C T (\lambda 
(d2: C).(\lambda (_: T).(csubt g d1 d2))) (\lambda (d2: C).(\lambda (u0: 
T).(drop O O c2 (CHead d2 (Bind Abbr) u0)))) (\lambda (d2: C).(\lambda (u0: 
T).(ty3 g d2 u0 t)))))))) (\lambda (H10: (eq C (CHead c3 (Bind Abst) t) 
c2)).(eq_ind C (CHead c3 (Bind Abst) t) (\lambda (c: C).((csubt g d1 c3) \to 
(or (ex2 C (\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: C).(drop O O c 
(CHead d2 (Bind Abst) t)))) (ex3_2 C T (\lambda (d2: C).(\lambda (_: 
T).(csubt g d1 d2))) (\lambda (d2: C).(\lambda (u0: T).(drop O O c (CHead d2 
(Bind Abbr) u0)))) (\lambda (d2: C).(\lambda (u0: T).(ty3 g d2 u0 t))))))) 
(\lambda (H11: (csubt g d1 c3)).(or_introl (ex2 C (\lambda (d2: C).(csubt g 
d1 d2)) (\lambda (d2: C).(drop O O (CHead c3 (Bind Abst) t) (CHead d2 (Bind 
Abst) t)))) (ex3_2 C T (\lambda (d2: C).(\lambda (_: T).(csubt g d1 d2))) 
(\lambda (d2: C).(\lambda (u0: T).(drop O O (CHead c3 (Bind Abst) t) (CHead 
d2 (Bind Abbr) u0)))) (\lambda (d2: C).(\lambda (u0: T).(ty3 g d2 u0 t)))) 
(ex_intro2 C (\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: C).(drop O O 
(CHead c3 (Bind Abst) t) (CHead d2 (Bind Abst) t))) c3 H11 (drop_refl (CHead 
c3 (Bind Abst) t))))) c2 H10)) u (sym_eq T u t H9))) k (sym_eq K k (Bind 
Abst) H8))) c0 (sym_eq C c0 d1 H7))) H6)) H5)) H4 H2))) | (csubt_void c0 c3 
H2 b H3 u1 u2) \Rightarrow (\lambda (H4: (eq C (CHead c0 (Bind Void) u1) 
(CHead d1 (Bind Abst) t))).(\lambda (H5: (eq C (CHead c3 (Bind b) u2) 
c2)).((let H6 \def (eq_ind C (CHead c0 (Bind Void) u1) (\lambda (e: C).(match 
e in C return (\lambda (_: C).Prop) with [(CSort _) \Rightarrow False | 
(CHead _ k _) \Rightarrow (match k in K return (\lambda (_: K).Prop) with 
[(Bind b0) \Rightarrow (match b0 in B return (\lambda (_: B).Prop) with [Abbr 
\Rightarrow False | Abst \Rightarrow False | Void \Rightarrow True]) | (Flat 
_) \Rightarrow False])])) I (CHead d1 (Bind Abst) t) H4) in (False_ind ((eq C 
(CHead c3 (Bind b) u2) c2) \to ((csubt g c0 c3) \to ((not (eq B b Void)) \to 
(or (ex2 C (\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: C).(drop O O c2 
(CHead d2 (Bind Abst) t)))) (ex3_2 C T (\lambda (d2: C).(\lambda (_: 
T).(csubt g d1 d2))) (\lambda (d2: C).(\lambda (u: T).(drop O O c2 (CHead d2 
(Bind Abbr) u)))) (\lambda (d2: C).(\lambda (u: T).(ty3 g d2 u t)))))))) H6)) 
H5 H2 H3))) | (csubt_abst c0 c3 H2 u t0 H3) \Rightarrow (\lambda (H4: (eq C 
(CHead c0 (Bind Abst) t0) (CHead d1 (Bind Abst) t))).(\lambda (H5: (eq C 
(CHead c3 (Bind Abbr) u) c2)).((let H6 \def (f_equal C T (\lambda (e: 
C).(match e in C return (\lambda (_: C).T) with [(CSort _) \Rightarrow t0 | 
(CHead _ _ t1) \Rightarrow t1])) (CHead c0 (Bind Abst) t0) (CHead d1 (Bind 
Abst) t) H4) in ((let H7 \def (f_equal C C (\lambda (e: C).(match e in C 
return (\lambda (_: C).C) with [(CSort _) \Rightarrow c0 | (CHead c _ _) 
\Rightarrow c])) (CHead c0 (Bind Abst) t0) (CHead d1 (Bind Abst) t) H4) in 
(eq_ind C d1 (\lambda (c: C).((eq T t0 t) \to ((eq C (CHead c3 (Bind Abbr) u) 
c2) \to ((csubt g c c3) \to ((ty3 g c3 u t0) \to (or (ex2 C (\lambda (d2: 
C).(csubt g d1 d2)) (\lambda (d2: C).(drop O O c2 (CHead d2 (Bind Abst) t)))) 
(ex3_2 C T (\lambda (d2: C).(\lambda (_: T).(csubt g d1 d2))) (\lambda (d2: 
C).(\lambda (u0: T).(drop O O c2 (CHead d2 (Bind Abbr) u0)))) (\lambda (d2: 
C).(\lambda (u0: T).(ty3 g d2 u0 t)))))))))) (\lambda (H8: (eq T t0 
t)).(eq_ind T t (\lambda (t1: T).((eq C (CHead c3 (Bind Abbr) u) c2) \to 
((csubt g d1 c3) \to ((ty3 g c3 u t1) \to (or (ex2 C (\lambda (d2: C).(csubt 
g d1 d2)) (\lambda (d2: C).(drop O O c2 (CHead d2 (Bind Abst) t)))) (ex3_2 C 
T (\lambda (d2: C).(\lambda (_: T).(csubt g d1 d2))) (\lambda (d2: 
C).(\lambda (u0: T).(drop O O c2 (CHead d2 (Bind Abbr) u0)))) (\lambda (d2: 
C).(\lambda (u0: T).(ty3 g d2 u0 t))))))))) (\lambda (H9: (eq C (CHead c3 
(Bind Abbr) u) c2)).(eq_ind C (CHead c3 (Bind Abbr) u) (\lambda (c: 
C).((csubt g d1 c3) \to ((ty3 g c3 u t) \to (or (ex2 C (\lambda (d2: 
C).(csubt g d1 d2)) (\lambda (d2: C).(drop O O c (CHead d2 (Bind Abst) t)))) 
(ex3_2 C T (\lambda (d2: C).(\lambda (_: T).(csubt g d1 d2))) (\lambda (d2: 
C).(\lambda (u0: T).(drop O O c (CHead d2 (Bind Abbr) u0)))) (\lambda (d2: 
C).(\lambda (u0: T).(ty3 g d2 u0 t)))))))) (\lambda (H10: (csubt g d1 
c3)).(\lambda (H11: (ty3 g c3 u t)).(or_intror (ex2 C (\lambda (d2: C).(csubt 
g d1 d2)) (\lambda (d2: C).(drop O O (CHead c3 (Bind Abbr) u) (CHead d2 (Bind 
Abst) t)))) (ex3_2 C T (\lambda (d2: C).(\lambda (_: T).(csubt g d1 d2))) 
(\lambda (d2: C).(\lambda (u0: T).(drop O O (CHead c3 (Bind Abbr) u) (CHead 
d2 (Bind Abbr) u0)))) (\lambda (d2: C).(\lambda (u0: T).(ty3 g d2 u0 t)))) 
(ex3_2_intro C T (\lambda (d2: C).(\lambda (_: T).(csubt g d1 d2))) (\lambda 
(d2: C).(\lambda (u0: T).(drop O O (CHead c3 (Bind Abbr) u) (CHead d2 (Bind 
Abbr) u0)))) (\lambda (d2: C).(\lambda (u0: T).(ty3 g d2 u0 t))) c3 u H10 
(drop_refl (CHead c3 (Bind Abbr) u)) H11)))) c2 H9)) t0 (sym_eq T t0 t H8))) 
c0 (sym_eq C c0 d1 H7))) H6)) H5 H2 H3)))]) in (H2 (refl_equal C (CHead d1 
(Bind Abst) t)) (refl_equal C c2)))))))))) (\lambda (n0: nat).(\lambda (H: 
((\forall (c1: C).(\forall (c2: C).((csubt g c1 c2) \to (\forall (d1: 
C).(\forall (t: T).((drop n0 O c1 (CHead d1 (Bind Abst) t)) \to (or (ex2 C 
(\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: C).(drop n0 O c2 (CHead d2 
(Bind Abst) t)))) (ex3_2 C T (\lambda (d2: C).(\lambda (_: T).(csubt g d1 
d2))) (\lambda (d2: C).(\lambda (u: T).(drop n0 O c2 (CHead d2 (Bind Abbr) 
u)))) (\lambda (d2: C).(\lambda (u: T).(ty3 g d2 u t))))))))))))).(\lambda 
(c1: C).(\lambda (c2: C).(\lambda (H0: (csubt g c1 c2)).(csubt_ind g (\lambda 
(c: C).(\lambda (c0: C).(\forall (d1: C).(\forall (t: T).((drop (S n0) O c 
(CHead d1 (Bind Abst) t)) \to (or (ex2 C (\lambda (d2: C).(csubt g d1 d2)) 
(\lambda (d2: C).(drop (S n0) O c0 (CHead d2 (Bind Abst) t)))) (ex3_2 C T 
(\lambda (d2: C).(\lambda (_: T).(csubt g d1 d2))) (\lambda (d2: C).(\lambda 
(u: T).(drop (S n0) O c0 (CHead d2 (Bind Abbr) u)))) (\lambda (d2: 
C).(\lambda (u: T).(ty3 g d2 u t)))))))))) (\lambda (n1: nat).(\lambda (d1: 
C).(\lambda (t: T).(\lambda (H1: (drop (S n0) O (CSort n1) (CHead d1 (Bind 
Abst) t))).(let H2 \def (match H1 in drop return (\lambda (n2: nat).(\lambda 
(n3: nat).(\lambda (c: C).(\lambda (c0: C).(\lambda (_: (drop n2 n3 c 
c0)).((eq nat n2 (S n0)) \to ((eq nat n3 O) \to ((eq C c (CSort n1)) \to ((eq 
C c0 (CHead d1 (Bind Abst) t)) \to (or (ex2 C (\lambda (d2: C).(csubt g d1 
d2)) (\lambda (d2: C).(drop (S n0) O (CSort n1) (CHead d2 (Bind Abst) t)))) 
(ex3_2 C T (\lambda (d2: C).(\lambda (_: T).(csubt g d1 d2))) (\lambda (d2: 
C).(\lambda (u: T).(drop (S n0) O (CSort n1) (CHead d2 (Bind Abbr) u)))) 
(\lambda (d2: C).(\lambda (u: T).(ty3 g d2 u t)))))))))))))) with [(drop_refl 
c) \Rightarrow (\lambda (H2: (eq nat O (S n0))).(\lambda (H3: (eq nat O 
O)).(\lambda (H4: (eq C c (CSort n1))).(\lambda (H5: (eq C c (CHead d1 (Bind 
Abst) t))).((let H6 \def (eq_ind nat O (\lambda (e: nat).(match e in nat 
return (\lambda (_: nat).Prop) with [O \Rightarrow True | (S _) \Rightarrow 
False])) I (S n0) H2) in (False_ind ((eq nat O O) \to ((eq C c (CSort n1)) 
\to ((eq C c (CHead d1 (Bind Abst) t)) \to (or (ex2 C (\lambda (d2: C).(csubt 
g d1 d2)) (\lambda (d2: C).(drop (S n0) O (CSort n1) (CHead d2 (Bind Abst) 
t)))) (ex3_2 C T (\lambda (d2: C).(\lambda (_: T).(csubt g d1 d2))) (\lambda 
(d2: C).(\lambda (u: T).(drop (S n0) O (CSort n1) (CHead d2 (Bind Abbr) u)))) 
(\lambda (d2: C).(\lambda (u: T).(ty3 g d2 u t)))))))) H6)) H3 H4 H5))))) | 
(drop_drop k h c e H2 u) \Rightarrow (\lambda (H3: (eq nat (S h) (S 
n0))).(\lambda (H4: (eq nat O O)).(\lambda (H5: (eq C (CHead c k u) (CSort 
n1))).(\lambda (H6: (eq C e (CHead d1 (Bind Abst) t))).((let H7 \def (f_equal 
nat nat (\lambda (e0: nat).(match e0 in nat return (\lambda (_: nat).nat) 
with [O \Rightarrow h | (S n2) \Rightarrow n2])) (S h) (S n0) H3) in (eq_ind 
nat n0 (\lambda (n2: nat).((eq nat O O) \to ((eq C (CHead c k u) (CSort n1)) 
\to ((eq C e (CHead d1 (Bind Abst) t)) \to ((drop (r k n2) O c e) \to (or 
(ex2 C (\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: C).(drop (S n0) O 
(CSort n1) (CHead d2 (Bind Abst) t)))) (ex3_2 C T (\lambda (d2: C).(\lambda 
(_: T).(csubt g d1 d2))) (\lambda (d2: C).(\lambda (u0: T).(drop (S n0) O 
(CSort n1) (CHead d2 (Bind Abbr) u0)))) (\lambda (d2: C).(\lambda (u0: 
T).(ty3 g d2 u0 t)))))))))) (\lambda (_: (eq nat O O)).(\lambda (H9: (eq C 
(CHead c k u) (CSort n1))).(let H10 \def (eq_ind C (CHead c k u) (\lambda 
(e0: C).(match e0 in C return (\lambda (_: C).Prop) with [(CSort _) 
\Rightarrow False | (CHead _ _ _) \Rightarrow True])) I (CSort n1) H9) in 
(False_ind ((eq C e (CHead d1 (Bind Abst) t)) \to ((drop (r k n0) O c e) \to 
(or (ex2 C (\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: C).(drop (S n0) O 
(CSort n1) (CHead d2 (Bind Abst) t)))) (ex3_2 C T (\lambda (d2: C).(\lambda 
(_: T).(csubt g d1 d2))) (\lambda (d2: C).(\lambda (u0: T).(drop (S n0) O 
(CSort n1) (CHead d2 (Bind Abbr) u0)))) (\lambda (d2: C).(\lambda (u0: 
T).(ty3 g d2 u0 t))))))) H10)))) h (sym_eq nat h n0 H7))) H4 H5 H6 H2))))) | 
(drop_skip k h d c e H2 u) \Rightarrow (\lambda (H3: (eq nat h (S 
n0))).(\lambda (H4: (eq nat (S d) O)).(\lambda (H5: (eq C (CHead c k (lift h 
(r k d) u)) (CSort n1))).(\lambda (H6: (eq C (CHead e k u) (CHead d1 (Bind 
Abst) t))).(eq_ind nat (S n0) (\lambda (n2: nat).((eq nat (S d) O) \to ((eq C 
(CHead c k (lift n2 (r k d) u)) (CSort n1)) \to ((eq C (CHead e k u) (CHead 
d1 (Bind Abst) t)) \to ((drop n2 (r k d) c e) \to (or (ex2 C (\lambda (d2: 
C).(csubt g d1 d2)) (\lambda (d2: C).(drop (S n0) O (CSort n1) (CHead d2 
(Bind Abst) t)))) (ex3_2 C T (\lambda (d2: C).(\lambda (_: T).(csubt g d1 
d2))) (\lambda (d2: C).(\lambda (u0: T).(drop (S n0) O (CSort n1) (CHead d2 
(Bind Abbr) u0)))) (\lambda (d2: C).(\lambda (u0: T).(ty3 g d2 u0 t)))))))))) 
(\lambda (H7: (eq nat (S d) O)).(let H8 \def (eq_ind nat (S d) (\lambda (e0: 
nat).(match e0 in nat return (\lambda (_: nat).Prop) with [O \Rightarrow 
False | (S _) \Rightarrow True])) I O H7) in (False_ind ((eq C (CHead c k 
(lift (S n0) (r k d) u)) (CSort n1)) \to ((eq C (CHead e k u) (CHead d1 (Bind 
Abst) t)) \to ((drop (S n0) (r k d) c e) \to (or (ex2 C (\lambda (d2: 
C).(csubt g d1 d2)) (\lambda (d2: C).(drop (S n0) O (CSort n1) (CHead d2 
(Bind Abst) t)))) (ex3_2 C T (\lambda (d2: C).(\lambda (_: T).(csubt g d1 
d2))) (\lambda (d2: C).(\lambda (u0: T).(drop (S n0) O (CSort n1) (CHead d2 
(Bind Abbr) u0)))) (\lambda (d2: C).(\lambda (u0: T).(ty3 g d2 u0 t)))))))) 
H8))) h (sym_eq nat h (S n0) H3) H4 H5 H6 H2)))))]) in (H2 (refl_equal nat (S 
n0)) (refl_equal nat O) (refl_equal C (CSort n1)) (refl_equal C (CHead d1 
(Bind Abst) t)))))))) (\lambda (c0: C).(\lambda (c3: C).(\lambda (H1: (csubt 
g c0 c3)).(\lambda (H2: ((\forall (d1: C).(\forall (t: T).((drop (S n0) O c0 
(CHead d1 (Bind Abst) t)) \to (or (ex2 C (\lambda (d2: C).(csubt g d1 d2)) 
(\lambda (d2: C).(drop (S n0) O c3 (CHead d2 (Bind Abst) t)))) (ex3_2 C T 
(\lambda (d2: C).(\lambda (_: T).(csubt g d1 d2))) (\lambda (d2: C).(\lambda 
(u: T).(drop (S n0) O c3 (CHead d2 (Bind Abbr) u)))) (\lambda (d2: 
C).(\lambda (u: T).(ty3 g d2 u t)))))))))).(\lambda (k: K).(K_ind (\lambda 
(k0: K).(\forall (u: T).(\forall (d1: C).(\forall (t: T).((drop (S n0) O 
(CHead c0 k0 u) (CHead d1 (Bind Abst) t)) \to (or (ex2 C (\lambda (d2: 
C).(csubt g d1 d2)) (\lambda (d2: C).(drop (S n0) O (CHead c3 k0 u) (CHead d2 
(Bind Abst) t)))) (ex3_2 C T (\lambda (d2: C).(\lambda (_: T).(csubt g d1 
d2))) (\lambda (d2: C).(\lambda (u0: T).(drop (S n0) O (CHead c3 k0 u) (CHead 
d2 (Bind Abbr) u0)))) (\lambda (d2: C).(\lambda (u0: T).(ty3 g d2 u0 
t)))))))))) (\lambda (b: B).(\lambda (u: T).(\lambda (d1: C).(\lambda (t: 
T).(\lambda (H3: (drop (S n0) O (CHead c0 (Bind b) u) (CHead d1 (Bind Abst) 
t))).(or_ind (ex2 C (\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: C).(drop 
n0 O c3 (CHead d2 (Bind Abst) t)))) (ex3_2 C T (\lambda (d2: C).(\lambda (_: 
T).(csubt g d1 d2))) (\lambda (d2: C).(\lambda (u0: T).(drop n0 O c3 (CHead 
d2 (Bind Abbr) u0)))) (\lambda (d2: C).(\lambda (u0: T).(ty3 g d2 u0 t)))) 
(or (ex2 C (\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: C).(drop (S n0) O 
(CHead c3 (Bind b) u) (CHead d2 (Bind Abst) t)))) (ex3_2 C T (\lambda (d2: 
C).(\lambda (_: T).(csubt g d1 d2))) (\lambda (d2: C).(\lambda (u0: T).(drop 
(S n0) O (CHead c3 (Bind b) u) (CHead d2 (Bind Abbr) u0)))) (\lambda (d2: 
C).(\lambda (u0: T).(ty3 g d2 u0 t))))) (\lambda (H4: (ex2 C (\lambda (d2: 
C).(csubt g d1 d2)) (\lambda (d2: C).(drop n0 O c3 (CHead d2 (Bind Abst) 
t))))).(ex2_ind C (\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: C).(drop n0 
O c3 (CHead d2 (Bind Abst) t))) (or (ex2 C (\lambda (d2: C).(csubt g d1 d2)) 
(\lambda (d2: C).(drop (S n0) O (CHead c3 (Bind b) u) (CHead d2 (Bind Abst) 
t)))) (ex3_2 C T (\lambda (d2: C).(\lambda (_: T).(csubt g d1 d2))) (\lambda 
(d2: C).(\lambda (u0: T).(drop (S n0) O (CHead c3 (Bind b) u) (CHead d2 (Bind 
Abbr) u0)))) (\lambda (d2: C).(\lambda (u0: T).(ty3 g d2 u0 t))))) (\lambda 
(x: C).(\lambda (H5: (csubt g d1 x)).(\lambda (H6: (drop n0 O c3 (CHead x 
(Bind Abst) t))).(or_introl (ex2 C (\lambda (d2: C).(csubt g d1 d2)) (\lambda 
(d2: C).(drop (S n0) O (CHead c3 (Bind b) u) (CHead d2 (Bind Abst) t)))) 
(ex3_2 C T (\lambda (d2: C).(\lambda (_: T).(csubt g d1 d2))) (\lambda (d2: 
C).(\lambda (u0: T).(drop (S n0) O (CHead c3 (Bind b) u) (CHead d2 (Bind 
Abbr) u0)))) (\lambda (d2: C).(\lambda (u0: T).(ty3 g d2 u0 t)))) (ex_intro2 
C (\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: C).(drop (S n0) O (CHead c3 
(Bind b) u) (CHead d2 (Bind Abst) t))) x H5 (drop_drop (Bind b) n0 c3 (CHead 
x (Bind Abst) t) H6 u)))))) H4)) (\lambda (H4: (ex3_2 C T (\lambda (d2: 
C).(\lambda (_: T).(csubt g d1 d2))) (\lambda (d2: C).(\lambda (u0: T).(drop 
n0 O c3 (CHead d2 (Bind Abbr) u0)))) (\lambda (d2: C).(\lambda (u0: T).(ty3 g 
d2 u0 t))))).(ex3_2_ind C T (\lambda (d2: C).(\lambda (_: T).(csubt g d1 
d2))) (\lambda (d2: C).(\lambda (u0: T).(drop n0 O c3 (CHead d2 (Bind Abbr) 
u0)))) (\lambda (d2: C).(\lambda (u0: T).(ty3 g d2 u0 t))) (or (ex2 C 
(\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: C).(drop (S n0) O (CHead c3 
(Bind b) u) (CHead d2 (Bind Abst) t)))) (ex3_2 C T (\lambda (d2: C).(\lambda 
(_: T).(csubt g d1 d2))) (\lambda (d2: C).(\lambda (u0: T).(drop (S n0) O 
(CHead c3 (Bind b) u) (CHead d2 (Bind Abbr) u0)))) (\lambda (d2: C).(\lambda 
(u0: T).(ty3 g d2 u0 t))))) (\lambda (x0: C).(\lambda (x1: T).(\lambda (H5: 
(csubt g d1 x0)).(\lambda (H6: (drop n0 O c3 (CHead x0 (Bind Abbr) 
x1))).(\lambda (H7: (ty3 g x0 x1 t)).(or_intror (ex2 C (\lambda (d2: 
C).(csubt g d1 d2)) (\lambda (d2: C).(drop (S n0) O (CHead c3 (Bind b) u) 
(CHead d2 (Bind Abst) t)))) (ex3_2 C T (\lambda (d2: C).(\lambda (_: 
T).(csubt g d1 d2))) (\lambda (d2: C).(\lambda (u0: T).(drop (S n0) O (CHead 
c3 (Bind b) u) (CHead d2 (Bind Abbr) u0)))) (\lambda (d2: C).(\lambda (u0: 
T).(ty3 g d2 u0 t)))) (ex3_2_intro C T (\lambda (d2: C).(\lambda (_: 
T).(csubt g d1 d2))) (\lambda (d2: C).(\lambda (u0: T).(drop (S n0) O (CHead 
c3 (Bind b) u) (CHead d2 (Bind Abbr) u0)))) (\lambda (d2: C).(\lambda (u0: 
T).(ty3 g d2 u0 t))) x0 x1 H5 (drop_drop (Bind b) n0 c3 (CHead x0 (Bind Abbr) 
x1) H6 u) H7))))))) H4)) (H c0 c3 H1 d1 t (drop_gen_drop (Bind b) c0 (CHead 
d1 (Bind Abst) t) u n0 H3)))))))) (\lambda (f: F).(\lambda (u: T).(\lambda 
(d1: C).(\lambda (t: T).(\lambda (H3: (drop (S n0) O (CHead c0 (Flat f) u) 
(CHead d1 (Bind Abst) t))).(or_ind (ex2 C (\lambda (d2: C).(csubt g d1 d2)) 
(\lambda (d2: C).(drop (S n0) O c3 (CHead d2 (Bind Abst) t)))) (ex3_2 C T 
(\lambda (d2: C).(\lambda (_: T).(csubt g d1 d2))) (\lambda (d2: C).(\lambda 
(u0: T).(drop (S n0) O c3 (CHead d2 (Bind Abbr) u0)))) (\lambda (d2: 
C).(\lambda (u0: T).(ty3 g d2 u0 t)))) (or (ex2 C (\lambda (d2: C).(csubt g 
d1 d2)) (\lambda (d2: C).(drop (S n0) O (CHead c3 (Flat f) u) (CHead d2 (Bind 
Abst) t)))) (ex3_2 C T (\lambda (d2: C).(\lambda (_: T).(csubt g d1 d2))) 
(\lambda (d2: C).(\lambda (u0: T).(drop (S n0) O (CHead c3 (Flat f) u) (CHead 
d2 (Bind Abbr) u0)))) (\lambda (d2: C).(\lambda (u0: T).(ty3 g d2 u0 t))))) 
(\lambda (H4: (ex2 C (\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: C).(drop 
(S n0) O c3 (CHead d2 (Bind Abst) t))))).(ex2_ind C (\lambda (d2: C).(csubt g 
d1 d2)) (\lambda (d2: C).(drop (S n0) O c3 (CHead d2 (Bind Abst) t))) (or 
(ex2 C (\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: C).(drop (S n0) O 
(CHead c3 (Flat f) u) (CHead d2 (Bind Abst) t)))) (ex3_2 C T (\lambda (d2: 
C).(\lambda (_: T).(csubt g d1 d2))) (\lambda (d2: C).(\lambda (u0: T).(drop 
(S n0) O (CHead c3 (Flat f) u) (CHead d2 (Bind Abbr) u0)))) (\lambda (d2: 
C).(\lambda (u0: T).(ty3 g d2 u0 t))))) (\lambda (x: C).(\lambda (H5: (csubt 
g d1 x)).(\lambda (H6: (drop (S n0) O c3 (CHead x (Bind Abst) t))).(or_introl 
(ex2 C (\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: C).(drop (S n0) O 
(CHead c3 (Flat f) u) (CHead d2 (Bind Abst) t)))) (ex3_2 C T (\lambda (d2: 
C).(\lambda (_: T).(csubt g d1 d2))) (\lambda (d2: C).(\lambda (u0: T).(drop 
(S n0) O (CHead c3 (Flat f) u) (CHead d2 (Bind Abbr) u0)))) (\lambda (d2: 
C).(\lambda (u0: T).(ty3 g d2 u0 t)))) (ex_intro2 C (\lambda (d2: C).(csubt g 
d1 d2)) (\lambda (d2: C).(drop (S n0) O (CHead c3 (Flat f) u) (CHead d2 (Bind 
Abst) t))) x H5 (drop_drop (Flat f) n0 c3 (CHead x (Bind Abst) t) H6 u)))))) 
H4)) (\lambda (H4: (ex3_2 C T (\lambda (d2: C).(\lambda (_: T).(csubt g d1 
d2))) (\lambda (d2: C).(\lambda (u0: T).(drop (S n0) O c3 (CHead d2 (Bind 
Abbr) u0)))) (\lambda (d2: C).(\lambda (u0: T).(ty3 g d2 u0 t))))).(ex3_2_ind 
C T (\lambda (d2: C).(\lambda (_: T).(csubt g d1 d2))) (\lambda (d2: 
C).(\lambda (u0: T).(drop (S n0) O c3 (CHead d2 (Bind Abbr) u0)))) (\lambda 
(d2: C).(\lambda (u0: T).(ty3 g d2 u0 t))) (or (ex2 C (\lambda (d2: C).(csubt 
g d1 d2)) (\lambda (d2: C).(drop (S n0) O (CHead c3 (Flat f) u) (CHead d2 
(Bind Abst) t)))) (ex3_2 C T (\lambda (d2: C).(\lambda (_: T).(csubt g d1 
d2))) (\lambda (d2: C).(\lambda (u0: T).(drop (S n0) O (CHead c3 (Flat f) u) 
(CHead d2 (Bind Abbr) u0)))) (\lambda (d2: C).(\lambda (u0: T).(ty3 g d2 u0 
t))))) (\lambda (x0: C).(\lambda (x1: T).(\lambda (H5: (csubt g d1 
x0)).(\lambda (H6: (drop (S n0) O c3 (CHead x0 (Bind Abbr) x1))).(\lambda 
(H7: (ty3 g x0 x1 t)).(or_intror (ex2 C (\lambda (d2: C).(csubt g d1 d2)) 
(\lambda (d2: C).(drop (S n0) O (CHead c3 (Flat f) u) (CHead d2 (Bind Abst) 
t)))) (ex3_2 C T (\lambda (d2: C).(\lambda (_: T).(csubt g d1 d2))) (\lambda 
(d2: C).(\lambda (u0: T).(drop (S n0) O (CHead c3 (Flat f) u) (CHead d2 (Bind 
Abbr) u0)))) (\lambda (d2: C).(\lambda (u0: T).(ty3 g d2 u0 t)))) 
(ex3_2_intro C T (\lambda (d2: C).(\lambda (_: T).(csubt g d1 d2))) (\lambda 
(d2: C).(\lambda (u0: T).(drop (S n0) O (CHead c3 (Flat f) u) (CHead d2 (Bind 
Abbr) u0)))) (\lambda (d2: C).(\lambda (u0: T).(ty3 g d2 u0 t))) x0 x1 H5 
(drop_drop (Flat f) n0 c3 (CHead x0 (Bind Abbr) x1) H6 u) H7))))))) H4)) (H2 
d1 t (drop_gen_drop (Flat f) c0 (CHead d1 (Bind Abst) t) u n0 H3)))))))) 
k)))))) (\lambda (c0: C).(\lambda (c3: C).(\lambda (H1: (csubt g c0 
c3)).(\lambda (_: ((\forall (d1: C).(\forall (t: T).((drop (S n0) O c0 (CHead 
d1 (Bind Abst) t)) \to (or (ex2 C (\lambda (d2: C).(csubt g d1 d2)) (\lambda 
(d2: C).(drop (S n0) O c3 (CHead d2 (Bind Abst) t)))) (ex3_2 C T (\lambda 
(d2: C).(\lambda (_: T).(csubt g d1 d2))) (\lambda (d2: C).(\lambda (u: 
T).(drop (S n0) O c3 (CHead d2 (Bind Abbr) u)))) (\lambda (d2: C).(\lambda 
(u: T).(ty3 g d2 u t)))))))))).(\lambda (b: B).(\lambda (_: (not (eq B b 
Void))).(\lambda (u1: T).(\lambda (u2: T).(\lambda (d1: C).(\lambda (t: 
T).(\lambda (H4: (drop (S n0) O (CHead c0 (Bind Void) u1) (CHead d1 (Bind 
Abst) t))).(or_ind (ex2 C (\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: 
C).(drop n0 O c3 (CHead d2 (Bind Abst) t)))) (ex3_2 C T (\lambda (d2: 
C).(\lambda (_: T).(csubt g d1 d2))) (\lambda (d2: C).(\lambda (u: T).(drop 
n0 O c3 (CHead d2 (Bind Abbr) u)))) (\lambda (d2: C).(\lambda (u: T).(ty3 g 
d2 u t)))) (or (ex2 C (\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: 
C).(drop (S n0) O (CHead c3 (Bind b) u2) (CHead d2 (Bind Abst) t)))) (ex3_2 C 
T (\lambda (d2: C).(\lambda (_: T).(csubt g d1 d2))) (\lambda (d2: 
C).(\lambda (u: T).(drop (S n0) O (CHead c3 (Bind b) u2) (CHead d2 (Bind 
Abbr) u)))) (\lambda (d2: C).(\lambda (u: T).(ty3 g d2 u t))))) (\lambda (H5: 
(ex2 C (\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: C).(drop n0 O c3 
(CHead d2 (Bind Abst) t))))).(ex2_ind C (\lambda (d2: C).(csubt g d1 d2)) 
(\lambda (d2: C).(drop n0 O c3 (CHead d2 (Bind Abst) t))) (or (ex2 C (\lambda 
(d2: C).(csubt g d1 d2)) (\lambda (d2: C).(drop (S n0) O (CHead c3 (Bind b) 
u2) (CHead d2 (Bind Abst) t)))) (ex3_2 C T (\lambda (d2: C).(\lambda (_: 
T).(csubt g d1 d2))) (\lambda (d2: C).(\lambda (u: T).(drop (S n0) O (CHead 
c3 (Bind b) u2) (CHead d2 (Bind Abbr) u)))) (\lambda (d2: C).(\lambda (u: 
T).(ty3 g d2 u t))))) (\lambda (x: C).(\lambda (H6: (csubt g d1 x)).(\lambda 
(H7: (drop n0 O c3 (CHead x (Bind Abst) t))).(or_introl (ex2 C (\lambda (d2: 
C).(csubt g d1 d2)) (\lambda (d2: C).(drop (S n0) O (CHead c3 (Bind b) u2) 
(CHead d2 (Bind Abst) t)))) (ex3_2 C T (\lambda (d2: C).(\lambda (_: 
T).(csubt g d1 d2))) (\lambda (d2: C).(\lambda (u: T).(drop (S n0) O (CHead 
c3 (Bind b) u2) (CHead d2 (Bind Abbr) u)))) (\lambda (d2: C).(\lambda (u: 
T).(ty3 g d2 u t)))) (ex_intro2 C (\lambda (d2: C).(csubt g d1 d2)) (\lambda 
(d2: C).(drop (S n0) O (CHead c3 (Bind b) u2) (CHead d2 (Bind Abst) t))) x H6 
(drop_drop (Bind b) n0 c3 (CHead x (Bind Abst) t) H7 u2)))))) H5)) (\lambda 
(H5: (ex3_2 C T (\lambda (d2: C).(\lambda (_: T).(csubt g d1 d2))) (\lambda 
(d2: C).(\lambda (u: T).(drop n0 O c3 (CHead d2 (Bind Abbr) u)))) (\lambda 
(d2: C).(\lambda (u: T).(ty3 g d2 u t))))).(ex3_2_ind C T (\lambda (d2: 
C).(\lambda (_: T).(csubt g d1 d2))) (\lambda (d2: C).(\lambda (u: T).(drop 
n0 O c3 (CHead d2 (Bind Abbr) u)))) (\lambda (d2: C).(\lambda (u: T).(ty3 g 
d2 u t))) (or (ex2 C (\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: C).(drop 
(S n0) O (CHead c3 (Bind b) u2) (CHead d2 (Bind Abst) t)))) (ex3_2 C T 
(\lambda (d2: C).(\lambda (_: T).(csubt g d1 d2))) (\lambda (d2: C).(\lambda 
(u: T).(drop (S n0) O (CHead c3 (Bind b) u2) (CHead d2 (Bind Abbr) u)))) 
(\lambda (d2: C).(\lambda (u: T).(ty3 g d2 u t))))) (\lambda (x0: C).(\lambda 
(x1: T).(\lambda (H6: (csubt g d1 x0)).(\lambda (H7: (drop n0 O c3 (CHead x0 
(Bind Abbr) x1))).(\lambda (H8: (ty3 g x0 x1 t)).(or_intror (ex2 C (\lambda 
(d2: C).(csubt g d1 d2)) (\lambda (d2: C).(drop (S n0) O (CHead c3 (Bind b) 
u2) (CHead d2 (Bind Abst) t)))) (ex3_2 C T (\lambda (d2: C).(\lambda (_: 
T).(csubt g d1 d2))) (\lambda (d2: C).(\lambda (u: T).(drop (S n0) O (CHead 
c3 (Bind b) u2) (CHead d2 (Bind Abbr) u)))) (\lambda (d2: C).(\lambda (u: 
T).(ty3 g d2 u t)))) (ex3_2_intro C T (\lambda (d2: C).(\lambda (_: T).(csubt 
g d1 d2))) (\lambda (d2: C).(\lambda (u: T).(drop (S n0) O (CHead c3 (Bind b) 
u2) (CHead d2 (Bind Abbr) u)))) (\lambda (d2: C).(\lambda (u: T).(ty3 g d2 u 
t))) x0 x1 H6 (drop_drop (Bind b) n0 c3 (CHead x0 (Bind Abbr) x1) H7 u2) 
H8))))))) H5)) (H c0 c3 H1 d1 t (drop_gen_drop (Bind Void) c0 (CHead d1 (Bind 
Abst) t) u1 n0 H4)))))))))))))) (\lambda (c0: C).(\lambda (c3: C).(\lambda 
(H1: (csubt g c0 c3)).(\lambda (_: ((\forall (d1: C).(\forall (t: T).((drop 
(S n0) O c0 (CHead d1 (Bind Abst) t)) \to (or (ex2 C (\lambda (d2: C).(csubt 
g d1 d2)) (\lambda (d2: C).(drop (S n0) O c3 (CHead d2 (Bind Abst) t)))) 
(ex3_2 C T (\lambda (d2: C).(\lambda (_: T).(csubt g d1 d2))) (\lambda (d2: 
C).(\lambda (u: T).(drop (S n0) O c3 (CHead d2 (Bind Abbr) u)))) (\lambda 
(d2: C).(\lambda (u: T).(ty3 g d2 u t)))))))))).(\lambda (u: T).(\lambda (t: 
T).(\lambda (_: (ty3 g c3 u t)).(\lambda (d1: C).(\lambda (t0: T).(\lambda 
(H4: (drop (S n0) O (CHead c0 (Bind Abst) t) (CHead d1 (Bind Abst) 
t0))).(or_ind (ex2 C (\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: C).(drop 
n0 O c3 (CHead d2 (Bind Abst) t0)))) (ex3_2 C T (\lambda (d2: C).(\lambda (_: 
T).(csubt g d1 d2))) (\lambda (d2: C).(\lambda (u0: T).(drop n0 O c3 (CHead 
d2 (Bind Abbr) u0)))) (\lambda (d2: C).(\lambda (u0: T).(ty3 g d2 u0 t0)))) 
(or (ex2 C (\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: C).(drop (S n0) O 
(CHead c3 (Bind Abbr) u) (CHead d2 (Bind Abst) t0)))) (ex3_2 C T (\lambda 
(d2: C).(\lambda (_: T).(csubt g d1 d2))) (\lambda (d2: C).(\lambda (u0: 
T).(drop (S n0) O (CHead c3 (Bind Abbr) u) (CHead d2 (Bind Abbr) u0)))) 
(\lambda (d2: C).(\lambda (u0: T).(ty3 g d2 u0 t0))))) (\lambda (H5: (ex2 C 
(\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: C).(drop n0 O c3 (CHead d2 
(Bind Abst) t0))))).(ex2_ind C (\lambda (d2: C).(csubt g d1 d2)) (\lambda 
(d2: C).(drop n0 O c3 (CHead d2 (Bind Abst) t0))) (or (ex2 C (\lambda (d2: 
C).(csubt g d1 d2)) (\lambda (d2: C).(drop (S n0) O (CHead c3 (Bind Abbr) u) 
(CHead d2 (Bind Abst) t0)))) (ex3_2 C T (\lambda (d2: C).(\lambda (_: 
T).(csubt g d1 d2))) (\lambda (d2: C).(\lambda (u0: T).(drop (S n0) O (CHead 
c3 (Bind Abbr) u) (CHead d2 (Bind Abbr) u0)))) (\lambda (d2: C).(\lambda (u0: 
T).(ty3 g d2 u0 t0))))) (\lambda (x: C).(\lambda (H6: (csubt g d1 
x)).(\lambda (H7: (drop n0 O c3 (CHead x (Bind Abst) t0))).(or_introl (ex2 C 
(\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: C).(drop (S n0) O (CHead c3 
(Bind Abbr) u) (CHead d2 (Bind Abst) t0)))) (ex3_2 C T (\lambda (d2: 
C).(\lambda (_: T).(csubt g d1 d2))) (\lambda (d2: C).(\lambda (u0: T).(drop 
(S n0) O (CHead c3 (Bind Abbr) u) (CHead d2 (Bind Abbr) u0)))) (\lambda (d2: 
C).(\lambda (u0: T).(ty3 g d2 u0 t0)))) (ex_intro2 C (\lambda (d2: C).(csubt 
g d1 d2)) (\lambda (d2: C).(drop (S n0) O (CHead c3 (Bind Abbr) u) (CHead d2 
(Bind Abst) t0))) x H6 (drop_drop (Bind Abbr) n0 c3 (CHead x (Bind Abst) t0) 
H7 u)))))) H5)) (\lambda (H5: (ex3_2 C T (\lambda (d2: C).(\lambda (_: 
T).(csubt g d1 d2))) (\lambda (d2: C).(\lambda (u0: T).(drop n0 O c3 (CHead 
d2 (Bind Abbr) u0)))) (\lambda (d2: C).(\lambda (u0: T).(ty3 g d2 u0 
t0))))).(ex3_2_ind C T (\lambda (d2: C).(\lambda (_: T).(csubt g d1 d2))) 
(\lambda (d2: C).(\lambda (u0: T).(drop n0 O c3 (CHead d2 (Bind Abbr) u0)))) 
(\lambda (d2: C).(\lambda (u0: T).(ty3 g d2 u0 t0))) (or (ex2 C (\lambda (d2: 
C).(csubt g d1 d2)) (\lambda (d2: C).(drop (S n0) O (CHead c3 (Bind Abbr) u) 
(CHead d2 (Bind Abst) t0)))) (ex3_2 C T (\lambda (d2: C).(\lambda (_: 
T).(csubt g d1 d2))) (\lambda (d2: C).(\lambda (u0: T).(drop (S n0) O (CHead 
c3 (Bind Abbr) u) (CHead d2 (Bind Abbr) u0)))) (\lambda (d2: C).(\lambda (u0: 
T).(ty3 g d2 u0 t0))))) (\lambda (x0: C).(\lambda (x1: T).(\lambda (H6: 
(csubt g d1 x0)).(\lambda (H7: (drop n0 O c3 (CHead x0 (Bind Abbr) 
x1))).(\lambda (H8: (ty3 g x0 x1 t0)).(or_intror (ex2 C (\lambda (d2: 
C).(csubt g d1 d2)) (\lambda (d2: C).(drop (S n0) O (CHead c3 (Bind Abbr) u) 
(CHead d2 (Bind Abst) t0)))) (ex3_2 C T (\lambda (d2: C).(\lambda (_: 
T).(csubt g d1 d2))) (\lambda (d2: C).(\lambda (u0: T).(drop (S n0) O (CHead 
c3 (Bind Abbr) u) (CHead d2 (Bind Abbr) u0)))) (\lambda (d2: C).(\lambda (u0: 
T).(ty3 g d2 u0 t0)))) (ex3_2_intro C T (\lambda (d2: C).(\lambda (_: 
T).(csubt g d1 d2))) (\lambda (d2: C).(\lambda (u0: T).(drop (S n0) O (CHead 
c3 (Bind Abbr) u) (CHead d2 (Bind Abbr) u0)))) (\lambda (d2: C).(\lambda (u0: 
T).(ty3 g d2 u0 t0))) x0 x1 H6 (drop_drop (Bind Abbr) n0 c3 (CHead x0 (Bind 
Abbr) x1) H7 u) H8))))))) H5)) (H c0 c3 H1 d1 t0 (drop_gen_drop (Bind Abst) 
c0 (CHead d1 (Bind Abst) t0) t n0 H4))))))))))))) c1 c2 H0)))))) n)).

