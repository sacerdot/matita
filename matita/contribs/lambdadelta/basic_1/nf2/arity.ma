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

include "Basic-1/nf2/fwd.ma".

include "Basic-1/arity/subst0.ma".

theorem arity_nf2_inv_all:
 \forall (g: G).(\forall (c: C).(\forall (t: T).(\forall (a: A).((arity g c t 
a) \to ((nf2 c t) \to (or3 (ex3_2 T T (\lambda (w: T).(\lambda (u: T).(eq T t 
(THead (Bind Abst) w u)))) (\lambda (w: T).(\lambda (_: T).(nf2 c w))) 
(\lambda (w: T).(\lambda (u: T).(nf2 (CHead c (Bind Abst) w) u)))) (ex nat 
(\lambda (n: nat).(eq T t (TSort n)))) (ex3_2 TList nat (\lambda (ws: 
TList).(\lambda (i: nat).(eq T t (THeads (Flat Appl) ws (TLRef i))))) 
(\lambda (ws: TList).(\lambda (_: nat).(nfs2 c ws))) (\lambda (_: 
TList).(\lambda (i: nat).(nf2 c (TLRef i)))))))))))
\def
 \lambda (g: G).(\lambda (c: C).(\lambda (t: T).(\lambda (a: A).(\lambda (H: 
(arity g c t a)).(arity_ind g (\lambda (c0: C).(\lambda (t0: T).(\lambda (_: 
A).((nf2 c0 t0) \to (or3 (ex3_2 T T (\lambda (w: T).(\lambda (u: T).(eq T t0 
(THead (Bind Abst) w u)))) (\lambda (w: T).(\lambda (_: T).(nf2 c0 w))) 
(\lambda (w: T).(\lambda (u: T).(nf2 (CHead c0 (Bind Abst) w) u)))) (ex nat 
(\lambda (n: nat).(eq T t0 (TSort n)))) (ex3_2 TList nat (\lambda (ws: 
TList).(\lambda (i: nat).(eq T t0 (THeads (Flat Appl) ws (TLRef i))))) 
(\lambda (ws: TList).(\lambda (_: nat).(nfs2 c0 ws))) (\lambda (_: 
TList).(\lambda (i: nat).(nf2 c0 (TLRef i)))))))))) (\lambda (c0: C).(\lambda 
(n: nat).(\lambda (_: (nf2 c0 (TSort n))).(or3_intro1 (ex3_2 T T (\lambda (w: 
T).(\lambda (u: T).(eq T (TSort n) (THead (Bind Abst) w u)))) (\lambda (w: 
T).(\lambda (_: T).(nf2 c0 w))) (\lambda (w: T).(\lambda (u: T).(nf2 (CHead 
c0 (Bind Abst) w) u)))) (ex nat (\lambda (n0: nat).(eq T (TSort n) (TSort 
n0)))) (ex3_2 TList nat (\lambda (ws: TList).(\lambda (i: nat).(eq T (TSort 
n) (THeads (Flat Appl) ws (TLRef i))))) (\lambda (ws: TList).(\lambda (_: 
nat).(nfs2 c0 ws))) (\lambda (_: TList).(\lambda (i: nat).(nf2 c0 (TLRef 
i))))) (ex_intro nat (\lambda (n0: nat).(eq T (TSort n) (TSort n0))) n 
(refl_equal T (TSort n))))))) (\lambda (c0: C).(\lambda (d: C).(\lambda (u: 
T).(\lambda (i: nat).(\lambda (H0: (getl i c0 (CHead d (Bind Abbr) 
u))).(\lambda (a0: A).(\lambda (_: (arity g d u a0)).(\lambda (_: (((nf2 d u) 
\to (or3 (ex3_2 T T (\lambda (w: T).(\lambda (u0: T).(eq T u (THead (Bind 
Abst) w u0)))) (\lambda (w: T).(\lambda (_: T).(nf2 d w))) (\lambda (w: 
T).(\lambda (u0: T).(nf2 (CHead d (Bind Abst) w) u0)))) (ex nat (\lambda (n: 
nat).(eq T u (TSort n)))) (ex3_2 TList nat (\lambda (ws: TList).(\lambda (i0: 
nat).(eq T u (THeads (Flat Appl) ws (TLRef i0))))) (\lambda (ws: 
TList).(\lambda (_: nat).(nfs2 d ws))) (\lambda (_: TList).(\lambda (i0: 
nat).(nf2 d (TLRef i0))))))))).(\lambda (H3: (nf2 c0 (TLRef 
i))).(nf2_gen_lref c0 d u i H0 H3 (or3 (ex3_2 T T (\lambda (w: T).(\lambda 
(u0: T).(eq T (TLRef i) (THead (Bind Abst) w u0)))) (\lambda (w: T).(\lambda 
(_: T).(nf2 c0 w))) (\lambda (w: T).(\lambda (u0: T).(nf2 (CHead c0 (Bind 
Abst) w) u0)))) (ex nat (\lambda (n: nat).(eq T (TLRef i) (TSort n)))) (ex3_2 
TList nat (\lambda (ws: TList).(\lambda (i0: nat).(eq T (TLRef i) (THeads 
(Flat Appl) ws (TLRef i0))))) (\lambda (ws: TList).(\lambda (_: nat).(nfs2 c0 
ws))) (\lambda (_: TList).(\lambda (i0: nat).(nf2 c0 (TLRef 
i0)))))))))))))))) (\lambda (c0: C).(\lambda (d: C).(\lambda (u: T).(\lambda 
(i: nat).(\lambda (_: (getl i c0 (CHead d (Bind Abst) u))).(\lambda (a0: 
A).(\lambda (_: (arity g d u (asucc g a0))).(\lambda (_: (((nf2 d u) \to (or3 
(ex3_2 T T (\lambda (w: T).(\lambda (u0: T).(eq T u (THead (Bind Abst) w 
u0)))) (\lambda (w: T).(\lambda (_: T).(nf2 d w))) (\lambda (w: T).(\lambda 
(u0: T).(nf2 (CHead d (Bind Abst) w) u0)))) (ex nat (\lambda (n: nat).(eq T u 
(TSort n)))) (ex3_2 TList nat (\lambda (ws: TList).(\lambda (i0: nat).(eq T u 
(THeads (Flat Appl) ws (TLRef i0))))) (\lambda (ws: TList).(\lambda (_: 
nat).(nfs2 d ws))) (\lambda (_: TList).(\lambda (i0: nat).(nf2 d (TLRef 
i0))))))))).(\lambda (H3: (nf2 c0 (TLRef i))).(or3_intro2 (ex3_2 T T (\lambda 
(w: T).(\lambda (u0: T).(eq T (TLRef i) (THead (Bind Abst) w u0)))) (\lambda 
(w: T).(\lambda (_: T).(nf2 c0 w))) (\lambda (w: T).(\lambda (u0: T).(nf2 
(CHead c0 (Bind Abst) w) u0)))) (ex nat (\lambda (n: nat).(eq T (TLRef i) 
(TSort n)))) (ex3_2 TList nat (\lambda (ws: TList).(\lambda (i0: nat).(eq T 
(TLRef i) (THeads (Flat Appl) ws (TLRef i0))))) (\lambda (ws: TList).(\lambda 
(_: nat).(nfs2 c0 ws))) (\lambda (_: TList).(\lambda (i0: nat).(nf2 c0 (TLRef 
i0))))) (ex3_2_intro TList nat (\lambda (ws: TList).(\lambda (i0: nat).(eq T 
(TLRef i) (THeads (Flat Appl) ws (TLRef i0))))) (\lambda (ws: TList).(\lambda 
(_: nat).(nfs2 c0 ws))) (\lambda (_: TList).(\lambda (i0: nat).(nf2 c0 (TLRef 
i0)))) TNil i (refl_equal T (TLRef i)) I H3))))))))))) (\lambda (b: 
B).(\lambda (H0: (not (eq B b Abst))).(\lambda (c0: C).(\lambda (u: 
T).(\lambda (a1: A).(\lambda (_: (arity g c0 u a1)).(\lambda (_: (((nf2 c0 u) 
\to (or3 (ex3_2 T T (\lambda (w: T).(\lambda (u0: T).(eq T u (THead (Bind 
Abst) w u0)))) (\lambda (w: T).(\lambda (_: T).(nf2 c0 w))) (\lambda (w: 
T).(\lambda (u0: T).(nf2 (CHead c0 (Bind Abst) w) u0)))) (ex nat (\lambda (n: 
nat).(eq T u (TSort n)))) (ex3_2 TList nat (\lambda (ws: TList).(\lambda (i: 
nat).(eq T u (THeads (Flat Appl) ws (TLRef i))))) (\lambda (ws: 
TList).(\lambda (_: nat).(nfs2 c0 ws))) (\lambda (_: TList).(\lambda (i: 
nat).(nf2 c0 (TLRef i))))))))).(\lambda (t0: T).(\lambda (a2: A).(\lambda 
(H3: (arity g (CHead c0 (Bind b) u) t0 a2)).(\lambda (_: (((nf2 (CHead c0 
(Bind b) u) t0) \to (or3 (ex3_2 T T (\lambda (w: T).(\lambda (u0: T).(eq T t0 
(THead (Bind Abst) w u0)))) (\lambda (w: T).(\lambda (_: T).(nf2 (CHead c0 
(Bind b) u) w))) (\lambda (w: T).(\lambda (u0: T).(nf2 (CHead (CHead c0 (Bind 
b) u) (Bind Abst) w) u0)))) (ex nat (\lambda (n: nat).(eq T t0 (TSort n)))) 
(ex3_2 TList nat (\lambda (ws: TList).(\lambda (i: nat).(eq T t0 (THeads 
(Flat Appl) ws (TLRef i))))) (\lambda (ws: TList).(\lambda (_: nat).(nfs2 
(CHead c0 (Bind b) u) ws))) (\lambda (_: TList).(\lambda (i: nat).(nf2 (CHead 
c0 (Bind b) u) (TLRef i))))))))).(\lambda (H5: (nf2 c0 (THead (Bind b) u 
t0))).(B_ind (\lambda (b0: B).((not (eq B b0 Abst)) \to ((arity g (CHead c0 
(Bind b0) u) t0 a2) \to ((nf2 c0 (THead (Bind b0) u t0)) \to (or3 (ex3_2 T T 
(\lambda (w: T).(\lambda (u0: T).(eq T (THead (Bind b0) u t0) (THead (Bind 
Abst) w u0)))) (\lambda (w: T).(\lambda (_: T).(nf2 c0 w))) (\lambda (w: 
T).(\lambda (u0: T).(nf2 (CHead c0 (Bind Abst) w) u0)))) (ex nat (\lambda (n: 
nat).(eq T (THead (Bind b0) u t0) (TSort n)))) (ex3_2 TList nat (\lambda (ws: 
TList).(\lambda (i: nat).(eq T (THead (Bind b0) u t0) (THeads (Flat Appl) ws 
(TLRef i))))) (\lambda (ws: TList).(\lambda (_: nat).(nfs2 c0 ws))) (\lambda 
(_: TList).(\lambda (i: nat).(nf2 c0 (TLRef i)))))))))) (\lambda (_: (not (eq 
B Abbr Abst))).(\lambda (_: (arity g (CHead c0 (Bind Abbr) u) t0 
a2)).(\lambda (H8: (nf2 c0 (THead (Bind Abbr) u t0))).(nf2_gen_abbr c0 u t0 
H8 (or3 (ex3_2 T T (\lambda (w: T).(\lambda (u0: T).(eq T (THead (Bind Abbr) 
u t0) (THead (Bind Abst) w u0)))) (\lambda (w: T).(\lambda (_: T).(nf2 c0 
w))) (\lambda (w: T).(\lambda (u0: T).(nf2 (CHead c0 (Bind Abst) w) u0)))) 
(ex nat (\lambda (n: nat).(eq T (THead (Bind Abbr) u t0) (TSort n)))) (ex3_2 
TList nat (\lambda (ws: TList).(\lambda (i: nat).(eq T (THead (Bind Abbr) u 
t0) (THeads (Flat Appl) ws (TLRef i))))) (\lambda (ws: TList).(\lambda (_: 
nat).(nfs2 c0 ws))) (\lambda (_: TList).(\lambda (i: nat).(nf2 c0 (TLRef 
i)))))))))) (\lambda (H6: (not (eq B Abst Abst))).(\lambda (_: (arity g 
(CHead c0 (Bind Abst) u) t0 a2)).(\lambda (_: (nf2 c0 (THead (Bind Abst) u 
t0))).(let H9 \def (match (H6 (refl_equal B Abst)) in False return (\lambda 
(_: False).(or3 (ex3_2 T T (\lambda (w: T).(\lambda (u0: T).(eq T (THead 
(Bind Abst) u t0) (THead (Bind Abst) w u0)))) (\lambda (w: T).(\lambda (_: 
T).(nf2 c0 w))) (\lambda (w: T).(\lambda (u0: T).(nf2 (CHead c0 (Bind Abst) 
w) u0)))) (ex nat (\lambda (n: nat).(eq T (THead (Bind Abst) u t0) (TSort 
n)))) (ex3_2 TList nat (\lambda (ws: TList).(\lambda (i: nat).(eq T (THead 
(Bind Abst) u t0) (THeads (Flat Appl) ws (TLRef i))))) (\lambda (ws: 
TList).(\lambda (_: nat).(nfs2 c0 ws))) (\lambda (_: TList).(\lambda (i: 
nat).(nf2 c0 (TLRef i))))))) with []) in H9)))) (\lambda (_: (not (eq B Void 
Abst))).(\lambda (H7: (arity g (CHead c0 (Bind Void) u) t0 a2)).(\lambda (H8: 
(nf2 c0 (THead (Bind Void) u t0))).(let H9 \def (arity_gen_cvoid g (CHead c0 
(Bind Void) u) t0 a2 H7 c0 u O (getl_refl Void c0 u)) in (ex_ind T (\lambda 
(v: T).(eq T t0 (lift (S O) O v))) (or3 (ex3_2 T T (\lambda (w: T).(\lambda 
(u0: T).(eq T (THead (Bind Void) u t0) (THead (Bind Abst) w u0)))) (\lambda 
(w: T).(\lambda (_: T).(nf2 c0 w))) (\lambda (w: T).(\lambda (u0: T).(nf2 
(CHead c0 (Bind Abst) w) u0)))) (ex nat (\lambda (n: nat).(eq T (THead (Bind 
Void) u t0) (TSort n)))) (ex3_2 TList nat (\lambda (ws: TList).(\lambda (i: 
nat).(eq T (THead (Bind Void) u t0) (THeads (Flat Appl) ws (TLRef i))))) 
(\lambda (ws: TList).(\lambda (_: nat).(nfs2 c0 ws))) (\lambda (_: 
TList).(\lambda (i: nat).(nf2 c0 (TLRef i)))))) (\lambda (x: T).(\lambda 
(H10: (eq T t0 (lift (S O) O x))).(let H11 \def (eq_ind T t0 (\lambda (t1: 
T).(nf2 c0 (THead (Bind Void) u t1))) H8 (lift (S O) O x) H10) in (eq_ind_r T 
(lift (S O) O x) (\lambda (t1: T).(or3 (ex3_2 T T (\lambda (w: T).(\lambda 
(u0: T).(eq T (THead (Bind Void) u t1) (THead (Bind Abst) w u0)))) (\lambda 
(w: T).(\lambda (_: T).(nf2 c0 w))) (\lambda (w: T).(\lambda (u0: T).(nf2 
(CHead c0 (Bind Abst) w) u0)))) (ex nat (\lambda (n: nat).(eq T (THead (Bind 
Void) u t1) (TSort n)))) (ex3_2 TList nat (\lambda (ws: TList).(\lambda (i: 
nat).(eq T (THead (Bind Void) u t1) (THeads (Flat Appl) ws (TLRef i))))) 
(\lambda (ws: TList).(\lambda (_: nat).(nfs2 c0 ws))) (\lambda (_: 
TList).(\lambda (i: nat).(nf2 c0 (TLRef i))))))) (nf2_gen_void c0 u x H11 
(or3 (ex3_2 T T (\lambda (w: T).(\lambda (u0: T).(eq T (THead (Bind Void) u 
(lift (S O) O x)) (THead (Bind Abst) w u0)))) (\lambda (w: T).(\lambda (_: 
T).(nf2 c0 w))) (\lambda (w: T).(\lambda (u0: T).(nf2 (CHead c0 (Bind Abst) 
w) u0)))) (ex nat (\lambda (n: nat).(eq T (THead (Bind Void) u (lift (S O) O 
x)) (TSort n)))) (ex3_2 TList nat (\lambda (ws: TList).(\lambda (i: nat).(eq 
T (THead (Bind Void) u (lift (S O) O x)) (THeads (Flat Appl) ws (TLRef i))))) 
(\lambda (ws: TList).(\lambda (_: nat).(nfs2 c0 ws))) (\lambda (_: 
TList).(\lambda (i: nat).(nf2 c0 (TLRef i))))))) t0 H10)))) H9))))) b H0 H3 
H5))))))))))))) (\lambda (c0: C).(\lambda (u: T).(\lambda (a1: A).(\lambda 
(_: (arity g c0 u (asucc g a1))).(\lambda (_: (((nf2 c0 u) \to (or3 (ex3_2 T 
T (\lambda (w: T).(\lambda (u0: T).(eq T u (THead (Bind Abst) w u0)))) 
(\lambda (w: T).(\lambda (_: T).(nf2 c0 w))) (\lambda (w: T).(\lambda (u0: 
T).(nf2 (CHead c0 (Bind Abst) w) u0)))) (ex nat (\lambda (n: nat).(eq T u 
(TSort n)))) (ex3_2 TList nat (\lambda (ws: TList).(\lambda (i: nat).(eq T u 
(THeads (Flat Appl) ws (TLRef i))))) (\lambda (ws: TList).(\lambda (_: 
nat).(nfs2 c0 ws))) (\lambda (_: TList).(\lambda (i: nat).(nf2 c0 (TLRef 
i))))))))).(\lambda (t0: T).(\lambda (a2: A).(\lambda (_: (arity g (CHead c0 
(Bind Abst) u) t0 a2)).(\lambda (_: (((nf2 (CHead c0 (Bind Abst) u) t0) \to 
(or3 (ex3_2 T T (\lambda (w: T).(\lambda (u0: T).(eq T t0 (THead (Bind Abst) 
w u0)))) (\lambda (w: T).(\lambda (_: T).(nf2 (CHead c0 (Bind Abst) u) w))) 
(\lambda (w: T).(\lambda (u0: T).(nf2 (CHead (CHead c0 (Bind Abst) u) (Bind 
Abst) w) u0)))) (ex nat (\lambda (n: nat).(eq T t0 (TSort n)))) (ex3_2 TList 
nat (\lambda (ws: TList).(\lambda (i: nat).(eq T t0 (THeads (Flat Appl) ws 
(TLRef i))))) (\lambda (ws: TList).(\lambda (_: nat).(nfs2 (CHead c0 (Bind 
Abst) u) ws))) (\lambda (_: TList).(\lambda (i: nat).(nf2 (CHead c0 (Bind 
Abst) u) (TLRef i))))))))).(\lambda (H4: (nf2 c0 (THead (Bind Abst) u 
t0))).(let H5 \def (nf2_gen_abst c0 u t0 H4) in (land_ind (nf2 c0 u) (nf2 
(CHead c0 (Bind Abst) u) t0) (or3 (ex3_2 T T (\lambda (w: T).(\lambda (u0: 
T).(eq T (THead (Bind Abst) u t0) (THead (Bind Abst) w u0)))) (\lambda (w: 
T).(\lambda (_: T).(nf2 c0 w))) (\lambda (w: T).(\lambda (u0: T).(nf2 (CHead 
c0 (Bind Abst) w) u0)))) (ex nat (\lambda (n: nat).(eq T (THead (Bind Abst) u 
t0) (TSort n)))) (ex3_2 TList nat (\lambda (ws: TList).(\lambda (i: nat).(eq 
T (THead (Bind Abst) u t0) (THeads (Flat Appl) ws (TLRef i))))) (\lambda (ws: 
TList).(\lambda (_: nat).(nfs2 c0 ws))) (\lambda (_: TList).(\lambda (i: 
nat).(nf2 c0 (TLRef i)))))) (\lambda (H6: (nf2 c0 u)).(\lambda (H7: (nf2 
(CHead c0 (Bind Abst) u) t0)).(or3_intro0 (ex3_2 T T (\lambda (w: T).(\lambda 
(u0: T).(eq T (THead (Bind Abst) u t0) (THead (Bind Abst) w u0)))) (\lambda 
(w: T).(\lambda (_: T).(nf2 c0 w))) (\lambda (w: T).(\lambda (u0: T).(nf2 
(CHead c0 (Bind Abst) w) u0)))) (ex nat (\lambda (n: nat).(eq T (THead (Bind 
Abst) u t0) (TSort n)))) (ex3_2 TList nat (\lambda (ws: TList).(\lambda (i: 
nat).(eq T (THead (Bind Abst) u t0) (THeads (Flat Appl) ws (TLRef i))))) 
(\lambda (ws: TList).(\lambda (_: nat).(nfs2 c0 ws))) (\lambda (_: 
TList).(\lambda (i: nat).(nf2 c0 (TLRef i))))) (ex3_2_intro T T (\lambda (w: 
T).(\lambda (u0: T).(eq T (THead (Bind Abst) u t0) (THead (Bind Abst) w 
u0)))) (\lambda (w: T).(\lambda (_: T).(nf2 c0 w))) (\lambda (w: T).(\lambda 
(u0: T).(nf2 (CHead c0 (Bind Abst) w) u0))) u t0 (refl_equal T (THead (Bind 
Abst) u t0)) H6 H7)))) H5)))))))))))) (\lambda (c0: C).(\lambda (u: 
T).(\lambda (a1: A).(\lambda (_: (arity g c0 u a1)).(\lambda (_: (((nf2 c0 u) 
\to (or3 (ex3_2 T T (\lambda (w: T).(\lambda (u0: T).(eq T u (THead (Bind 
Abst) w u0)))) (\lambda (w: T).(\lambda (_: T).(nf2 c0 w))) (\lambda (w: 
T).(\lambda (u0: T).(nf2 (CHead c0 (Bind Abst) w) u0)))) (ex nat (\lambda (n: 
nat).(eq T u (TSort n)))) (ex3_2 TList nat (\lambda (ws: TList).(\lambda (i: 
nat).(eq T u (THeads (Flat Appl) ws (TLRef i))))) (\lambda (ws: 
TList).(\lambda (_: nat).(nfs2 c0 ws))) (\lambda (_: TList).(\lambda (i: 
nat).(nf2 c0 (TLRef i))))))))).(\lambda (t0: T).(\lambda (a2: A).(\lambda 
(H2: (arity g c0 t0 (AHead a1 a2))).(\lambda (H3: (((nf2 c0 t0) \to (or3 
(ex3_2 T T (\lambda (w: T).(\lambda (u0: T).(eq T t0 (THead (Bind Abst) w 
u0)))) (\lambda (w: T).(\lambda (_: T).(nf2 c0 w))) (\lambda (w: T).(\lambda 
(u0: T).(nf2 (CHead c0 (Bind Abst) w) u0)))) (ex nat (\lambda (n: nat).(eq T 
t0 (TSort n)))) (ex3_2 TList nat (\lambda (ws: TList).(\lambda (i: nat).(eq T 
t0 (THeads (Flat Appl) ws (TLRef i))))) (\lambda (ws: TList).(\lambda (_: 
nat).(nfs2 c0 ws))) (\lambda (_: TList).(\lambda (i: nat).(nf2 c0 (TLRef 
i))))))))).(\lambda (H4: (nf2 c0 (THead (Flat Appl) u t0))).(let H5 \def 
(nf2_gen_flat Appl c0 u t0 H4) in (land_ind (nf2 c0 u) (nf2 c0 t0) (or3 
(ex3_2 T T (\lambda (w: T).(\lambda (u0: T).(eq T (THead (Flat Appl) u t0) 
(THead (Bind Abst) w u0)))) (\lambda (w: T).(\lambda (_: T).(nf2 c0 w))) 
(\lambda (w: T).(\lambda (u0: T).(nf2 (CHead c0 (Bind Abst) w) u0)))) (ex nat 
(\lambda (n: nat).(eq T (THead (Flat Appl) u t0) (TSort n)))) (ex3_2 TList 
nat (\lambda (ws: TList).(\lambda (i: nat).(eq T (THead (Flat Appl) u t0) 
(THeads (Flat Appl) ws (TLRef i))))) (\lambda (ws: TList).(\lambda (_: 
nat).(nfs2 c0 ws))) (\lambda (_: TList).(\lambda (i: nat).(nf2 c0 (TLRef 
i)))))) (\lambda (H6: (nf2 c0 u)).(\lambda (H7: (nf2 c0 t0)).(let H_x \def 
(H3 H7) in (let H8 \def H_x in (or3_ind (ex3_2 T T (\lambda (w: T).(\lambda 
(u0: T).(eq T t0 (THead (Bind Abst) w u0)))) (\lambda (w: T).(\lambda (_: 
T).(nf2 c0 w))) (\lambda (w: T).(\lambda (u0: T).(nf2 (CHead c0 (Bind Abst) 
w) u0)))) (ex nat (\lambda (n: nat).(eq T t0 (TSort n)))) (ex3_2 TList nat 
(\lambda (ws: TList).(\lambda (i: nat).(eq T t0 (THeads (Flat Appl) ws (TLRef 
i))))) (\lambda (ws: TList).(\lambda (_: nat).(nfs2 c0 ws))) (\lambda (_: 
TList).(\lambda (i: nat).(nf2 c0 (TLRef i))))) (or3 (ex3_2 T T (\lambda (w: 
T).(\lambda (u0: T).(eq T (THead (Flat Appl) u t0) (THead (Bind Abst) w 
u0)))) (\lambda (w: T).(\lambda (_: T).(nf2 c0 w))) (\lambda (w: T).(\lambda 
(u0: T).(nf2 (CHead c0 (Bind Abst) w) u0)))) (ex nat (\lambda (n: nat).(eq T 
(THead (Flat Appl) u t0) (TSort n)))) (ex3_2 TList nat (\lambda (ws: 
TList).(\lambda (i: nat).(eq T (THead (Flat Appl) u t0) (THeads (Flat Appl) 
ws (TLRef i))))) (\lambda (ws: TList).(\lambda (_: nat).(nfs2 c0 ws))) 
(\lambda (_: TList).(\lambda (i: nat).(nf2 c0 (TLRef i)))))) (\lambda (H9: 
(ex3_2 T T (\lambda (w: T).(\lambda (u0: T).(eq T t0 (THead (Bind Abst) w 
u0)))) (\lambda (w: T).(\lambda (_: T).(nf2 c0 w))) (\lambda (w: T).(\lambda 
(u0: T).(nf2 (CHead c0 (Bind Abst) w) u0))))).(ex3_2_ind T T (\lambda (w: 
T).(\lambda (u0: T).(eq T t0 (THead (Bind Abst) w u0)))) (\lambda (w: 
T).(\lambda (_: T).(nf2 c0 w))) (\lambda (w: T).(\lambda (u0: T).(nf2 (CHead 
c0 (Bind Abst) w) u0))) (or3 (ex3_2 T T (\lambda (w: T).(\lambda (u0: T).(eq 
T (THead (Flat Appl) u t0) (THead (Bind Abst) w u0)))) (\lambda (w: 
T).(\lambda (_: T).(nf2 c0 w))) (\lambda (w: T).(\lambda (u0: T).(nf2 (CHead 
c0 (Bind Abst) w) u0)))) (ex nat (\lambda (n: nat).(eq T (THead (Flat Appl) u 
t0) (TSort n)))) (ex3_2 TList nat (\lambda (ws: TList).(\lambda (i: nat).(eq 
T (THead (Flat Appl) u t0) (THeads (Flat Appl) ws (TLRef i))))) (\lambda (ws: 
TList).(\lambda (_: nat).(nfs2 c0 ws))) (\lambda (_: TList).(\lambda (i: 
nat).(nf2 c0 (TLRef i)))))) (\lambda (x0: T).(\lambda (x1: T).(\lambda (H10: 
(eq T t0 (THead (Bind Abst) x0 x1))).(\lambda (_: (nf2 c0 x0)).(\lambda (_: 
(nf2 (CHead c0 (Bind Abst) x0) x1)).(let H13 \def (eq_ind T t0 (\lambda (t1: 
T).(nf2 c0 (THead (Flat Appl) u t1))) H4 (THead (Bind Abst) x0 x1) H10) in 
(let H14 \def (eq_ind T t0 (\lambda (t1: T).(arity g c0 t1 (AHead a1 a2))) H2 
(THead (Bind Abst) x0 x1) H10) in (eq_ind_r T (THead (Bind Abst) x0 x1) 
(\lambda (t1: T).(or3 (ex3_2 T T (\lambda (w: T).(\lambda (u0: T).(eq T 
(THead (Flat Appl) u t1) (THead (Bind Abst) w u0)))) (\lambda (w: T).(\lambda 
(_: T).(nf2 c0 w))) (\lambda (w: T).(\lambda (u0: T).(nf2 (CHead c0 (Bind 
Abst) w) u0)))) (ex nat (\lambda (n: nat).(eq T (THead (Flat Appl) u t1) 
(TSort n)))) (ex3_2 TList nat (\lambda (ws: TList).(\lambda (i: nat).(eq T 
(THead (Flat Appl) u t1) (THeads (Flat Appl) ws (TLRef i))))) (\lambda (ws: 
TList).(\lambda (_: nat).(nfs2 c0 ws))) (\lambda (_: TList).(\lambda (i: 
nat).(nf2 c0 (TLRef i))))))) (nf2_gen_beta c0 u x0 x1 H13 (or3 (ex3_2 T T 
(\lambda (w: T).(\lambda (u0: T).(eq T (THead (Flat Appl) u (THead (Bind 
Abst) x0 x1)) (THead (Bind Abst) w u0)))) (\lambda (w: T).(\lambda (_: 
T).(nf2 c0 w))) (\lambda (w: T).(\lambda (u0: T).(nf2 (CHead c0 (Bind Abst) 
w) u0)))) (ex nat (\lambda (n: nat).(eq T (THead (Flat Appl) u (THead (Bind 
Abst) x0 x1)) (TSort n)))) (ex3_2 TList nat (\lambda (ws: TList).(\lambda (i: 
nat).(eq T (THead (Flat Appl) u (THead (Bind Abst) x0 x1)) (THeads (Flat 
Appl) ws (TLRef i))))) (\lambda (ws: TList).(\lambda (_: nat).(nfs2 c0 ws))) 
(\lambda (_: TList).(\lambda (i: nat).(nf2 c0 (TLRef i))))))) t0 H10)))))))) 
H9)) (\lambda (H9: (ex nat (\lambda (n: nat).(eq T t0 (TSort n))))).(ex_ind 
nat (\lambda (n: nat).(eq T t0 (TSort n))) (or3 (ex3_2 T T (\lambda (w: 
T).(\lambda (u0: T).(eq T (THead (Flat Appl) u t0) (THead (Bind Abst) w 
u0)))) (\lambda (w: T).(\lambda (_: T).(nf2 c0 w))) (\lambda (w: T).(\lambda 
(u0: T).(nf2 (CHead c0 (Bind Abst) w) u0)))) (ex nat (\lambda (n: nat).(eq T 
(THead (Flat Appl) u t0) (TSort n)))) (ex3_2 TList nat (\lambda (ws: 
TList).(\lambda (i: nat).(eq T (THead (Flat Appl) u t0) (THeads (Flat Appl) 
ws (TLRef i))))) (\lambda (ws: TList).(\lambda (_: nat).(nfs2 c0 ws))) 
(\lambda (_: TList).(\lambda (i: nat).(nf2 c0 (TLRef i)))))) (\lambda (x: 
nat).(\lambda (H10: (eq T t0 (TSort x))).(let H11 \def (eq_ind T t0 (\lambda 
(t1: T).(nf2 c0 (THead (Flat Appl) u t1))) H4 (TSort x) H10) in (let H12 \def 
(eq_ind T t0 (\lambda (t1: T).(arity g c0 t1 (AHead a1 a2))) H2 (TSort x) 
H10) in (eq_ind_r T (TSort x) (\lambda (t1: T).(or3 (ex3_2 T T (\lambda (w: 
T).(\lambda (u0: T).(eq T (THead (Flat Appl) u t1) (THead (Bind Abst) w 
u0)))) (\lambda (w: T).(\lambda (_: T).(nf2 c0 w))) (\lambda (w: T).(\lambda 
(u0: T).(nf2 (CHead c0 (Bind Abst) w) u0)))) (ex nat (\lambda (n: nat).(eq T 
(THead (Flat Appl) u t1) (TSort n)))) (ex3_2 TList nat (\lambda (ws: 
TList).(\lambda (i: nat).(eq T (THead (Flat Appl) u t1) (THeads (Flat Appl) 
ws (TLRef i))))) (\lambda (ws: TList).(\lambda (_: nat).(nfs2 c0 ws))) 
(\lambda (_: TList).(\lambda (i: nat).(nf2 c0 (TLRef i))))))) (let H_x0 \def 
(leq_gen_head1 g a1 a2 (ASort O x) (arity_gen_sort g c0 x (AHead a1 a2) H12)) 
in (let H13 \def H_x0 in (ex3_2_ind A A (\lambda (a3: A).(\lambda (_: A).(leq 
g a1 a3))) (\lambda (_: A).(\lambda (a4: A).(leq g a2 a4))) (\lambda (a3: 
A).(\lambda (a4: A).(eq A (ASort O x) (AHead a3 a4)))) (or3 (ex3_2 T T 
(\lambda (w: T).(\lambda (u0: T).(eq T (THead (Flat Appl) u (TSort x)) (THead 
(Bind Abst) w u0)))) (\lambda (w: T).(\lambda (_: T).(nf2 c0 w))) (\lambda 
(w: T).(\lambda (u0: T).(nf2 (CHead c0 (Bind Abst) w) u0)))) (ex nat (\lambda 
(n: nat).(eq T (THead (Flat Appl) u (TSort x)) (TSort n)))) (ex3_2 TList nat 
(\lambda (ws: TList).(\lambda (i: nat).(eq T (THead (Flat Appl) u (TSort x)) 
(THeads (Flat Appl) ws (TLRef i))))) (\lambda (ws: TList).(\lambda (_: 
nat).(nfs2 c0 ws))) (\lambda (_: TList).(\lambda (i: nat).(nf2 c0 (TLRef 
i)))))) (\lambda (x0: A).(\lambda (x1: A).(\lambda (_: (leq g a1 
x0)).(\lambda (_: (leq g a2 x1)).(\lambda (H16: (eq A (ASort O x) (AHead x0 
x1))).(let H17 \def (eq_ind A (ASort O x) (\lambda (ee: A).(match ee in A 
return (\lambda (_: A).Prop) with [(ASort _ _) \Rightarrow True | (AHead _ _) 
\Rightarrow False])) I (AHead x0 x1) H16) in (False_ind (or3 (ex3_2 T T 
(\lambda (w: T).(\lambda (u0: T).(eq T (THead (Flat Appl) u (TSort x)) (THead 
(Bind Abst) w u0)))) (\lambda (w: T).(\lambda (_: T).(nf2 c0 w))) (\lambda 
(w: T).(\lambda (u0: T).(nf2 (CHead c0 (Bind Abst) w) u0)))) (ex nat (\lambda 
(n: nat).(eq T (THead (Flat Appl) u (TSort x)) (TSort n)))) (ex3_2 TList nat 
(\lambda (ws: TList).(\lambda (i: nat).(eq T (THead (Flat Appl) u (TSort x)) 
(THeads (Flat Appl) ws (TLRef i))))) (\lambda (ws: TList).(\lambda (_: 
nat).(nfs2 c0 ws))) (\lambda (_: TList).(\lambda (i: nat).(nf2 c0 (TLRef 
i)))))) H17))))))) H13))) t0 H10))))) H9)) (\lambda (H9: (ex3_2 TList nat 
(\lambda (ws: TList).(\lambda (i: nat).(eq T t0 (THeads (Flat Appl) ws (TLRef 
i))))) (\lambda (ws: TList).(\lambda (_: nat).(nfs2 c0 ws))) (\lambda (_: 
TList).(\lambda (i: nat).(nf2 c0 (TLRef i)))))).(ex3_2_ind TList nat (\lambda 
(ws: TList).(\lambda (i: nat).(eq T t0 (THeads (Flat Appl) ws (TLRef i))))) 
(\lambda (ws: TList).(\lambda (_: nat).(nfs2 c0 ws))) (\lambda (_: 
TList).(\lambda (i: nat).(nf2 c0 (TLRef i)))) (or3 (ex3_2 T T (\lambda (w: 
T).(\lambda (u0: T).(eq T (THead (Flat Appl) u t0) (THead (Bind Abst) w 
u0)))) (\lambda (w: T).(\lambda (_: T).(nf2 c0 w))) (\lambda (w: T).(\lambda 
(u0: T).(nf2 (CHead c0 (Bind Abst) w) u0)))) (ex nat (\lambda (n: nat).(eq T 
(THead (Flat Appl) u t0) (TSort n)))) (ex3_2 TList nat (\lambda (ws: 
TList).(\lambda (i: nat).(eq T (THead (Flat Appl) u t0) (THeads (Flat Appl) 
ws (TLRef i))))) (\lambda (ws: TList).(\lambda (_: nat).(nfs2 c0 ws))) 
(\lambda (_: TList).(\lambda (i: nat).(nf2 c0 (TLRef i)))))) (\lambda (x0: 
TList).(\lambda (x1: nat).(\lambda (H10: (eq T t0 (THeads (Flat Appl) x0 
(TLRef x1)))).(\lambda (H11: (nfs2 c0 x0)).(\lambda (H12: (nf2 c0 (TLRef 
x1))).(let H13 \def (eq_ind T t0 (\lambda (t1: T).(nf2 c0 (THead (Flat Appl) 
u t1))) H4 (THeads (Flat Appl) x0 (TLRef x1)) H10) in (let H14 \def (eq_ind T 
t0 (\lambda (t1: T).(arity g c0 t1 (AHead a1 a2))) H2 (THeads (Flat Appl) x0 
(TLRef x1)) H10) in (eq_ind_r T (THeads (Flat Appl) x0 (TLRef x1)) (\lambda 
(t1: T).(or3 (ex3_2 T T (\lambda (w: T).(\lambda (u0: T).(eq T (THead (Flat 
Appl) u t1) (THead (Bind Abst) w u0)))) (\lambda (w: T).(\lambda (_: T).(nf2 
c0 w))) (\lambda (w: T).(\lambda (u0: T).(nf2 (CHead c0 (Bind Abst) w) u0)))) 
(ex nat (\lambda (n: nat).(eq T (THead (Flat Appl) u t1) (TSort n)))) (ex3_2 
TList nat (\lambda (ws: TList).(\lambda (i: nat).(eq T (THead (Flat Appl) u 
t1) (THeads (Flat Appl) ws (TLRef i))))) (\lambda (ws: TList).(\lambda (_: 
nat).(nfs2 c0 ws))) (\lambda (_: TList).(\lambda (i: nat).(nf2 c0 (TLRef 
i))))))) (or3_intro2 (ex3_2 T T (\lambda (w: T).(\lambda (u0: T).(eq T (THead 
(Flat Appl) u (THeads (Flat Appl) x0 (TLRef x1))) (THead (Bind Abst) w u0)))) 
(\lambda (w: T).(\lambda (_: T).(nf2 c0 w))) (\lambda (w: T).(\lambda (u0: 
T).(nf2 (CHead c0 (Bind Abst) w) u0)))) (ex nat (\lambda (n: nat).(eq T 
(THead (Flat Appl) u (THeads (Flat Appl) x0 (TLRef x1))) (TSort n)))) (ex3_2 
TList nat (\lambda (ws: TList).(\lambda (i: nat).(eq T (THead (Flat Appl) u 
(THeads (Flat Appl) x0 (TLRef x1))) (THeads (Flat Appl) ws (TLRef i))))) 
(\lambda (ws: TList).(\lambda (_: nat).(nfs2 c0 ws))) (\lambda (_: 
TList).(\lambda (i: nat).(nf2 c0 (TLRef i))))) (ex3_2_intro TList nat 
(\lambda (ws: TList).(\lambda (i: nat).(eq T (THead (Flat Appl) u (THeads 
(Flat Appl) x0 (TLRef x1))) (THeads (Flat Appl) ws (TLRef i))))) (\lambda 
(ws: TList).(\lambda (_: nat).(nfs2 c0 ws))) (\lambda (_: TList).(\lambda (i: 
nat).(nf2 c0 (TLRef i)))) (TCons u x0) x1 (refl_equal T (THead (Flat Appl) u 
(THeads (Flat Appl) x0 (TLRef x1)))) (conj (nf2 c0 u) (nfs2 c0 x0) H6 H11) 
H12)) t0 H10)))))))) H9)) H8))))) H5)))))))))))) (\lambda (c0: C).(\lambda 
(u: T).(\lambda (a0: A).(\lambda (_: (arity g c0 u (asucc g a0))).(\lambda 
(_: (((nf2 c0 u) \to (or3 (ex3_2 T T (\lambda (w: T).(\lambda (u0: T).(eq T u 
(THead (Bind Abst) w u0)))) (\lambda (w: T).(\lambda (_: T).(nf2 c0 w))) 
(\lambda (w: T).(\lambda (u0: T).(nf2 (CHead c0 (Bind Abst) w) u0)))) (ex nat 
(\lambda (n: nat).(eq T u (TSort n)))) (ex3_2 TList nat (\lambda (ws: 
TList).(\lambda (i: nat).(eq T u (THeads (Flat Appl) ws (TLRef i))))) 
(\lambda (ws: TList).(\lambda (_: nat).(nfs2 c0 ws))) (\lambda (_: 
TList).(\lambda (i: nat).(nf2 c0 (TLRef i))))))))).(\lambda (t0: T).(\lambda 
(_: (arity g c0 t0 a0)).(\lambda (_: (((nf2 c0 t0) \to (or3 (ex3_2 T T 
(\lambda (w: T).(\lambda (u0: T).(eq T t0 (THead (Bind Abst) w u0)))) 
(\lambda (w: T).(\lambda (_: T).(nf2 c0 w))) (\lambda (w: T).(\lambda (u0: 
T).(nf2 (CHead c0 (Bind Abst) w) u0)))) (ex nat (\lambda (n: nat).(eq T t0 
(TSort n)))) (ex3_2 TList nat (\lambda (ws: TList).(\lambda (i: nat).(eq T t0 
(THeads (Flat Appl) ws (TLRef i))))) (\lambda (ws: TList).(\lambda (_: 
nat).(nfs2 c0 ws))) (\lambda (_: TList).(\lambda (i: nat).(nf2 c0 (TLRef 
i))))))))).(\lambda (H4: (nf2 c0 (THead (Flat Cast) u t0))).(nf2_gen_cast c0 
u t0 H4 (or3 (ex3_2 T T (\lambda (w: T).(\lambda (u0: T).(eq T (THead (Flat 
Cast) u t0) (THead (Bind Abst) w u0)))) (\lambda (w: T).(\lambda (_: T).(nf2 
c0 w))) (\lambda (w: T).(\lambda (u0: T).(nf2 (CHead c0 (Bind Abst) w) u0)))) 
(ex nat (\lambda (n: nat).(eq T (THead (Flat Cast) u t0) (TSort n)))) (ex3_2 
TList nat (\lambda (ws: TList).(\lambda (i: nat).(eq T (THead (Flat Cast) u 
t0) (THeads (Flat Appl) ws (TLRef i))))) (\lambda (ws: TList).(\lambda (_: 
nat).(nfs2 c0 ws))) (\lambda (_: TList).(\lambda (i: nat).(nf2 c0 (TLRef 
i)))))))))))))))) (\lambda (c0: C).(\lambda (t0: T).(\lambda (a1: A).(\lambda 
(_: (arity g c0 t0 a1)).(\lambda (H1: (((nf2 c0 t0) \to (or3 (ex3_2 T T 
(\lambda (w: T).(\lambda (u: T).(eq T t0 (THead (Bind Abst) w u)))) (\lambda 
(w: T).(\lambda (_: T).(nf2 c0 w))) (\lambda (w: T).(\lambda (u: T).(nf2 
(CHead c0 (Bind Abst) w) u)))) (ex nat (\lambda (n: nat).(eq T t0 (TSort 
n)))) (ex3_2 TList nat (\lambda (ws: TList).(\lambda (i: nat).(eq T t0 
(THeads (Flat Appl) ws (TLRef i))))) (\lambda (ws: TList).(\lambda (_: 
nat).(nfs2 c0 ws))) (\lambda (_: TList).(\lambda (i: nat).(nf2 c0 (TLRef 
i))))))))).(\lambda (a2: A).(\lambda (_: (leq g a1 a2)).(\lambda (H3: (nf2 c0 
t0)).(let H_x \def (H1 H3) in (let H4 \def H_x in (or3_ind (ex3_2 T T 
(\lambda (w: T).(\lambda (u: T).(eq T t0 (THead (Bind Abst) w u)))) (\lambda 
(w: T).(\lambda (_: T).(nf2 c0 w))) (\lambda (w: T).(\lambda (u: T).(nf2 
(CHead c0 (Bind Abst) w) u)))) (ex nat (\lambda (n: nat).(eq T t0 (TSort 
n)))) (ex3_2 TList nat (\lambda (ws: TList).(\lambda (i: nat).(eq T t0 
(THeads (Flat Appl) ws (TLRef i))))) (\lambda (ws: TList).(\lambda (_: 
nat).(nfs2 c0 ws))) (\lambda (_: TList).(\lambda (i: nat).(nf2 c0 (TLRef 
i))))) (or3 (ex3_2 T T (\lambda (w: T).(\lambda (u: T).(eq T t0 (THead (Bind 
Abst) w u)))) (\lambda (w: T).(\lambda (_: T).(nf2 c0 w))) (\lambda (w: 
T).(\lambda (u: T).(nf2 (CHead c0 (Bind Abst) w) u)))) (ex nat (\lambda (n: 
nat).(eq T t0 (TSort n)))) (ex3_2 TList nat (\lambda (ws: TList).(\lambda (i: 
nat).(eq T t0 (THeads (Flat Appl) ws (TLRef i))))) (\lambda (ws: 
TList).(\lambda (_: nat).(nfs2 c0 ws))) (\lambda (_: TList).(\lambda (i: 
nat).(nf2 c0 (TLRef i)))))) (\lambda (H5: (ex3_2 T T (\lambda (w: T).(\lambda 
(u: T).(eq T t0 (THead (Bind Abst) w u)))) (\lambda (w: T).(\lambda (_: 
T).(nf2 c0 w))) (\lambda (w: T).(\lambda (u: T).(nf2 (CHead c0 (Bind Abst) w) 
u))))).(ex3_2_ind T T (\lambda (w: T).(\lambda (u: T).(eq T t0 (THead (Bind 
Abst) w u)))) (\lambda (w: T).(\lambda (_: T).(nf2 c0 w))) (\lambda (w: 
T).(\lambda (u: T).(nf2 (CHead c0 (Bind Abst) w) u))) (or3 (ex3_2 T T 
(\lambda (w: T).(\lambda (u: T).(eq T t0 (THead (Bind Abst) w u)))) (\lambda 
(w: T).(\lambda (_: T).(nf2 c0 w))) (\lambda (w: T).(\lambda (u: T).(nf2 
(CHead c0 (Bind Abst) w) u)))) (ex nat (\lambda (n: nat).(eq T t0 (TSort 
n)))) (ex3_2 TList nat (\lambda (ws: TList).(\lambda (i: nat).(eq T t0 
(THeads (Flat Appl) ws (TLRef i))))) (\lambda (ws: TList).(\lambda (_: 
nat).(nfs2 c0 ws))) (\lambda (_: TList).(\lambda (i: nat).(nf2 c0 (TLRef 
i)))))) (\lambda (x0: T).(\lambda (x1: T).(\lambda (H6: (eq T t0 (THead (Bind 
Abst) x0 x1))).(\lambda (H7: (nf2 c0 x0)).(\lambda (H8: (nf2 (CHead c0 (Bind 
Abst) x0) x1)).(eq_ind_r T (THead (Bind Abst) x0 x1) (\lambda (t1: T).(or3 
(ex3_2 T T (\lambda (w: T).(\lambda (u: T).(eq T t1 (THead (Bind Abst) w 
u)))) (\lambda (w: T).(\lambda (_: T).(nf2 c0 w))) (\lambda (w: T).(\lambda 
(u: T).(nf2 (CHead c0 (Bind Abst) w) u)))) (ex nat (\lambda (n: nat).(eq T t1 
(TSort n)))) (ex3_2 TList nat (\lambda (ws: TList).(\lambda (i: nat).(eq T t1 
(THeads (Flat Appl) ws (TLRef i))))) (\lambda (ws: TList).(\lambda (_: 
nat).(nfs2 c0 ws))) (\lambda (_: TList).(\lambda (i: nat).(nf2 c0 (TLRef 
i))))))) (or3_intro0 (ex3_2 T T (\lambda (w: T).(\lambda (u: T).(eq T (THead 
(Bind Abst) x0 x1) (THead (Bind Abst) w u)))) (\lambda (w: T).(\lambda (_: 
T).(nf2 c0 w))) (\lambda (w: T).(\lambda (u: T).(nf2 (CHead c0 (Bind Abst) w) 
u)))) (ex nat (\lambda (n: nat).(eq T (THead (Bind Abst) x0 x1) (TSort n)))) 
(ex3_2 TList nat (\lambda (ws: TList).(\lambda (i: nat).(eq T (THead (Bind 
Abst) x0 x1) (THeads (Flat Appl) ws (TLRef i))))) (\lambda (ws: 
TList).(\lambda (_: nat).(nfs2 c0 ws))) (\lambda (_: TList).(\lambda (i: 
nat).(nf2 c0 (TLRef i))))) (ex3_2_intro T T (\lambda (w: T).(\lambda (u: 
T).(eq T (THead (Bind Abst) x0 x1) (THead (Bind Abst) w u)))) (\lambda (w: 
T).(\lambda (_: T).(nf2 c0 w))) (\lambda (w: T).(\lambda (u: T).(nf2 (CHead 
c0 (Bind Abst) w) u))) x0 x1 (refl_equal T (THead (Bind Abst) x0 x1)) H7 H8)) 
t0 H6)))))) H5)) (\lambda (H5: (ex nat (\lambda (n: nat).(eq T t0 (TSort 
n))))).(ex_ind nat (\lambda (n: nat).(eq T t0 (TSort n))) (or3 (ex3_2 T T 
(\lambda (w: T).(\lambda (u: T).(eq T t0 (THead (Bind Abst) w u)))) (\lambda 
(w: T).(\lambda (_: T).(nf2 c0 w))) (\lambda (w: T).(\lambda (u: T).(nf2 
(CHead c0 (Bind Abst) w) u)))) (ex nat (\lambda (n: nat).(eq T t0 (TSort 
n)))) (ex3_2 TList nat (\lambda (ws: TList).(\lambda (i: nat).(eq T t0 
(THeads (Flat Appl) ws (TLRef i))))) (\lambda (ws: TList).(\lambda (_: 
nat).(nfs2 c0 ws))) (\lambda (_: TList).(\lambda (i: nat).(nf2 c0 (TLRef 
i)))))) (\lambda (x: nat).(\lambda (H6: (eq T t0 (TSort x))).(eq_ind_r T 
(TSort x) (\lambda (t1: T).(or3 (ex3_2 T T (\lambda (w: T).(\lambda (u: 
T).(eq T t1 (THead (Bind Abst) w u)))) (\lambda (w: T).(\lambda (_: T).(nf2 
c0 w))) (\lambda (w: T).(\lambda (u: T).(nf2 (CHead c0 (Bind Abst) w) u)))) 
(ex nat (\lambda (n: nat).(eq T t1 (TSort n)))) (ex3_2 TList nat (\lambda 
(ws: TList).(\lambda (i: nat).(eq T t1 (THeads (Flat Appl) ws (TLRef i))))) 
(\lambda (ws: TList).(\lambda (_: nat).(nfs2 c0 ws))) (\lambda (_: 
TList).(\lambda (i: nat).(nf2 c0 (TLRef i))))))) (or3_intro1 (ex3_2 T T 
(\lambda (w: T).(\lambda (u: T).(eq T (TSort x) (THead (Bind Abst) w u)))) 
(\lambda (w: T).(\lambda (_: T).(nf2 c0 w))) (\lambda (w: T).(\lambda (u: 
T).(nf2 (CHead c0 (Bind Abst) w) u)))) (ex nat (\lambda (n: nat).(eq T (TSort 
x) (TSort n)))) (ex3_2 TList nat (\lambda (ws: TList).(\lambda (i: nat).(eq T 
(TSort x) (THeads (Flat Appl) ws (TLRef i))))) (\lambda (ws: TList).(\lambda 
(_: nat).(nfs2 c0 ws))) (\lambda (_: TList).(\lambda (i: nat).(nf2 c0 (TLRef 
i))))) (ex_intro nat (\lambda (n: nat).(eq T (TSort x) (TSort n))) x 
(refl_equal T (TSort x)))) t0 H6))) H5)) (\lambda (H5: (ex3_2 TList nat 
(\lambda (ws: TList).(\lambda (i: nat).(eq T t0 (THeads (Flat Appl) ws (TLRef 
i))))) (\lambda (ws: TList).(\lambda (_: nat).(nfs2 c0 ws))) (\lambda (_: 
TList).(\lambda (i: nat).(nf2 c0 (TLRef i)))))).(ex3_2_ind TList nat (\lambda 
(ws: TList).(\lambda (i: nat).(eq T t0 (THeads (Flat Appl) ws (TLRef i))))) 
(\lambda (ws: TList).(\lambda (_: nat).(nfs2 c0 ws))) (\lambda (_: 
TList).(\lambda (i: nat).(nf2 c0 (TLRef i)))) (or3 (ex3_2 T T (\lambda (w: 
T).(\lambda (u: T).(eq T t0 (THead (Bind Abst) w u)))) (\lambda (w: 
T).(\lambda (_: T).(nf2 c0 w))) (\lambda (w: T).(\lambda (u: T).(nf2 (CHead 
c0 (Bind Abst) w) u)))) (ex nat (\lambda (n: nat).(eq T t0 (TSort n)))) 
(ex3_2 TList nat (\lambda (ws: TList).(\lambda (i: nat).(eq T t0 (THeads 
(Flat Appl) ws (TLRef i))))) (\lambda (ws: TList).(\lambda (_: nat).(nfs2 c0 
ws))) (\lambda (_: TList).(\lambda (i: nat).(nf2 c0 (TLRef i)))))) (\lambda 
(x0: TList).(\lambda (x1: nat).(\lambda (H6: (eq T t0 (THeads (Flat Appl) x0 
(TLRef x1)))).(\lambda (H7: (nfs2 c0 x0)).(\lambda (H8: (nf2 c0 (TLRef 
x1))).(eq_ind_r T (THeads (Flat Appl) x0 (TLRef x1)) (\lambda (t1: T).(or3 
(ex3_2 T T (\lambda (w: T).(\lambda (u: T).(eq T t1 (THead (Bind Abst) w 
u)))) (\lambda (w: T).(\lambda (_: T).(nf2 c0 w))) (\lambda (w: T).(\lambda 
(u: T).(nf2 (CHead c0 (Bind Abst) w) u)))) (ex nat (\lambda (n: nat).(eq T t1 
(TSort n)))) (ex3_2 TList nat (\lambda (ws: TList).(\lambda (i: nat).(eq T t1 
(THeads (Flat Appl) ws (TLRef i))))) (\lambda (ws: TList).(\lambda (_: 
nat).(nfs2 c0 ws))) (\lambda (_: TList).(\lambda (i: nat).(nf2 c0 (TLRef 
i))))))) (or3_intro2 (ex3_2 T T (\lambda (w: T).(\lambda (u: T).(eq T (THeads 
(Flat Appl) x0 (TLRef x1)) (THead (Bind Abst) w u)))) (\lambda (w: 
T).(\lambda (_: T).(nf2 c0 w))) (\lambda (w: T).(\lambda (u: T).(nf2 (CHead 
c0 (Bind Abst) w) u)))) (ex nat (\lambda (n: nat).(eq T (THeads (Flat Appl) 
x0 (TLRef x1)) (TSort n)))) (ex3_2 TList nat (\lambda (ws: TList).(\lambda 
(i: nat).(eq T (THeads (Flat Appl) x0 (TLRef x1)) (THeads (Flat Appl) ws 
(TLRef i))))) (\lambda (ws: TList).(\lambda (_: nat).(nfs2 c0 ws))) (\lambda 
(_: TList).(\lambda (i: nat).(nf2 c0 (TLRef i))))) (ex3_2_intro TList nat 
(\lambda (ws: TList).(\lambda (i: nat).(eq T (THeads (Flat Appl) x0 (TLRef 
x1)) (THeads (Flat Appl) ws (TLRef i))))) (\lambda (ws: TList).(\lambda (_: 
nat).(nfs2 c0 ws))) (\lambda (_: TList).(\lambda (i: nat).(nf2 c0 (TLRef 
i)))) x0 x1 (refl_equal T (THeads (Flat Appl) x0 (TLRef x1))) H7 H8)) t0 
H6)))))) H5)) H4))))))))))) c t a H))))).
(* COMMENTS
Initial nodes: 9193
END *)

