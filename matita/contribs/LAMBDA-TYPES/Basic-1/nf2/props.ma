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

include "Basic-1/nf2/defs.ma".

include "Basic-1/pr2/fwd.ma".

theorem nf2_sort:
 \forall (c: C).(\forall (n: nat).(nf2 c (TSort n)))
\def
 \lambda (c: C).(\lambda (n: nat).(\lambda (t2: T).(\lambda (H: (pr2 c (TSort 
n) t2)).(eq_ind_r T (TSort n) (\lambda (t: T).(eq T (TSort n) t)) (refl_equal 
T (TSort n)) t2 (pr2_gen_sort c t2 n H))))).
(* COMMENTS
Initial nodes: 55
END *)

theorem nf2_csort_lref:
 \forall (n: nat).(\forall (i: nat).(nf2 (CSort n) (TLRef i)))
\def
 \lambda (n: nat).(\lambda (i: nat).(\lambda (t2: T).(\lambda (H: (pr2 (CSort 
n) (TLRef i) t2)).(let H0 \def (pr2_gen_lref (CSort n) t2 i H) in (or_ind (eq 
T t2 (TLRef i)) (ex2_2 C T (\lambda (d: C).(\lambda (u: T).(getl i (CSort n) 
(CHead d (Bind Abbr) u)))) (\lambda (_: C).(\lambda (u: T).(eq T t2 (lift (S 
i) O u))))) (eq T (TLRef i) t2) (\lambda (H1: (eq T t2 (TLRef i))).(eq_ind_r 
T (TLRef i) (\lambda (t: T).(eq T (TLRef i) t)) (refl_equal T (TLRef i)) t2 
H1)) (\lambda (H1: (ex2_2 C T (\lambda (d: C).(\lambda (u: T).(getl i (CSort 
n) (CHead d (Bind Abbr) u)))) (\lambda (_: C).(\lambda (u: T).(eq T t2 (lift 
(S i) O u)))))).(ex2_2_ind C T (\lambda (d: C).(\lambda (u: T).(getl i (CSort 
n) (CHead d (Bind Abbr) u)))) (\lambda (_: C).(\lambda (u: T).(eq T t2 (lift 
(S i) O u)))) (eq T (TLRef i) t2) (\lambda (x0: C).(\lambda (x1: T).(\lambda 
(H2: (getl i (CSort n) (CHead x0 (Bind Abbr) x1))).(\lambda (H3: (eq T t2 
(lift (S i) O x1))).(eq_ind_r T (lift (S i) O x1) (\lambda (t: T).(eq T 
(TLRef i) t)) (getl_gen_sort n i (CHead x0 (Bind Abbr) x1) H2 (eq T (TLRef i) 
(lift (S i) O x1))) t2 H3))))) H1)) H0))))).
(* COMMENTS
Initial nodes: 355
END *)

theorem nf2_abst:
 \forall (c: C).(\forall (u: T).((nf2 c u) \to (\forall (b: B).(\forall (v: 
T).(\forall (t: T).((nf2 (CHead c (Bind b) v) t) \to (nf2 c (THead (Bind 
Abst) u t))))))))
\def
 \lambda (c: C).(\lambda (u: T).(\lambda (H: ((\forall (t2: T).((pr2 c u t2) 
\to (eq T u t2))))).(\lambda (b: B).(\lambda (v: T).(\lambda (t: T).(\lambda 
(H0: ((\forall (t2: T).((pr2 (CHead c (Bind b) v) t t2) \to (eq T t 
t2))))).(\lambda (t2: T).(\lambda (H1: (pr2 c (THead (Bind Abst) u t) 
t2)).(let H2 \def (pr2_gen_abst c u t t2 H1) in (ex3_2_ind T T (\lambda (u2: 
T).(\lambda (t3: T).(eq T t2 (THead (Bind Abst) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c u u2))) (\lambda (_: T).(\lambda (t3: T).(\forall 
(b0: B).(\forall (u0: T).(pr2 (CHead c (Bind b0) u0) t t3))))) (eq T (THead 
(Bind Abst) u t) t2) (\lambda (x0: T).(\lambda (x1: T).(\lambda (H3: (eq T t2 
(THead (Bind Abst) x0 x1))).(\lambda (H4: (pr2 c u x0)).(\lambda (H5: 
((\forall (b0: B).(\forall (u0: T).(pr2 (CHead c (Bind b0) u0) t 
x1))))).(eq_ind_r T (THead (Bind Abst) x0 x1) (\lambda (t0: T).(eq T (THead 
(Bind Abst) u t) t0)) (f_equal3 K T T T THead (Bind Abst) (Bind Abst) u x0 t 
x1 (refl_equal K (Bind Abst)) (H x0 H4) (H0 x1 (H5 b v))) t2 H3)))))) 
H2)))))))))).
(* COMMENTS
Initial nodes: 299
END *)

theorem nf2_abst_shift:
 \forall (c: C).(\forall (u: T).((nf2 c u) \to (\forall (t: T).((nf2 (CHead c 
(Bind Abst) u) t) \to (nf2 c (THead (Bind Abst) u t))))))
\def
 \lambda (c: C).(\lambda (u: T).(\lambda (H: ((\forall (t2: T).((pr2 c u t2) 
\to (eq T u t2))))).(\lambda (t: T).(\lambda (H0: ((\forall (t2: T).((pr2 
(CHead c (Bind Abst) u) t t2) \to (eq T t t2))))).(\lambda (t2: T).(\lambda 
(H1: (pr2 c (THead (Bind Abst) u t) t2)).(let H2 \def (pr2_gen_abst c u t t2 
H1) in (ex3_2_ind T T (\lambda (u2: T).(\lambda (t3: T).(eq T t2 (THead (Bind 
Abst) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c u u2))) (\lambda (_: 
T).(\lambda (t3: T).(\forall (b: B).(\forall (u0: T).(pr2 (CHead c (Bind b) 
u0) t t3))))) (eq T (THead (Bind Abst) u t) t2) (\lambda (x0: T).(\lambda 
(x1: T).(\lambda (H3: (eq T t2 (THead (Bind Abst) x0 x1))).(\lambda (H4: (pr2 
c u x0)).(\lambda (H5: ((\forall (b: B).(\forall (u0: T).(pr2 (CHead c (Bind 
b) u0) t x1))))).(eq_ind_r T (THead (Bind Abst) x0 x1) (\lambda (t0: T).(eq T 
(THead (Bind Abst) u t) t0)) (f_equal3 K T T T THead (Bind Abst) (Bind Abst) 
u x0 t x1 (refl_equal K (Bind Abst)) (H x0 H4) (H0 x1 (H5 Abst u))) t2 
H3)))))) H2)))))))).
(* COMMENTS
Initial nodes: 295
END *)

theorem nfs2_tapp:
 \forall (c: C).(\forall (t: T).(\forall (ts: TList).((nfs2 c (TApp ts t)) 
\to (land (nfs2 c ts) (nf2 c t)))))
\def
 \lambda (c: C).(\lambda (t: T).(\lambda (ts: TList).(TList_ind (\lambda (t0: 
TList).((nfs2 c (TApp t0 t)) \to (land (nfs2 c t0) (nf2 c t)))) (\lambda (H: 
(land (nf2 c t) True)).(let H0 \def H in (land_ind (nf2 c t) True (land True 
(nf2 c t)) (\lambda (H1: (nf2 c t)).(\lambda (_: True).(conj True (nf2 c t) I 
H1))) H0))) (\lambda (t0: T).(\lambda (t1: TList).(\lambda (H: (((nfs2 c 
(TApp t1 t)) \to (land (nfs2 c t1) (nf2 c t))))).(\lambda (H0: (land (nf2 c 
t0) (nfs2 c (TApp t1 t)))).(let H1 \def H0 in (land_ind (nf2 c t0) (nfs2 c 
(TApp t1 t)) (land (land (nf2 c t0) (nfs2 c t1)) (nf2 c t)) (\lambda (H2: 
(nf2 c t0)).(\lambda (H3: (nfs2 c (TApp t1 t))).(let H_x \def (H H3) in (let 
H4 \def H_x in (land_ind (nfs2 c t1) (nf2 c t) (land (land (nf2 c t0) (nfs2 c 
t1)) (nf2 c t)) (\lambda (H5: (nfs2 c t1)).(\lambda (H6: (nf2 c t)).(conj 
(land (nf2 c t0) (nfs2 c t1)) (nf2 c t) (conj (nf2 c t0) (nfs2 c t1) H2 H5) 
H6))) H4))))) H1)))))) ts))).
(* COMMENTS
Initial nodes: 295
END *)

theorem nf2_appls_lref:
 \forall (c: C).(\forall (i: nat).((nf2 c (TLRef i)) \to (\forall (vs: 
TList).((nfs2 c vs) \to (nf2 c (THeads (Flat Appl) vs (TLRef i)))))))
\def
 \lambda (c: C).(\lambda (i: nat).(\lambda (H: (nf2 c (TLRef i))).(\lambda 
(vs: TList).(TList_ind (\lambda (t: TList).((nfs2 c t) \to (nf2 c (THeads 
(Flat Appl) t (TLRef i))))) (\lambda (_: True).H) (\lambda (t: T).(\lambda 
(t0: TList).(\lambda (H0: (((nfs2 c t0) \to (nf2 c (THeads (Flat Appl) t0 
(TLRef i)))))).(\lambda (H1: (land (nf2 c t) (nfs2 c t0))).(let H2 \def H1 in 
(land_ind (nf2 c t) (nfs2 c t0) (nf2 c (THead (Flat Appl) t (THeads (Flat 
Appl) t0 (TLRef i)))) (\lambda (H3: (nf2 c t)).(\lambda (H4: (nfs2 c 
t0)).(let H_y \def (H0 H4) in (\lambda (t2: T).(\lambda (H5: (pr2 c (THead 
(Flat Appl) t (THeads (Flat Appl) t0 (TLRef i))) t2)).(let H6 \def 
(pr2_gen_appl c t (THeads (Flat Appl) t0 (TLRef i)) t2 H5) in (or3_ind (ex3_2 
T T (\lambda (u2: T).(\lambda (t3: T).(eq T t2 (THead (Flat Appl) u2 t3)))) 
(\lambda (u2: T).(\lambda (_: T).(pr2 c t u2))) (\lambda (_: T).(\lambda (t3: 
T).(pr2 c (THeads (Flat Appl) t0 (TLRef i)) t3)))) (ex4_4 T T T T (\lambda 
(y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(eq T (THeads (Flat 
Appl) t0 (TLRef i)) (THead (Bind Abst) y1 z1)))))) (\lambda (_: T).(\lambda 
(_: T).(\lambda (u2: T).(\lambda (t3: T).(eq T t2 (THead (Bind Abbr) u2 
t3)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: 
T).(pr2 c t u2))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda 
(t3: T).(\forall (b: B).(\forall (u: T).(pr2 (CHead c (Bind b) u) z1 
t3)))))))) (ex6_6 B T T T T T (\lambda (b: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(not (eq B b Abst)))))))) 
(\lambda (b: B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda 
(_: T).(\lambda (_: T).(eq T (THeads (Flat Appl) t0 (TLRef i)) (THead (Bind 
b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda 
(z2: T).(\lambda (u2: T).(\lambda (y2: T).(eq T t2 (THead (Bind b) y2 (THead 
(Flat Appl) (lift (S O) O u2) z2))))))))) (\lambda (_: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c t 
u2))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (y2: T).(pr2 c y1 y2))))))) (\lambda (b: 
B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: T).(\lambda (_: T).(\lambda 
(y2: T).(pr2 (CHead c (Bind b) y2) z1 z2)))))))) (eq T (THead (Flat Appl) t 
(THeads (Flat Appl) t0 (TLRef i))) t2) (\lambda (H7: (ex3_2 T T (\lambda (u2: 
T).(\lambda (t3: T).(eq T t2 (THead (Flat Appl) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c t u2))) (\lambda (_: T).(\lambda (t3: T).(pr2 c 
(THeads (Flat Appl) t0 (TLRef i)) t3))))).(ex3_2_ind T T (\lambda (u2: 
T).(\lambda (t3: T).(eq T t2 (THead (Flat Appl) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c t u2))) (\lambda (_: T).(\lambda (t3: T).(pr2 c 
(THeads (Flat Appl) t0 (TLRef i)) t3))) (eq T (THead (Flat Appl) t (THeads 
(Flat Appl) t0 (TLRef i))) t2) (\lambda (x0: T).(\lambda (x1: T).(\lambda 
(H8: (eq T t2 (THead (Flat Appl) x0 x1))).(\lambda (H9: (pr2 c t 
x0)).(\lambda (H10: (pr2 c (THeads (Flat Appl) t0 (TLRef i)) x1)).(eq_ind_r T 
(THead (Flat Appl) x0 x1) (\lambda (t1: T).(eq T (THead (Flat Appl) t (THeads 
(Flat Appl) t0 (TLRef i))) t1)) (let H11 \def (eq_ind_r T x1 (\lambda (t1: 
T).(pr2 c (THeads (Flat Appl) t0 (TLRef i)) t1)) H10 (THeads (Flat Appl) t0 
(TLRef i)) (H_y x1 H10)) in (eq_ind T (THeads (Flat Appl) t0 (TLRef i)) 
(\lambda (t1: T).(eq T (THead (Flat Appl) t (THeads (Flat Appl) t0 (TLRef 
i))) (THead (Flat Appl) x0 t1))) (let H12 \def (eq_ind_r T x0 (\lambda (t1: 
T).(pr2 c t t1)) H9 t (H3 x0 H9)) in (eq_ind T t (\lambda (t1: T).(eq T 
(THead (Flat Appl) t (THeads (Flat Appl) t0 (TLRef i))) (THead (Flat Appl) t1 
(THeads (Flat Appl) t0 (TLRef i))))) (refl_equal T (THead (Flat Appl) t 
(THeads (Flat Appl) t0 (TLRef i)))) x0 (H3 x0 H9))) x1 (H_y x1 H10))) t2 
H8)))))) H7)) (\lambda (H7: (ex4_4 T T T T (\lambda (y1: T).(\lambda (z1: 
T).(\lambda (_: T).(\lambda (_: T).(eq T (THeads (Flat Appl) t0 (TLRef i)) 
(THead (Bind Abst) y1 z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (t3: T).(eq T t2 (THead (Bind Abbr) u2 t3)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c t u2))))) (\lambda 
(_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t3: T).(\forall (b: 
B).(\forall (u: T).(pr2 (CHead c (Bind b) u) z1 t3))))))))).(ex4_4_ind T T T 
T (\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(eq T 
(THeads (Flat Appl) t0 (TLRef i)) (THead (Bind Abst) y1 z1)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t3: T).(eq T t2 (THead (Bind 
Abbr) u2 t3)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(_: T).(pr2 c t u2))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (t3: T).(\forall (b: B).(\forall (u: T).(pr2 (CHead c (Bind b) u) 
z1 t3))))))) (eq T (THead (Flat Appl) t (THeads (Flat Appl) t0 (TLRef i))) 
t2) (\lambda (x0: T).(\lambda (x1: T).(\lambda (x2: T).(\lambda (x3: 
T).(\lambda (H8: (eq T (THeads (Flat Appl) t0 (TLRef i)) (THead (Bind Abst) 
x0 x1))).(\lambda (H9: (eq T t2 (THead (Bind Abbr) x2 x3))).(\lambda (_: (pr2 
c t x2)).(\lambda (_: ((\forall (b: B).(\forall (u: T).(pr2 (CHead c (Bind b) 
u) x1 x3))))).(eq_ind_r T (THead (Bind Abbr) x2 x3) (\lambda (t1: T).(eq T 
(THead (Flat Appl) t (THeads (Flat Appl) t0 (TLRef i))) t1)) (TList_ind 
(\lambda (t1: TList).((nf2 c (THeads (Flat Appl) t1 (TLRef i))) \to ((eq T 
(THeads (Flat Appl) t1 (TLRef i)) (THead (Bind Abst) x0 x1)) \to (eq T (THead 
(Flat Appl) t (THeads (Flat Appl) t1 (TLRef i))) (THead (Bind Abbr) x2 
x3))))) (\lambda (_: (nf2 c (THeads (Flat Appl) TNil (TLRef i)))).(\lambda 
(H13: (eq T (THeads (Flat Appl) TNil (TLRef i)) (THead (Bind Abst) x0 
x1))).(let H14 \def (eq_ind T (TLRef i) (\lambda (ee: T).(match ee in T 
return (\lambda (_: T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) 
\Rightarrow True | (THead _ _ _) \Rightarrow False])) I (THead (Bind Abst) x0 
x1) H13) in (False_ind (eq T (THead (Flat Appl) t (THeads (Flat Appl) TNil 
(TLRef i))) (THead (Bind Abbr) x2 x3)) H14)))) (\lambda (t1: T).(\lambda (t3: 
TList).(\lambda (_: (((nf2 c (THeads (Flat Appl) t3 (TLRef i))) \to ((eq T 
(THeads (Flat Appl) t3 (TLRef i)) (THead (Bind Abst) x0 x1)) \to (eq T (THead 
(Flat Appl) t (THeads (Flat Appl) t3 (TLRef i))) (THead (Bind Abbr) x2 
x3)))))).(\lambda (_: (nf2 c (THeads (Flat Appl) (TCons t1 t3) (TLRef 
i)))).(\lambda (H13: (eq T (THeads (Flat Appl) (TCons t1 t3) (TLRef i)) 
(THead (Bind Abst) x0 x1))).(let H14 \def (eq_ind T (THead (Flat Appl) t1 
(THeads (Flat Appl) t3 (TLRef i))) (\lambda (ee: T).(match ee in T return 
(\lambda (_: T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) 
\Rightarrow False | (THead k _ _) \Rightarrow (match k in K return (\lambda 
(_: K).Prop) with [(Bind _) \Rightarrow False | (Flat _) \Rightarrow 
True])])) I (THead (Bind Abst) x0 x1) H13) in (False_ind (eq T (THead (Flat 
Appl) t (THeads (Flat Appl) (TCons t1 t3) (TLRef i))) (THead (Bind Abbr) x2 
x3)) H14))))))) t0 H_y H8) t2 H9))))))))) H7)) (\lambda (H7: (ex6_6 B T T T T 
T (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda 
(y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq 
T (THeads (Flat Appl) t0 (TLRef i)) (THead (Bind b) y1 z1)))))))) (\lambda 
(b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u2: 
T).(\lambda (y2: T).(eq T t2 (THead (Bind b) y2 (THead (Flat Appl) (lift (S 
O) O u2) z2))))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c t u2))))))) (\lambda (_: 
B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(y2: T).(pr2 c y1 y2))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (z1: 
T).(\lambda (z2: T).(\lambda (_: T).(\lambda (y2: T).(pr2 (CHead c (Bind b) 
y2) z1 z2))))))))).(ex6_6_ind B T T T T T (\lambda (b: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(not (eq B 
b Abst)))))))) (\lambda (b: B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(eq T (THeads (Flat Appl) t0 (TLRef i)) 
(THead (Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (z2: T).(\lambda (u2: T).(\lambda (y2: T).(eq T t2 (THead (Bind 
b) y2 (THead (Flat Appl) (lift (S O) O u2) z2))))))))) (\lambda (_: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(_: T).(pr2 c t u2))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (y2: T).(pr2 c y1 y2))))))) 
(\lambda (b: B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: T).(\lambda 
(_: T).(\lambda (y2: T).(pr2 (CHead c (Bind b) y2) z1 z2))))))) (eq T (THead 
(Flat Appl) t (THeads (Flat Appl) t0 (TLRef i))) t2) (\lambda (x0: 
B).(\lambda (x1: T).(\lambda (x2: T).(\lambda (x3: T).(\lambda (x4: 
T).(\lambda (x5: T).(\lambda (_: (not (eq B x0 Abst))).(\lambda (H9: (eq T 
(THeads (Flat Appl) t0 (TLRef i)) (THead (Bind x0) x1 x2))).(\lambda (H10: 
(eq T t2 (THead (Bind x0) x5 (THead (Flat Appl) (lift (S O) O x4) 
x3)))).(\lambda (_: (pr2 c t x4)).(\lambda (_: (pr2 c x1 x5)).(\lambda (_: 
(pr2 (CHead c (Bind x0) x5) x2 x3)).(eq_ind_r T (THead (Bind x0) x5 (THead 
(Flat Appl) (lift (S O) O x4) x3)) (\lambda (t1: T).(eq T (THead (Flat Appl) 
t (THeads (Flat Appl) t0 (TLRef i))) t1)) (TList_ind (\lambda (t1: 
TList).((nf2 c (THeads (Flat Appl) t1 (TLRef i))) \to ((eq T (THeads (Flat 
Appl) t1 (TLRef i)) (THead (Bind x0) x1 x2)) \to (eq T (THead (Flat Appl) t 
(THeads (Flat Appl) t1 (TLRef i))) (THead (Bind x0) x5 (THead (Flat Appl) 
(lift (S O) O x4) x3)))))) (\lambda (_: (nf2 c (THeads (Flat Appl) TNil 
(TLRef i)))).(\lambda (H15: (eq T (THeads (Flat Appl) TNil (TLRef i)) (THead 
(Bind x0) x1 x2))).(let H16 \def (eq_ind T (TLRef i) (\lambda (ee: T).(match 
ee in T return (\lambda (_: T).Prop) with [(TSort _) \Rightarrow False | 
(TLRef _) \Rightarrow True | (THead _ _ _) \Rightarrow False])) I (THead 
(Bind x0) x1 x2) H15) in (False_ind (eq T (THead (Flat Appl) t (THeads (Flat 
Appl) TNil (TLRef i))) (THead (Bind x0) x5 (THead (Flat Appl) (lift (S O) O 
x4) x3))) H16)))) (\lambda (t1: T).(\lambda (t3: TList).(\lambda (_: (((nf2 c 
(THeads (Flat Appl) t3 (TLRef i))) \to ((eq T (THeads (Flat Appl) t3 (TLRef 
i)) (THead (Bind x0) x1 x2)) \to (eq T (THead (Flat Appl) t (THeads (Flat 
Appl) t3 (TLRef i))) (THead (Bind x0) x5 (THead (Flat Appl) (lift (S O) O x4) 
x3))))))).(\lambda (_: (nf2 c (THeads (Flat Appl) (TCons t1 t3) (TLRef 
i)))).(\lambda (H15: (eq T (THeads (Flat Appl) (TCons t1 t3) (TLRef i)) 
(THead (Bind x0) x1 x2))).(let H16 \def (eq_ind T (THead (Flat Appl) t1 
(THeads (Flat Appl) t3 (TLRef i))) (\lambda (ee: T).(match ee in T return 
(\lambda (_: T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) 
\Rightarrow False | (THead k _ _) \Rightarrow (match k in K return (\lambda 
(_: K).Prop) with [(Bind _) \Rightarrow False | (Flat _) \Rightarrow 
True])])) I (THead (Bind x0) x1 x2) H15) in (False_ind (eq T (THead (Flat 
Appl) t (THeads (Flat Appl) (TCons t1 t3) (TLRef i))) (THead (Bind x0) x5 
(THead (Flat Appl) (lift (S O) O x4) x3))) H16))))))) t0 H_y H9) t2 
H10))))))))))))) H7)) H6))))))) H2)))))) vs)))).
(* COMMENTS
Initial nodes: 2915
END *)

theorem nf2_appl_lref:
 \forall (c: C).(\forall (u: T).((nf2 c u) \to (\forall (i: nat).((nf2 c 
(TLRef i)) \to (nf2 c (THead (Flat Appl) u (TLRef i)))))))
\def
 \lambda (c: C).(\lambda (u: T).(\lambda (H: (nf2 c u)).(\lambda (i: 
nat).(\lambda (H0: (nf2 c (TLRef i))).(let H_y \def (nf2_appls_lref c i H0 
(TCons u TNil)) in (H_y (conj (nf2 c u) True H I))))))).
(* COMMENTS
Initial nodes: 49
END *)

theorem nf2_lref_abst:
 \forall (c: C).(\forall (e: C).(\forall (u: T).(\forall (i: nat).((getl i c 
(CHead e (Bind Abst) u)) \to (nf2 c (TLRef i))))))
\def
 \lambda (c: C).(\lambda (e: C).(\lambda (u: T).(\lambda (i: nat).(\lambda 
(H: (getl i c (CHead e (Bind Abst) u))).(\lambda (t2: T).(\lambda (H0: (pr2 c 
(TLRef i) t2)).(let H1 \def (pr2_gen_lref c t2 i H0) in (or_ind (eq T t2 
(TLRef i)) (ex2_2 C T (\lambda (d: C).(\lambda (u0: T).(getl i c (CHead d 
(Bind Abbr) u0)))) (\lambda (_: C).(\lambda (u0: T).(eq T t2 (lift (S i) O 
u0))))) (eq T (TLRef i) t2) (\lambda (H2: (eq T t2 (TLRef i))).(eq_ind_r T 
(TLRef i) (\lambda (t: T).(eq T (TLRef i) t)) (refl_equal T (TLRef i)) t2 
H2)) (\lambda (H2: (ex2_2 C T (\lambda (d: C).(\lambda (u0: T).(getl i c 
(CHead d (Bind Abbr) u0)))) (\lambda (_: C).(\lambda (u0: T).(eq T t2 (lift 
(S i) O u0)))))).(ex2_2_ind C T (\lambda (d: C).(\lambda (u0: T).(getl i c 
(CHead d (Bind Abbr) u0)))) (\lambda (_: C).(\lambda (u0: T).(eq T t2 (lift 
(S i) O u0)))) (eq T (TLRef i) t2) (\lambda (x0: C).(\lambda (x1: T).(\lambda 
(H3: (getl i c (CHead x0 (Bind Abbr) x1))).(\lambda (H4: (eq T t2 (lift (S i) 
O x1))).(eq_ind_r T (lift (S i) O x1) (\lambda (t: T).(eq T (TLRef i) t)) 
(let H5 \def (eq_ind C (CHead e (Bind Abst) u) (\lambda (c0: C).(getl i c 
c0)) H (CHead x0 (Bind Abbr) x1) (getl_mono c (CHead e (Bind Abst) u) i H 
(CHead x0 (Bind Abbr) x1) H3)) in (let H6 \def (eq_ind C (CHead e (Bind Abst) 
u) (\lambda (ee: C).(match ee in C return (\lambda (_: C).Prop) with [(CSort 
_) \Rightarrow False | (CHead _ k _) \Rightarrow (match k in K return 
(\lambda (_: K).Prop) with [(Bind b) \Rightarrow (match b in B return 
(\lambda (_: B).Prop) with [Abbr \Rightarrow False | Abst \Rightarrow True | 
Void \Rightarrow False]) | (Flat _) \Rightarrow False])])) I (CHead x0 (Bind 
Abbr) x1) (getl_mono c (CHead e (Bind Abst) u) i H (CHead x0 (Bind Abbr) x1) 
H3)) in (False_ind (eq T (TLRef i) (lift (S i) O x1)) H6))) t2 H4))))) H2)) 
H1)))))))).
(* COMMENTS
Initial nodes: 494
END *)

theorem nf2_lift:
 \forall (d: C).(\forall (t: T).((nf2 d t) \to (\forall (c: C).(\forall (h: 
nat).(\forall (i: nat).((drop h i c d) \to (nf2 c (lift h i t))))))))
\def
 \lambda (d: C).(\lambda (t: T).(\lambda (H: ((\forall (t2: T).((pr2 d t t2) 
\to (eq T t t2))))).(\lambda (c: C).(\lambda (h: nat).(\lambda (i: 
nat).(\lambda (H0: (drop h i c d)).(\lambda (t2: T).(\lambda (H1: (pr2 c 
(lift h i t) t2)).(let H2 \def (pr2_gen_lift c t t2 h i H1 d H0) in (ex2_ind 
T (\lambda (t3: T).(eq T t2 (lift h i t3))) (\lambda (t3: T).(pr2 d t t3)) 
(eq T (lift h i t) t2) (\lambda (x: T).(\lambda (H3: (eq T t2 (lift h i 
x))).(\lambda (H4: (pr2 d t x)).(eq_ind_r T (lift h i x) (\lambda (t0: T).(eq 
T (lift h i t) t0)) (let H_y \def (H x H4) in (let H5 \def (eq_ind_r T x 
(\lambda (t0: T).(pr2 d t t0)) H4 t H_y) in (eq_ind T t (\lambda (t0: T).(eq 
T (lift h i t) (lift h i t0))) (refl_equal T (lift h i t)) x H_y))) t2 H3)))) 
H2)))))))))).
(* COMMENTS
Initial nodes: 245
END *)

