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

include "Basic-1/pc3/dec.ma".

include "Basic-1/getl/flt.ma".

include "Basic-1/getl/dec.ma".

theorem ty3_inference:
 \forall (g: G).(\forall (c: C).(\forall (t1: T).(or (ex T (\lambda (t2: 
T).(ty3 g c t1 t2))) (\forall (t2: T).((ty3 g c t1 t2) \to False)))))
\def
 \lambda (g: G).(\lambda (c: C).(\lambda (t1: T).(flt_wf_ind (\lambda (c0: 
C).(\lambda (t: T).(or (ex T (\lambda (t2: T).(ty3 g c0 t t2))) (\forall (t2: 
T).((ty3 g c0 t t2) \to False))))) (\lambda (c2: C).(\lambda (t2: T).(T_ind 
(\lambda (t: T).(((\forall (c1: C).(\forall (t3: T).((flt c1 t3 c2 t) \to (or 
(ex T (\lambda (t4: T).(ty3 g c1 t3 t4))) (\forall (t4: T).((ty3 g c1 t3 t4) 
\to False))))))) \to (or (ex T (\lambda (t3: T).(ty3 g c2 t t3))) (\forall 
(t3: T).((ty3 g c2 t t3) \to False))))) (\lambda (n: nat).(\lambda (_: 
((\forall (c1: C).(\forall (t3: T).((flt c1 t3 c2 (TSort n)) \to (or (ex T 
(\lambda (t4: T).(ty3 g c1 t3 t4))) (\forall (t4: T).((ty3 g c1 t3 t4) \to 
False)))))))).(or_introl (ex T (\lambda (t3: T).(ty3 g c2 (TSort n) t3))) 
(\forall (t3: T).((ty3 g c2 (TSort n) t3) \to False)) (ex_intro T (\lambda 
(t3: T).(ty3 g c2 (TSort n) t3)) (TSort (next g n)) (ty3_sort g c2 n))))) 
(\lambda (n: nat).(\lambda (H: ((\forall (c1: C).(\forall (t3: T).((flt c1 t3 
c2 (TLRef n)) \to (or (ex T (\lambda (t4: T).(ty3 g c1 t3 t4))) (\forall (t4: 
T).((ty3 g c1 t3 t4) \to False)))))))).(let H_x \def (getl_dec c2 n) in (let 
H0 \def H_x in (or_ind (ex_3 C B T (\lambda (e: C).(\lambda (b: B).(\lambda 
(v: T).(getl n c2 (CHead e (Bind b) v)))))) (\forall (d: C).((getl n c2 d) 
\to (\forall (P: Prop).P))) (or (ex T (\lambda (t3: T).(ty3 g c2 (TLRef n) 
t3))) (\forall (t3: T).((ty3 g c2 (TLRef n) t3) \to False))) (\lambda (H1: 
(ex_3 C B T (\lambda (e: C).(\lambda (b: B).(\lambda (v: T).(getl n c2 (CHead 
e (Bind b) v))))))).(ex_3_ind C B T (\lambda (e: C).(\lambda (b: B).(\lambda 
(v: T).(getl n c2 (CHead e (Bind b) v))))) (or (ex T (\lambda (t3: T).(ty3 g 
c2 (TLRef n) t3))) (\forall (t3: T).((ty3 g c2 (TLRef n) t3) \to False))) 
(\lambda (x0: C).(\lambda (x1: B).(\lambda (x2: T).(\lambda (H2: (getl n c2 
(CHead x0 (Bind x1) x2))).(let H3 \def (H x0 x2 (getl_flt x1 c2 x0 x2 n H2)) 
in (or_ind (ex T (\lambda (t3: T).(ty3 g x0 x2 t3))) (\forall (t3: T).((ty3 g 
x0 x2 t3) \to False)) (or (ex T (\lambda (t3: T).(ty3 g c2 (TLRef n) t3))) 
(\forall (t3: T).((ty3 g c2 (TLRef n) t3) \to False))) (\lambda (H4: (ex T 
(\lambda (t3: T).(ty3 g x0 x2 t3)))).(ex_ind T (\lambda (t3: T).(ty3 g x0 x2 
t3)) (or (ex T (\lambda (t3: T).(ty3 g c2 (TLRef n) t3))) (\forall (t3: 
T).((ty3 g c2 (TLRef n) t3) \to False))) (\lambda (x: T).(\lambda (H5: (ty3 g 
x0 x2 x)).(B_ind (\lambda (b: B).((getl n c2 (CHead x0 (Bind b) x2)) \to (or 
(ex T (\lambda (t3: T).(ty3 g c2 (TLRef n) t3))) (\forall (t3: T).((ty3 g c2 
(TLRef n) t3) \to False))))) (\lambda (H6: (getl n c2 (CHead x0 (Bind Abbr) 
x2))).(or_introl (ex T (\lambda (t3: T).(ty3 g c2 (TLRef n) t3))) (\forall 
(t3: T).((ty3 g c2 (TLRef n) t3) \to False)) (ex_intro T (\lambda (t3: 
T).(ty3 g c2 (TLRef n) t3)) (lift (S n) O x) (ty3_abbr g n c2 x0 x2 H6 x 
H5)))) (\lambda (H6: (getl n c2 (CHead x0 (Bind Abst) x2))).(or_introl (ex T 
(\lambda (t3: T).(ty3 g c2 (TLRef n) t3))) (\forall (t3: T).((ty3 g c2 (TLRef 
n) t3) \to False)) (ex_intro T (\lambda (t3: T).(ty3 g c2 (TLRef n) t3)) 
(lift (S n) O x2) (ty3_abst g n c2 x0 x2 H6 x H5)))) (\lambda (H6: (getl n c2 
(CHead x0 (Bind Void) x2))).(or_intror (ex T (\lambda (t3: T).(ty3 g c2 
(TLRef n) t3))) (\forall (t3: T).((ty3 g c2 (TLRef n) t3) \to False)) 
(\lambda (t3: T).(\lambda (H7: (ty3 g c2 (TLRef n) t3)).(or_ind (ex3_3 C T T 
(\lambda (_: C).(\lambda (_: T).(\lambda (t: T).(pc3 c2 (lift (S n) O t) 
t3)))) (\lambda (e: C).(\lambda (u: T).(\lambda (_: T).(getl n c2 (CHead e 
(Bind Abbr) u))))) (\lambda (e: C).(\lambda (u: T).(\lambda (t: T).(ty3 g e u 
t))))) (ex3_3 C T T (\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(pc3 c2 
(lift (S n) O u) t3)))) (\lambda (e: C).(\lambda (u: T).(\lambda (_: T).(getl 
n c2 (CHead e (Bind Abst) u))))) (\lambda (e: C).(\lambda (u: T).(\lambda (t: 
T).(ty3 g e u t))))) False (\lambda (H8: (ex3_3 C T T (\lambda (_: 
C).(\lambda (_: T).(\lambda (t: T).(pc3 c2 (lift (S n) O t) t3)))) (\lambda 
(e: C).(\lambda (u: T).(\lambda (_: T).(getl n c2 (CHead e (Bind Abbr) u))))) 
(\lambda (e: C).(\lambda (u: T).(\lambda (t: T).(ty3 g e u t)))))).(ex3_3_ind 
C T T (\lambda (_: C).(\lambda (_: T).(\lambda (t: T).(pc3 c2 (lift (S n) O 
t) t3)))) (\lambda (e: C).(\lambda (u: T).(\lambda (_: T).(getl n c2 (CHead e 
(Bind Abbr) u))))) (\lambda (e: C).(\lambda (u: T).(\lambda (t: T).(ty3 g e u 
t)))) False (\lambda (x3: C).(\lambda (x4: T).(\lambda (x5: T).(\lambda (_: 
(pc3 c2 (lift (S n) O x5) t3)).(\lambda (H10: (getl n c2 (CHead x3 (Bind 
Abbr) x4))).(\lambda (_: (ty3 g x3 x4 x5)).(let H12 \def (eq_ind C (CHead x0 
(Bind Void) x2) (\lambda (c0: C).(getl n c2 c0)) H6 (CHead x3 (Bind Abbr) x4) 
(getl_mono c2 (CHead x0 (Bind Void) x2) n H6 (CHead x3 (Bind Abbr) x4) H10)) 
in (let H13 \def (eq_ind C (CHead x0 (Bind Void) x2) (\lambda (ee: C).(match 
ee in C return (\lambda (_: C).Prop) with [(CSort _) \Rightarrow False | 
(CHead _ k _) \Rightarrow (match k in K return (\lambda (_: K).Prop) with 
[(Bind b) \Rightarrow (match b in B return (\lambda (_: B).Prop) with [Abbr 
\Rightarrow False | Abst \Rightarrow False | Void \Rightarrow True]) | (Flat 
_) \Rightarrow False])])) I (CHead x3 (Bind Abbr) x4) (getl_mono c2 (CHead x0 
(Bind Void) x2) n H6 (CHead x3 (Bind Abbr) x4) H10)) in (False_ind False 
H13))))))))) H8)) (\lambda (H8: (ex3_3 C T T (\lambda (_: C).(\lambda (u: 
T).(\lambda (_: T).(pc3 c2 (lift (S n) O u) t3)))) (\lambda (e: C).(\lambda 
(u: T).(\lambda (_: T).(getl n c2 (CHead e (Bind Abst) u))))) (\lambda (e: 
C).(\lambda (u: T).(\lambda (t: T).(ty3 g e u t)))))).(ex3_3_ind C T T 
(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(pc3 c2 (lift (S n) O u) 
t3)))) (\lambda (e: C).(\lambda (u: T).(\lambda (_: T).(getl n c2 (CHead e 
(Bind Abst) u))))) (\lambda (e: C).(\lambda (u: T).(\lambda (t: T).(ty3 g e u 
t)))) False (\lambda (x3: C).(\lambda (x4: T).(\lambda (x5: T).(\lambda (_: 
(pc3 c2 (lift (S n) O x4) t3)).(\lambda (H10: (getl n c2 (CHead x3 (Bind 
Abst) x4))).(\lambda (_: (ty3 g x3 x4 x5)).(let H12 \def (eq_ind C (CHead x0 
(Bind Void) x2) (\lambda (c0: C).(getl n c2 c0)) H6 (CHead x3 (Bind Abst) x4) 
(getl_mono c2 (CHead x0 (Bind Void) x2) n H6 (CHead x3 (Bind Abst) x4) H10)) 
in (let H13 \def (eq_ind C (CHead x0 (Bind Void) x2) (\lambda (ee: C).(match 
ee in C return (\lambda (_: C).Prop) with [(CSort _) \Rightarrow False | 
(CHead _ k _) \Rightarrow (match k in K return (\lambda (_: K).Prop) with 
[(Bind b) \Rightarrow (match b in B return (\lambda (_: B).Prop) with [Abbr 
\Rightarrow False | Abst \Rightarrow False | Void \Rightarrow True]) | (Flat 
_) \Rightarrow False])])) I (CHead x3 (Bind Abst) x4) (getl_mono c2 (CHead x0 
(Bind Void) x2) n H6 (CHead x3 (Bind Abst) x4) H10)) in (False_ind False 
H13))))))))) H8)) (ty3_gen_lref g c2 t3 n H7)))))) x1 H2))) H4)) (\lambda 
(H4: ((\forall (t3: T).((ty3 g x0 x2 t3) \to False)))).(or_intror (ex T 
(\lambda (t3: T).(ty3 g c2 (TLRef n) t3))) (\forall (t3: T).((ty3 g c2 (TLRef 
n) t3) \to False)) (\lambda (t3: T).(\lambda (H5: (ty3 g c2 (TLRef n) 
t3)).(or_ind (ex3_3 C T T (\lambda (_: C).(\lambda (_: T).(\lambda (t: 
T).(pc3 c2 (lift (S n) O t) t3)))) (\lambda (e: C).(\lambda (u: T).(\lambda 
(_: T).(getl n c2 (CHead e (Bind Abbr) u))))) (\lambda (e: C).(\lambda (u: 
T).(\lambda (t: T).(ty3 g e u t))))) (ex3_3 C T T (\lambda (_: C).(\lambda 
(u: T).(\lambda (_: T).(pc3 c2 (lift (S n) O u) t3)))) (\lambda (e: 
C).(\lambda (u: T).(\lambda (_: T).(getl n c2 (CHead e (Bind Abst) u))))) 
(\lambda (e: C).(\lambda (u: T).(\lambda (t: T).(ty3 g e u t))))) False 
(\lambda (H6: (ex3_3 C T T (\lambda (_: C).(\lambda (_: T).(\lambda (t: 
T).(pc3 c2 (lift (S n) O t) t3)))) (\lambda (e: C).(\lambda (u: T).(\lambda 
(_: T).(getl n c2 (CHead e (Bind Abbr) u))))) (\lambda (e: C).(\lambda (u: 
T).(\lambda (t: T).(ty3 g e u t)))))).(ex3_3_ind C T T (\lambda (_: 
C).(\lambda (_: T).(\lambda (t: T).(pc3 c2 (lift (S n) O t) t3)))) (\lambda 
(e: C).(\lambda (u: T).(\lambda (_: T).(getl n c2 (CHead e (Bind Abbr) u))))) 
(\lambda (e: C).(\lambda (u: T).(\lambda (t: T).(ty3 g e u t)))) False 
(\lambda (x3: C).(\lambda (x4: T).(\lambda (x5: T).(\lambda (_: (pc3 c2 (lift 
(S n) O x5) t3)).(\lambda (H8: (getl n c2 (CHead x3 (Bind Abbr) 
x4))).(\lambda (H9: (ty3 g x3 x4 x5)).(let H10 \def (eq_ind C (CHead x0 (Bind 
x1) x2) (\lambda (c0: C).(getl n c2 c0)) H2 (CHead x3 (Bind Abbr) x4) 
(getl_mono c2 (CHead x0 (Bind x1) x2) n H2 (CHead x3 (Bind Abbr) x4) H8)) in 
(let H11 \def (f_equal C C (\lambda (e: C).(match e in C return (\lambda (_: 
C).C) with [(CSort _) \Rightarrow x0 | (CHead c0 _ _) \Rightarrow c0])) 
(CHead x0 (Bind x1) x2) (CHead x3 (Bind Abbr) x4) (getl_mono c2 (CHead x0 
(Bind x1) x2) n H2 (CHead x3 (Bind Abbr) x4) H8)) in ((let H12 \def (f_equal 
C B (\lambda (e: C).(match e in C return (\lambda (_: C).B) with [(CSort _) 
\Rightarrow x1 | (CHead _ k _) \Rightarrow (match k in K return (\lambda (_: 
K).B) with [(Bind b) \Rightarrow b | (Flat _) \Rightarrow x1])])) (CHead x0 
(Bind x1) x2) (CHead x3 (Bind Abbr) x4) (getl_mono c2 (CHead x0 (Bind x1) x2) 
n H2 (CHead x3 (Bind Abbr) x4) H8)) in ((let H13 \def (f_equal C T (\lambda 
(e: C).(match e in C return (\lambda (_: C).T) with [(CSort _) \Rightarrow x2 
| (CHead _ _ t) \Rightarrow t])) (CHead x0 (Bind x1) x2) (CHead x3 (Bind 
Abbr) x4) (getl_mono c2 (CHead x0 (Bind x1) x2) n H2 (CHead x3 (Bind Abbr) 
x4) H8)) in (\lambda (_: (eq B x1 Abbr)).(\lambda (H15: (eq C x0 x3)).(let 
H16 \def (eq_ind_r T x4 (\lambda (t: T).(getl n c2 (CHead x3 (Bind Abbr) t))) 
H10 x2 H13) in (let H17 \def (eq_ind_r T x4 (\lambda (t: T).(ty3 g x3 t x5)) 
H9 x2 H13) in (let H18 \def (eq_ind_r C x3 (\lambda (c0: C).(getl n c2 (CHead 
c0 (Bind Abbr) x2))) H16 x0 H15) in (let H19 \def (eq_ind_r C x3 (\lambda 
(c0: C).(ty3 g c0 x2 x5)) H17 x0 H15) in (H4 x5 H19)))))))) H12)) 
H11))))))))) H6)) (\lambda (H6: (ex3_3 C T T (\lambda (_: C).(\lambda (u: 
T).(\lambda (_: T).(pc3 c2 (lift (S n) O u) t3)))) (\lambda (e: C).(\lambda 
(u: T).(\lambda (_: T).(getl n c2 (CHead e (Bind Abst) u))))) (\lambda (e: 
C).(\lambda (u: T).(\lambda (t: T).(ty3 g e u t)))))).(ex3_3_ind C T T 
(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(pc3 c2 (lift (S n) O u) 
t3)))) (\lambda (e: C).(\lambda (u: T).(\lambda (_: T).(getl n c2 (CHead e 
(Bind Abst) u))))) (\lambda (e: C).(\lambda (u: T).(\lambda (t: T).(ty3 g e u 
t)))) False (\lambda (x3: C).(\lambda (x4: T).(\lambda (x5: T).(\lambda (H7: 
(pc3 c2 (lift (S n) O x4) t3)).(\lambda (H8: (getl n c2 (CHead x3 (Bind Abst) 
x4))).(\lambda (H9: (ty3 g x3 x4 x5)).(let H10 \def (eq_ind C (CHead x0 (Bind 
x1) x2) (\lambda (c0: C).(getl n c2 c0)) H2 (CHead x3 (Bind Abst) x4) 
(getl_mono c2 (CHead x0 (Bind x1) x2) n H2 (CHead x3 (Bind Abst) x4) H8)) in 
(let H11 \def (f_equal C C (\lambda (e: C).(match e in C return (\lambda (_: 
C).C) with [(CSort _) \Rightarrow x0 | (CHead c0 _ _) \Rightarrow c0])) 
(CHead x0 (Bind x1) x2) (CHead x3 (Bind Abst) x4) (getl_mono c2 (CHead x0 
(Bind x1) x2) n H2 (CHead x3 (Bind Abst) x4) H8)) in ((let H12 \def (f_equal 
C B (\lambda (e: C).(match e in C return (\lambda (_: C).B) with [(CSort _) 
\Rightarrow x1 | (CHead _ k _) \Rightarrow (match k in K return (\lambda (_: 
K).B) with [(Bind b) \Rightarrow b | (Flat _) \Rightarrow x1])])) (CHead x0 
(Bind x1) x2) (CHead x3 (Bind Abst) x4) (getl_mono c2 (CHead x0 (Bind x1) x2) 
n H2 (CHead x3 (Bind Abst) x4) H8)) in ((let H13 \def (f_equal C T (\lambda 
(e: C).(match e in C return (\lambda (_: C).T) with [(CSort _) \Rightarrow x2 
| (CHead _ _ t) \Rightarrow t])) (CHead x0 (Bind x1) x2) (CHead x3 (Bind 
Abst) x4) (getl_mono c2 (CHead x0 (Bind x1) x2) n H2 (CHead x3 (Bind Abst) 
x4) H8)) in (\lambda (_: (eq B x1 Abst)).(\lambda (H15: (eq C x0 x3)).(let 
H16 \def (eq_ind_r T x4 (\lambda (t: T).(getl n c2 (CHead x3 (Bind Abst) t))) 
H10 x2 H13) in (let H17 \def (eq_ind_r T x4 (\lambda (t: T).(ty3 g x3 t x5)) 
H9 x2 H13) in (let H18 \def (eq_ind_r T x4 (\lambda (t: T).(pc3 c2 (lift (S 
n) O t) t3)) H7 x2 H13) in (let H19 \def (eq_ind_r C x3 (\lambda (c0: 
C).(getl n c2 (CHead c0 (Bind Abst) x2))) H16 x0 H15) in (let H20 \def 
(eq_ind_r C x3 (\lambda (c0: C).(ty3 g c0 x2 x5)) H17 x0 H15) in (H4 x5 
H20))))))))) H12)) H11))))))))) H6)) (ty3_gen_lref g c2 t3 n H5)))))) 
H3)))))) H1)) (\lambda (H1: ((\forall (d: C).((getl n c2 d) \to (\forall (P: 
Prop).P))))).(or_intror (ex T (\lambda (t3: T).(ty3 g c2 (TLRef n) t3))) 
(\forall (t3: T).((ty3 g c2 (TLRef n) t3) \to False)) (\lambda (t3: 
T).(\lambda (H2: (ty3 g c2 (TLRef n) t3)).(or_ind (ex3_3 C T T (\lambda (_: 
C).(\lambda (_: T).(\lambda (t: T).(pc3 c2 (lift (S n) O t) t3)))) (\lambda 
(e: C).(\lambda (u: T).(\lambda (_: T).(getl n c2 (CHead e (Bind Abbr) u))))) 
(\lambda (e: C).(\lambda (u: T).(\lambda (t: T).(ty3 g e u t))))) (ex3_3 C T 
T (\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(pc3 c2 (lift (S n) O u) 
t3)))) (\lambda (e: C).(\lambda (u: T).(\lambda (_: T).(getl n c2 (CHead e 
(Bind Abst) u))))) (\lambda (e: C).(\lambda (u: T).(\lambda (t: T).(ty3 g e u 
t))))) False (\lambda (H3: (ex3_3 C T T (\lambda (_: C).(\lambda (_: 
T).(\lambda (t: T).(pc3 c2 (lift (S n) O t) t3)))) (\lambda (e: C).(\lambda 
(u: T).(\lambda (_: T).(getl n c2 (CHead e (Bind Abbr) u))))) (\lambda (e: 
C).(\lambda (u: T).(\lambda (t: T).(ty3 g e u t)))))).(ex3_3_ind C T T 
(\lambda (_: C).(\lambda (_: T).(\lambda (t: T).(pc3 c2 (lift (S n) O t) 
t3)))) (\lambda (e: C).(\lambda (u: T).(\lambda (_: T).(getl n c2 (CHead e 
(Bind Abbr) u))))) (\lambda (e: C).(\lambda (u: T).(\lambda (t: T).(ty3 g e u 
t)))) False (\lambda (x0: C).(\lambda (x1: T).(\lambda (x2: T).(\lambda (_: 
(pc3 c2 (lift (S n) O x2) t3)).(\lambda (H5: (getl n c2 (CHead x0 (Bind Abbr) 
x1))).(\lambda (_: (ty3 g x0 x1 x2)).(H1 (CHead x0 (Bind Abbr) x1) H5 
False))))))) H3)) (\lambda (H3: (ex3_3 C T T (\lambda (_: C).(\lambda (u: 
T).(\lambda (_: T).(pc3 c2 (lift (S n) O u) t3)))) (\lambda (e: C).(\lambda 
(u: T).(\lambda (_: T).(getl n c2 (CHead e (Bind Abst) u))))) (\lambda (e: 
C).(\lambda (u: T).(\lambda (t: T).(ty3 g e u t)))))).(ex3_3_ind C T T 
(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(pc3 c2 (lift (S n) O u) 
t3)))) (\lambda (e: C).(\lambda (u: T).(\lambda (_: T).(getl n c2 (CHead e 
(Bind Abst) u))))) (\lambda (e: C).(\lambda (u: T).(\lambda (t: T).(ty3 g e u 
t)))) False (\lambda (x0: C).(\lambda (x1: T).(\lambda (x2: T).(\lambda (_: 
(pc3 c2 (lift (S n) O x1) t3)).(\lambda (H5: (getl n c2 (CHead x0 (Bind Abst) 
x1))).(\lambda (_: (ty3 g x0 x1 x2)).(H1 (CHead x0 (Bind Abst) x1) H5 
False))))))) H3)) (ty3_gen_lref g c2 t3 n H2)))))) H0))))) (\lambda (k: 
K).(\lambda (t: T).(\lambda (_: ((((\forall (c1: C).(\forall (t3: T).((flt c1 
t3 c2 t) \to (or (ex T (\lambda (t4: T).(ty3 g c1 t3 t4))) (\forall (t4: 
T).((ty3 g c1 t3 t4) \to False))))))) \to (or (ex T (\lambda (t3: T).(ty3 g 
c2 t t3))) (\forall (t3: T).((ty3 g c2 t t3) \to False)))))).(\lambda (t0: 
T).(\lambda (_: ((((\forall (c1: C).(\forall (t3: T).((flt c1 t3 c2 t0) \to 
(or (ex T (\lambda (t4: T).(ty3 g c1 t3 t4))) (\forall (t4: T).((ty3 g c1 t3 
t4) \to False))))))) \to (or (ex T (\lambda (t3: T).(ty3 g c2 t0 t3))) 
(\forall (t3: T).((ty3 g c2 t0 t3) \to False)))))).(\lambda (H1: ((\forall 
(c1: C).(\forall (t3: T).((flt c1 t3 c2 (THead k t t0)) \to (or (ex T 
(\lambda (t4: T).(ty3 g c1 t3 t4))) (\forall (t4: T).((ty3 g c1 t3 t4) \to 
False)))))))).(K_ind (\lambda (k0: K).(((\forall (c1: C).(\forall (t3: 
T).((flt c1 t3 c2 (THead k0 t t0)) \to (or (ex T (\lambda (t4: T).(ty3 g c1 
t3 t4))) (\forall (t4: T).((ty3 g c1 t3 t4) \to False))))))) \to (or (ex T 
(\lambda (t3: T).(ty3 g c2 (THead k0 t t0) t3))) (\forall (t3: T).((ty3 g c2 
(THead k0 t t0) t3) \to False))))) (\lambda (b: B).(\lambda (H2: ((\forall 
(c1: C).(\forall (t3: T).((flt c1 t3 c2 (THead (Bind b) t t0)) \to (or (ex T 
(\lambda (t4: T).(ty3 g c1 t3 t4))) (\forall (t4: T).((ty3 g c1 t3 t4) \to 
False)))))))).(let H3 \def (H2 c2 t (flt_thead_sx (Bind b) c2 t t0)) in 
(or_ind (ex T (\lambda (t3: T).(ty3 g c2 t t3))) (\forall (t3: T).((ty3 g c2 
t t3) \to False)) (or (ex T (\lambda (t3: T).(ty3 g c2 (THead (Bind b) t t0) 
t3))) (\forall (t3: T).((ty3 g c2 (THead (Bind b) t t0) t3) \to False))) 
(\lambda (H4: (ex T (\lambda (t3: T).(ty3 g c2 t t3)))).(ex_ind T (\lambda 
(t3: T).(ty3 g c2 t t3)) (or (ex T (\lambda (t3: T).(ty3 g c2 (THead (Bind b) 
t t0) t3))) (\forall (t3: T).((ty3 g c2 (THead (Bind b) t t0) t3) \to 
False))) (\lambda (x: T).(\lambda (H5: (ty3 g c2 t x)).(let H6 \def (H2 
(CHead c2 (Bind b) t) t0 (flt_shift (Bind b) c2 t t0)) in (or_ind (ex T 
(\lambda (t3: T).(ty3 g (CHead c2 (Bind b) t) t0 t3))) (\forall (t3: T).((ty3 
g (CHead c2 (Bind b) t) t0 t3) \to False)) (or (ex T (\lambda (t3: T).(ty3 g 
c2 (THead (Bind b) t t0) t3))) (\forall (t3: T).((ty3 g c2 (THead (Bind b) t 
t0) t3) \to False))) (\lambda (H7: (ex T (\lambda (t3: T).(ty3 g (CHead c2 
(Bind b) t) t0 t3)))).(ex_ind T (\lambda (t3: T).(ty3 g (CHead c2 (Bind b) t) 
t0 t3)) (or (ex T (\lambda (t3: T).(ty3 g c2 (THead (Bind b) t t0) t3))) 
(\forall (t3: T).((ty3 g c2 (THead (Bind b) t t0) t3) \to False))) (\lambda 
(x0: T).(\lambda (H8: (ty3 g (CHead c2 (Bind b) t) t0 x0)).(or_introl (ex T 
(\lambda (t3: T).(ty3 g c2 (THead (Bind b) t t0) t3))) (\forall (t3: T).((ty3 
g c2 (THead (Bind b) t t0) t3) \to False)) (ex_intro T (\lambda (t3: T).(ty3 
g c2 (THead (Bind b) t t0) t3)) (THead (Bind b) t x0) (ty3_bind g c2 t x H5 b 
t0 x0 H8))))) H7)) (\lambda (H7: ((\forall (t3: T).((ty3 g (CHead c2 (Bind b) 
t) t0 t3) \to False)))).(or_intror (ex T (\lambda (t3: T).(ty3 g c2 (THead 
(Bind b) t t0) t3))) (\forall (t3: T).((ty3 g c2 (THead (Bind b) t t0) t3) 
\to False)) (\lambda (t3: T).(\lambda (H8: (ty3 g c2 (THead (Bind b) t t0) 
t3)).(ex3_2_ind T T (\lambda (t4: T).(\lambda (_: T).(pc3 c2 (THead (Bind b) 
t t4) t3))) (\lambda (_: T).(\lambda (t5: T).(ty3 g c2 t t5))) (\lambda (t4: 
T).(\lambda (_: T).(ty3 g (CHead c2 (Bind b) t) t0 t4))) False (\lambda (x0: 
T).(\lambda (x1: T).(\lambda (_: (pc3 c2 (THead (Bind b) t x0) t3)).(\lambda 
(_: (ty3 g c2 t x1)).(\lambda (H11: (ty3 g (CHead c2 (Bind b) t) t0 x0)).(H7 
x0 H11)))))) (ty3_gen_bind g b c2 t t0 t3 H8)))))) H6)))) H4)) (\lambda (H4: 
((\forall (t3: T).((ty3 g c2 t t3) \to False)))).(or_intror (ex T (\lambda 
(t3: T).(ty3 g c2 (THead (Bind b) t t0) t3))) (\forall (t3: T).((ty3 g c2 
(THead (Bind b) t t0) t3) \to False)) (\lambda (t3: T).(\lambda (H5: (ty3 g 
c2 (THead (Bind b) t t0) t3)).(ex3_2_ind T T (\lambda (t4: T).(\lambda (_: 
T).(pc3 c2 (THead (Bind b) t t4) t3))) (\lambda (_: T).(\lambda (t5: T).(ty3 
g c2 t t5))) (\lambda (t4: T).(\lambda (_: T).(ty3 g (CHead c2 (Bind b) t) t0 
t4))) False (\lambda (x0: T).(\lambda (x1: T).(\lambda (_: (pc3 c2 (THead 
(Bind b) t x0) t3)).(\lambda (H7: (ty3 g c2 t x1)).(\lambda (_: (ty3 g (CHead 
c2 (Bind b) t) t0 x0)).(H4 x1 H7)))))) (ty3_gen_bind g b c2 t t0 t3 H5)))))) 
H3)))) (\lambda (f: F).(\lambda (H2: ((\forall (c1: C).(\forall (t3: T).((flt 
c1 t3 c2 (THead (Flat f) t t0)) \to (or (ex T (\lambda (t4: T).(ty3 g c1 t3 
t4))) (\forall (t4: T).((ty3 g c1 t3 t4) \to False)))))))).(F_ind (\lambda 
(f0: F).(((\forall (c1: C).(\forall (t3: T).((flt c1 t3 c2 (THead (Flat f0) t 
t0)) \to (or (ex T (\lambda (t4: T).(ty3 g c1 t3 t4))) (\forall (t4: T).((ty3 
g c1 t3 t4) \to False))))))) \to (or (ex T (\lambda (t3: T).(ty3 g c2 (THead 
(Flat f0) t t0) t3))) (\forall (t3: T).((ty3 g c2 (THead (Flat f0) t t0) t3) 
\to False))))) (\lambda (H3: ((\forall (c1: C).(\forall (t3: T).((flt c1 t3 
c2 (THead (Flat Appl) t t0)) \to (or (ex T (\lambda (t4: T).(ty3 g c1 t3 
t4))) (\forall (t4: T).((ty3 g c1 t3 t4) \to False)))))))).(let H4 \def (H3 
c2 t (flt_thead_sx (Flat Appl) c2 t t0)) in (or_ind (ex T (\lambda (t3: 
T).(ty3 g c2 t t3))) (\forall (t3: T).((ty3 g c2 t t3) \to False)) (or (ex T 
(\lambda (t3: T).(ty3 g c2 (THead (Flat Appl) t t0) t3))) (\forall (t3: 
T).((ty3 g c2 (THead (Flat Appl) t t0) t3) \to False))) (\lambda (H5: (ex T 
(\lambda (t3: T).(ty3 g c2 t t3)))).(ex_ind T (\lambda (t3: T).(ty3 g c2 t 
t3)) (or (ex T (\lambda (t3: T).(ty3 g c2 (THead (Flat Appl) t t0) t3))) 
(\forall (t3: T).((ty3 g c2 (THead (Flat Appl) t t0) t3) \to False))) 
(\lambda (x: T).(\lambda (H6: (ty3 g c2 t x)).(let H7 \def (H3 c2 t0 
(flt_thead_dx (Flat Appl) c2 t t0)) in (or_ind (ex T (\lambda (t3: T).(ty3 g 
c2 t0 t3))) (\forall (t3: T).((ty3 g c2 t0 t3) \to False)) (or (ex T (\lambda 
(t3: T).(ty3 g c2 (THead (Flat Appl) t t0) t3))) (\forall (t3: T).((ty3 g c2 
(THead (Flat Appl) t t0) t3) \to False))) (\lambda (H8: (ex T (\lambda (t3: 
T).(ty3 g c2 t0 t3)))).(ex_ind T (\lambda (t3: T).(ty3 g c2 t0 t3)) (or (ex T 
(\lambda (t3: T).(ty3 g c2 (THead (Flat Appl) t t0) t3))) (\forall (t3: 
T).((ty3 g c2 (THead (Flat Appl) t t0) t3) \to False))) (\lambda (x0: 
T).(\lambda (H9: (ty3 g c2 t0 x0)).(ex_ind T (\lambda (t3: T).(ty3 g c2 x0 
t3)) (or (ex T (\lambda (t3: T).(ty3 g c2 (THead (Flat Appl) t t0) t3))) 
(\forall (t3: T).((ty3 g c2 (THead (Flat Appl) t t0) t3) \to False))) 
(\lambda (x1: T).(\lambda (H10: (ty3 g c2 x0 x1)).(ex_ind T (\lambda (t3: 
T).(ty3 g c2 x t3)) (or (ex T (\lambda (t3: T).(ty3 g c2 (THead (Flat Appl) t 
t0) t3))) (\forall (t3: T).((ty3 g c2 (THead (Flat Appl) t t0) t3) \to 
False))) (\lambda (x2: T).(\lambda (H11: (ty3 g c2 x x2)).(let H12 \def 
(ty3_sn3 g c2 x x2 H11) in (let H_x \def (nf2_sn3 c2 x H12) in (let H13 \def 
H_x in (ex2_ind T (\lambda (u: T).(pr3 c2 x u)) (\lambda (u: T).(nf2 c2 u)) 
(or (ex T (\lambda (t3: T).(ty3 g c2 (THead (Flat Appl) t t0) t3))) (\forall 
(t3: T).((ty3 g c2 (THead (Flat Appl) t t0) t3) \to False))) (\lambda (x3: 
T).(\lambda (H14: (pr3 c2 x x3)).(\lambda (H15: (nf2 c2 x3)).(let H16 \def 
(ty3_sred_pr3 c2 x x3 H14 g x2 H11) in (let H_x0 \def (pc3_abst_dec g c2 x0 
x1 H10 x3 x2 H16) in (let H17 \def H_x0 in (or_ind (ex4_2 T T (\lambda (u: 
T).(\lambda (_: T).(pc3 c2 x0 (THead (Bind Abst) x3 u)))) (\lambda (u: 
T).(\lambda (v2: T).(ty3 g c2 (THead (Bind Abst) v2 u) x1))) (\lambda (_: 
T).(\lambda (v2: T).(pr3 c2 x3 v2))) (\lambda (_: T).(\lambda (v2: T).(nf2 c2 
v2)))) (\forall (u: T).((pc3 c2 x0 (THead (Bind Abst) x3 u)) \to False)) (or 
(ex T (\lambda (t3: T).(ty3 g c2 (THead (Flat Appl) t t0) t3))) (\forall (t3: 
T).((ty3 g c2 (THead (Flat Appl) t t0) t3) \to False))) (\lambda (H18: (ex4_2 
T T (\lambda (u: T).(\lambda (_: T).(pc3 c2 x0 (THead (Bind Abst) x3 u)))) 
(\lambda (u: T).(\lambda (v2: T).(ty3 g c2 (THead (Bind Abst) v2 u) x1))) 
(\lambda (_: T).(\lambda (v2: T).(pr3 c2 x3 v2))) (\lambda (_: T).(\lambda 
(v2: T).(nf2 c2 v2))))).(ex4_2_ind T T (\lambda (u: T).(\lambda (_: T).(pc3 
c2 x0 (THead (Bind Abst) x3 u)))) (\lambda (u: T).(\lambda (v2: T).(ty3 g c2 
(THead (Bind Abst) v2 u) x1))) (\lambda (_: T).(\lambda (v2: T).(pr3 c2 x3 
v2))) (\lambda (_: T).(\lambda (v2: T).(nf2 c2 v2))) (or (ex T (\lambda (t3: 
T).(ty3 g c2 (THead (Flat Appl) t t0) t3))) (\forall (t3: T).((ty3 g c2 
(THead (Flat Appl) t t0) t3) \to False))) (\lambda (x4: T).(\lambda (x5: 
T).(\lambda (H19: (pc3 c2 x0 (THead (Bind Abst) x3 x4))).(\lambda (H20: (ty3 
g c2 (THead (Bind Abst) x5 x4) x1)).(\lambda (H21: (pr3 c2 x3 x5)).(\lambda 
(_: (nf2 c2 x5)).(let H_y \def (nf2_pr3_unfold c2 x3 x5 H21 H15) in (let H23 
\def (eq_ind_r T x5 (\lambda (t3: T).(pr3 c2 x3 t3)) H21 x3 H_y) in (let H24 
\def (eq_ind_r T x5 (\lambda (t3: T).(ty3 g c2 (THead (Bind Abst) t3 x4) x1)) 
H20 x3 H_y) in (or_introl (ex T (\lambda (t3: T).(ty3 g c2 (THead (Flat Appl) 
t t0) t3))) (\forall (t3: T).((ty3 g c2 (THead (Flat Appl) t t0) t3) \to 
False)) (ex_intro T (\lambda (t3: T).(ty3 g c2 (THead (Flat Appl) t t0) t3)) 
(THead (Flat Appl) t (THead (Bind Abst) x3 x4)) (ty3_appl g c2 t x3 (ty3_tred 
g c2 t x H6 x3 H14) t0 x4 (ty3_conv g c2 (THead (Bind Abst) x3 x4) x1 H24 t0 
x0 H9 H19))))))))))))) H18)) (\lambda (H18: ((\forall (u: T).((pc3 c2 x0 
(THead (Bind Abst) x3 u)) \to False)))).(or_intror (ex T (\lambda (t3: 
T).(ty3 g c2 (THead (Flat Appl) t t0) t3))) (\forall (t3: T).((ty3 g c2 
(THead (Flat Appl) t t0) t3) \to False)) (\lambda (t3: T).(\lambda (H19: (ty3 
g c2 (THead (Flat Appl) t t0) t3)).(ex3_2_ind T T (\lambda (u: T).(\lambda 
(t4: T).(pc3 c2 (THead (Flat Appl) t (THead (Bind Abst) u t4)) t3))) (\lambda 
(u: T).(\lambda (t4: T).(ty3 g c2 t0 (THead (Bind Abst) u t4)))) (\lambda (u: 
T).(\lambda (_: T).(ty3 g c2 t u))) False (\lambda (x4: T).(\lambda (x5: 
T).(\lambda (_: (pc3 c2 (THead (Flat Appl) t (THead (Bind Abst) x4 x5)) 
t3)).(\lambda (H21: (ty3 g c2 t0 (THead (Bind Abst) x4 x5))).(\lambda (H22: 
(ty3 g c2 t x4)).(let H_y \def (ty3_unique g c2 t x4 H22 x H6) in (let H_y0 
\def (ty3_unique g c2 t0 (THead (Bind Abst) x4 x5) H21 x0 H9) in (H18 x5 
(pc3_t (THead (Bind Abst) x4 x5) c2 x0 (pc3_s c2 x0 (THead (Bind Abst) x4 x5) 
H_y0) (THead (Bind Abst) x3 x5) (pc3_head_1 c2 x4 x3 (pc3_t x c2 x4 H_y x3 
(pc3_pr3_r c2 x x3 H14)) (Bind Abst) x5)))))))))) (ty3_gen_appl g c2 t t0 t3 
H19)))))) H17))))))) H13)))))) (ty3_correct g c2 t x H6)))) (ty3_correct g c2 
t0 x0 H9)))) H8)) (\lambda (H8: ((\forall (t3: T).((ty3 g c2 t0 t3) \to 
False)))).(or_intror (ex T (\lambda (t3: T).(ty3 g c2 (THead (Flat Appl) t 
t0) t3))) (\forall (t3: T).((ty3 g c2 (THead (Flat Appl) t t0) t3) \to 
False)) (\lambda (t3: T).(\lambda (H9: (ty3 g c2 (THead (Flat Appl) t t0) 
t3)).(ex3_2_ind T T (\lambda (u: T).(\lambda (t4: T).(pc3 c2 (THead (Flat 
Appl) t (THead (Bind Abst) u t4)) t3))) (\lambda (u: T).(\lambda (t4: T).(ty3 
g c2 t0 (THead (Bind Abst) u t4)))) (\lambda (u: T).(\lambda (_: T).(ty3 g c2 
t u))) False (\lambda (x0: T).(\lambda (x1: T).(\lambda (_: (pc3 c2 (THead 
(Flat Appl) t (THead (Bind Abst) x0 x1)) t3)).(\lambda (H11: (ty3 g c2 t0 
(THead (Bind Abst) x0 x1))).(\lambda (_: (ty3 g c2 t x0)).(H8 (THead (Bind 
Abst) x0 x1) H11)))))) (ty3_gen_appl g c2 t t0 t3 H9)))))) H7)))) H5)) 
(\lambda (H5: ((\forall (t3: T).((ty3 g c2 t t3) \to False)))).(or_intror (ex 
T (\lambda (t3: T).(ty3 g c2 (THead (Flat Appl) t t0) t3))) (\forall (t3: 
T).((ty3 g c2 (THead (Flat Appl) t t0) t3) \to False)) (\lambda (t3: 
T).(\lambda (H6: (ty3 g c2 (THead (Flat Appl) t t0) t3)).(ex3_2_ind T T 
(\lambda (u: T).(\lambda (t4: T).(pc3 c2 (THead (Flat Appl) t (THead (Bind 
Abst) u t4)) t3))) (\lambda (u: T).(\lambda (t4: T).(ty3 g c2 t0 (THead (Bind 
Abst) u t4)))) (\lambda (u: T).(\lambda (_: T).(ty3 g c2 t u))) False 
(\lambda (x0: T).(\lambda (x1: T).(\lambda (_: (pc3 c2 (THead (Flat Appl) t 
(THead (Bind Abst) x0 x1)) t3)).(\lambda (_: (ty3 g c2 t0 (THead (Bind Abst) 
x0 x1))).(\lambda (H9: (ty3 g c2 t x0)).(H5 x0 H9)))))) (ty3_gen_appl g c2 t 
t0 t3 H6)))))) H4))) (\lambda (H3: ((\forall (c1: C).(\forall (t3: T).((flt 
c1 t3 c2 (THead (Flat Cast) t t0)) \to (or (ex T (\lambda (t4: T).(ty3 g c1 
t3 t4))) (\forall (t4: T).((ty3 g c1 t3 t4) \to False)))))))).(let H4 \def 
(H3 c2 t (flt_thead_sx (Flat Cast) c2 t t0)) in (or_ind (ex T (\lambda (t3: 
T).(ty3 g c2 t t3))) (\forall (t3: T).((ty3 g c2 t t3) \to False)) (or (ex T 
(\lambda (t3: T).(ty3 g c2 (THead (Flat Cast) t t0) t3))) (\forall (t3: 
T).((ty3 g c2 (THead (Flat Cast) t t0) t3) \to False))) (\lambda (H5: (ex T 
(\lambda (t3: T).(ty3 g c2 t t3)))).(ex_ind T (\lambda (t3: T).(ty3 g c2 t 
t3)) (or (ex T (\lambda (t3: T).(ty3 g c2 (THead (Flat Cast) t t0) t3))) 
(\forall (t3: T).((ty3 g c2 (THead (Flat Cast) t t0) t3) \to False))) 
(\lambda (x: T).(\lambda (H6: (ty3 g c2 t x)).(let H7 \def (H3 c2 t0 
(flt_thead_dx (Flat Cast) c2 t t0)) in (or_ind (ex T (\lambda (t3: T).(ty3 g 
c2 t0 t3))) (\forall (t3: T).((ty3 g c2 t0 t3) \to False)) (or (ex T (\lambda 
(t3: T).(ty3 g c2 (THead (Flat Cast) t t0) t3))) (\forall (t3: T).((ty3 g c2 
(THead (Flat Cast) t t0) t3) \to False))) (\lambda (H8: (ex T (\lambda (t3: 
T).(ty3 g c2 t0 t3)))).(ex_ind T (\lambda (t3: T).(ty3 g c2 t0 t3)) (or (ex T 
(\lambda (t3: T).(ty3 g c2 (THead (Flat Cast) t t0) t3))) (\forall (t3: 
T).((ty3 g c2 (THead (Flat Cast) t t0) t3) \to False))) (\lambda (x0: 
T).(\lambda (H9: (ty3 g c2 t0 x0)).(ex_ind T (\lambda (t3: T).(ty3 g c2 x0 
t3)) (or (ex T (\lambda (t3: T).(ty3 g c2 (THead (Flat Cast) t t0) t3))) 
(\forall (t3: T).((ty3 g c2 (THead (Flat Cast) t t0) t3) \to False))) 
(\lambda (x1: T).(\lambda (H10: (ty3 g c2 x0 x1)).(let H_x \def (pc3_dec g c2 
x0 x1 H10 t x H6) in (let H11 \def H_x in (or_ind (pc3 c2 x0 t) ((pc3 c2 x0 
t) \to False) (or (ex T (\lambda (t3: T).(ty3 g c2 (THead (Flat Cast) t t0) 
t3))) (\forall (t3: T).((ty3 g c2 (THead (Flat Cast) t t0) t3) \to False))) 
(\lambda (H12: (pc3 c2 x0 t)).(or_introl (ex T (\lambda (t3: T).(ty3 g c2 
(THead (Flat Cast) t t0) t3))) (\forall (t3: T).((ty3 g c2 (THead (Flat Cast) 
t t0) t3) \to False)) (ex_intro T (\lambda (t3: T).(ty3 g c2 (THead (Flat 
Cast) t t0) t3)) (THead (Flat Cast) x t) (ty3_cast g c2 t0 t (ty3_conv g c2 t 
x H6 t0 x0 H9 H12) x H6)))) (\lambda (H12: (((pc3 c2 x0 t) \to 
False))).(or_intror (ex T (\lambda (t3: T).(ty3 g c2 (THead (Flat Cast) t t0) 
t3))) (\forall (t3: T).((ty3 g c2 (THead (Flat Cast) t t0) t3) \to False)) 
(\lambda (t3: T).(\lambda (H13: (ty3 g c2 (THead (Flat Cast) t t0) 
t3)).(ex3_ind T (\lambda (t4: T).(pc3 c2 (THead (Flat Cast) t4 t) t3)) 
(\lambda (_: T).(ty3 g c2 t0 t)) (\lambda (t4: T).(ty3 g c2 t t4)) False 
(\lambda (x2: T).(\lambda (_: (pc3 c2 (THead (Flat Cast) x2 t) t3)).(\lambda 
(H15: (ty3 g c2 t0 t)).(\lambda (H16: (ty3 g c2 t x2)).(let H_y \def 
(ty3_unique g c2 t x2 H16 x H6) in (let H_y0 \def (ty3_unique g c2 t0 t H15 
x0 H9) in (H12 (ex2_sym T (pr3 c2 t) (pr3 c2 x0) H_y0)))))))) (ty3_gen_cast g 
c2 t0 t t3 H13)))))) H11))))) (ty3_correct g c2 t0 x0 H9)))) H8)) (\lambda 
(H8: ((\forall (t3: T).((ty3 g c2 t0 t3) \to False)))).(or_intror (ex T 
(\lambda (t3: T).(ty3 g c2 (THead (Flat Cast) t t0) t3))) (\forall (t3: 
T).((ty3 g c2 (THead (Flat Cast) t t0) t3) \to False)) (\lambda (t3: 
T).(\lambda (H9: (ty3 g c2 (THead (Flat Cast) t t0) t3)).(ex3_ind T (\lambda 
(t4: T).(pc3 c2 (THead (Flat Cast) t4 t) t3)) (\lambda (_: T).(ty3 g c2 t0 
t)) (\lambda (t4: T).(ty3 g c2 t t4)) False (\lambda (x0: T).(\lambda (_: 
(pc3 c2 (THead (Flat Cast) x0 t) t3)).(\lambda (H11: (ty3 g c2 t0 
t)).(\lambda (_: (ty3 g c2 t x0)).(H8 t H11))))) (ty3_gen_cast g c2 t0 t t3 
H9)))))) H7)))) H5)) (\lambda (H5: ((\forall (t3: T).((ty3 g c2 t t3) \to 
False)))).(or_intror (ex T (\lambda (t3: T).(ty3 g c2 (THead (Flat Cast) t 
t0) t3))) (\forall (t3: T).((ty3 g c2 (THead (Flat Cast) t t0) t3) \to 
False)) (\lambda (t3: T).(\lambda (H6: (ty3 g c2 (THead (Flat Cast) t t0) 
t3)).(ex3_ind T (\lambda (t4: T).(pc3 c2 (THead (Flat Cast) t4 t) t3)) 
(\lambda (_: T).(ty3 g c2 t0 t)) (\lambda (t4: T).(ty3 g c2 t t4)) False 
(\lambda (x0: T).(\lambda (_: (pc3 c2 (THead (Flat Cast) x0 t) t3)).(\lambda 
(_: (ty3 g c2 t0 t)).(\lambda (H9: (ty3 g c2 t x0)).(ex_ind T (\lambda (t4: 
T).(ty3 g c2 x0 t4)) False (\lambda (x: T).(\lambda (_: (ty3 g c2 x0 x)).(H5 
x0 H9))) (ty3_correct g c2 t x0 H9)))))) (ty3_gen_cast g c2 t0 t t3 H6)))))) 
H4))) f H2))) k H1))))))) t2))) c t1))).
(* COMMENTS
Initial nodes: 9001
END *)

