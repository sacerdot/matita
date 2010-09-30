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

include "Basic-1/T/defs.ma".

theorem terms_props__bind_dec:
 \forall (b1: B).(\forall (b2: B).(or (eq B b1 b2) ((eq B b1 b2) \to (\forall 
(P: Prop).P))))
\def
 \lambda (b1: B).(B_ind (\lambda (b: B).(\forall (b2: B).(or (eq B b b2) ((eq 
B b b2) \to (\forall (P: Prop).P))))) (\lambda (b2: B).(B_ind (\lambda (b: 
B).(or (eq B Abbr b) ((eq B Abbr b) \to (\forall (P: Prop).P)))) (or_introl 
(eq B Abbr Abbr) ((eq B Abbr Abbr) \to (\forall (P: Prop).P)) (refl_equal B 
Abbr)) (or_intror (eq B Abbr Abst) ((eq B Abbr Abst) \to (\forall (P: 
Prop).P)) (\lambda (H: (eq B Abbr Abst)).(\lambda (P: Prop).(let H0 \def 
(eq_ind B Abbr (\lambda (ee: B).(match ee in B return (\lambda (_: B).Prop) 
with [Abbr \Rightarrow True | Abst \Rightarrow False | Void \Rightarrow 
False])) I Abst H) in (False_ind P H0))))) (or_intror (eq B Abbr Void) ((eq B 
Abbr Void) \to (\forall (P: Prop).P)) (\lambda (H: (eq B Abbr Void)).(\lambda 
(P: Prop).(let H0 \def (eq_ind B Abbr (\lambda (ee: B).(match ee in B return 
(\lambda (_: B).Prop) with [Abbr \Rightarrow True | Abst \Rightarrow False | 
Void \Rightarrow False])) I Void H) in (False_ind P H0))))) b2)) (\lambda 
(b2: B).(B_ind (\lambda (b: B).(or (eq B Abst b) ((eq B Abst b) \to (\forall 
(P: Prop).P)))) (or_intror (eq B Abst Abbr) ((eq B Abst Abbr) \to (\forall 
(P: Prop).P)) (\lambda (H: (eq B Abst Abbr)).(\lambda (P: Prop).(let H0 \def 
(eq_ind B Abst (\lambda (ee: B).(match ee in B return (\lambda (_: B).Prop) 
with [Abbr \Rightarrow False | Abst \Rightarrow True | Void \Rightarrow 
False])) I Abbr H) in (False_ind P H0))))) (or_introl (eq B Abst Abst) ((eq B 
Abst Abst) \to (\forall (P: Prop).P)) (refl_equal B Abst)) (or_intror (eq B 
Abst Void) ((eq B Abst Void) \to (\forall (P: Prop).P)) (\lambda (H: (eq B 
Abst Void)).(\lambda (P: Prop).(let H0 \def (eq_ind B Abst (\lambda (ee: 
B).(match ee in B return (\lambda (_: B).Prop) with [Abbr \Rightarrow False | 
Abst \Rightarrow True | Void \Rightarrow False])) I Void H) in (False_ind P 
H0))))) b2)) (\lambda (b2: B).(B_ind (\lambda (b: B).(or (eq B Void b) ((eq B 
Void b) \to (\forall (P: Prop).P)))) (or_intror (eq B Void Abbr) ((eq B Void 
Abbr) \to (\forall (P: Prop).P)) (\lambda (H: (eq B Void Abbr)).(\lambda (P: 
Prop).(let H0 \def (eq_ind B Void (\lambda (ee: B).(match ee in B return 
(\lambda (_: B).Prop) with [Abbr \Rightarrow False | Abst \Rightarrow False | 
Void \Rightarrow True])) I Abbr H) in (False_ind P H0))))) (or_intror (eq B 
Void Abst) ((eq B Void Abst) \to (\forall (P: Prop).P)) (\lambda (H: (eq B 
Void Abst)).(\lambda (P: Prop).(let H0 \def (eq_ind B Void (\lambda (ee: 
B).(match ee in B return (\lambda (_: B).Prop) with [Abbr \Rightarrow False | 
Abst \Rightarrow False | Void \Rightarrow True])) I Abst H) in (False_ind P 
H0))))) (or_introl (eq B Void Void) ((eq B Void Void) \to (\forall (P: 
Prop).P)) (refl_equal B Void)) b2)) b1).
(* COMMENTS
Initial nodes: 559
END *)

theorem bind_dec_not:
 \forall (b1: B).(\forall (b2: B).(or (eq B b1 b2) (not (eq B b1 b2))))
\def
 \lambda (b1: B).(\lambda (b2: B).(let H_x \def (terms_props__bind_dec b1 b2) 
in (let H \def H_x in (or_ind (eq B b1 b2) ((eq B b1 b2) \to (\forall (P: 
Prop).P)) (or (eq B b1 b2) ((eq B b1 b2) \to False)) (\lambda (H0: (eq B b1 
b2)).(or_introl (eq B b1 b2) ((eq B b1 b2) \to False) H0)) (\lambda (H0: 
(((eq B b1 b2) \to (\forall (P: Prop).P)))).(or_intror (eq B b1 b2) ((eq B b1 
b2) \to False) (\lambda (H1: (eq B b1 b2)).(H0 H1 False)))) H)))).
(* COMMENTS
Initial nodes: 131
END *)

theorem terms_props__flat_dec:
 \forall (f1: F).(\forall (f2: F).(or (eq F f1 f2) ((eq F f1 f2) \to (\forall 
(P: Prop).P))))
\def
 \lambda (f1: F).(F_ind (\lambda (f: F).(\forall (f2: F).(or (eq F f f2) ((eq 
F f f2) \to (\forall (P: Prop).P))))) (\lambda (f2: F).(F_ind (\lambda (f: 
F).(or (eq F Appl f) ((eq F Appl f) \to (\forall (P: Prop).P)))) (or_introl 
(eq F Appl Appl) ((eq F Appl Appl) \to (\forall (P: Prop).P)) (refl_equal F 
Appl)) (or_intror (eq F Appl Cast) ((eq F Appl Cast) \to (\forall (P: 
Prop).P)) (\lambda (H: (eq F Appl Cast)).(\lambda (P: Prop).(let H0 \def 
(eq_ind F Appl (\lambda (ee: F).(match ee in F return (\lambda (_: F).Prop) 
with [Appl \Rightarrow True | Cast \Rightarrow False])) I Cast H) in 
(False_ind P H0))))) f2)) (\lambda (f2: F).(F_ind (\lambda (f: F).(or (eq F 
Cast f) ((eq F Cast f) \to (\forall (P: Prop).P)))) (or_intror (eq F Cast 
Appl) ((eq F Cast Appl) \to (\forall (P: Prop).P)) (\lambda (H: (eq F Cast 
Appl)).(\lambda (P: Prop).(let H0 \def (eq_ind F Cast (\lambda (ee: F).(match 
ee in F return (\lambda (_: F).Prop) with [Appl \Rightarrow False | Cast 
\Rightarrow True])) I Appl H) in (False_ind P H0))))) (or_introl (eq F Cast 
Cast) ((eq F Cast Cast) \to (\forall (P: Prop).P)) (refl_equal F Cast)) f2)) 
f1).
(* COMMENTS
Initial nodes: 263
END *)

theorem terms_props__kind_dec:
 \forall (k1: K).(\forall (k2: K).(or (eq K k1 k2) ((eq K k1 k2) \to (\forall 
(P: Prop).P))))
\def
 \lambda (k1: K).(K_ind (\lambda (k: K).(\forall (k2: K).(or (eq K k k2) ((eq 
K k k2) \to (\forall (P: Prop).P))))) (\lambda (b: B).(\lambda (k2: K).(K_ind 
(\lambda (k: K).(or (eq K (Bind b) k) ((eq K (Bind b) k) \to (\forall (P: 
Prop).P)))) (\lambda (b0: B).(let H_x \def (terms_props__bind_dec b b0) in 
(let H \def H_x in (or_ind (eq B b b0) ((eq B b b0) \to (\forall (P: 
Prop).P)) (or (eq K (Bind b) (Bind b0)) ((eq K (Bind b) (Bind b0)) \to 
(\forall (P: Prop).P))) (\lambda (H0: (eq B b b0)).(eq_ind B b (\lambda (b1: 
B).(or (eq K (Bind b) (Bind b1)) ((eq K (Bind b) (Bind b1)) \to (\forall (P: 
Prop).P)))) (or_introl (eq K (Bind b) (Bind b)) ((eq K (Bind b) (Bind b)) \to 
(\forall (P: Prop).P)) (refl_equal K (Bind b))) b0 H0)) (\lambda (H0: (((eq B 
b b0) \to (\forall (P: Prop).P)))).(or_intror (eq K (Bind b) (Bind b0)) ((eq 
K (Bind b) (Bind b0)) \to (\forall (P: Prop).P)) (\lambda (H1: (eq K (Bind b) 
(Bind b0))).(\lambda (P: Prop).(let H2 \def (f_equal K B (\lambda (e: 
K).(match e in K return (\lambda (_: K).B) with [(Bind b1) \Rightarrow b1 | 
(Flat _) \Rightarrow b])) (Bind b) (Bind b0) H1) in (let H3 \def (eq_ind_r B 
b0 (\lambda (b1: B).((eq B b b1) \to (\forall (P0: Prop).P0))) H0 b H2) in 
(H3 (refl_equal B b) P))))))) H)))) (\lambda (f: F).(or_intror (eq K (Bind b) 
(Flat f)) ((eq K (Bind b) (Flat f)) \to (\forall (P: Prop).P)) (\lambda (H: 
(eq K (Bind b) (Flat f))).(\lambda (P: Prop).(let H0 \def (eq_ind K (Bind b) 
(\lambda (ee: K).(match ee in K return (\lambda (_: K).Prop) with [(Bind _) 
\Rightarrow True | (Flat _) \Rightarrow False])) I (Flat f) H) in (False_ind 
P H0)))))) k2))) (\lambda (f: F).(\lambda (k2: K).(K_ind (\lambda (k: K).(or 
(eq K (Flat f) k) ((eq K (Flat f) k) \to (\forall (P: Prop).P)))) (\lambda 
(b: B).(or_intror (eq K (Flat f) (Bind b)) ((eq K (Flat f) (Bind b)) \to 
(\forall (P: Prop).P)) (\lambda (H: (eq K (Flat f) (Bind b))).(\lambda (P: 
Prop).(let H0 \def (eq_ind K (Flat f) (\lambda (ee: K).(match ee in K return 
(\lambda (_: K).Prop) with [(Bind _) \Rightarrow False | (Flat _) \Rightarrow 
True])) I (Bind b) H) in (False_ind P H0)))))) (\lambda (f0: F).(let H_x \def 
(terms_props__flat_dec f f0) in (let H \def H_x in (or_ind (eq F f f0) ((eq F 
f f0) \to (\forall (P: Prop).P)) (or (eq K (Flat f) (Flat f0)) ((eq K (Flat 
f) (Flat f0)) \to (\forall (P: Prop).P))) (\lambda (H0: (eq F f f0)).(eq_ind 
F f (\lambda (f1: F).(or (eq K (Flat f) (Flat f1)) ((eq K (Flat f) (Flat f1)) 
\to (\forall (P: Prop).P)))) (or_introl (eq K (Flat f) (Flat f)) ((eq K (Flat 
f) (Flat f)) \to (\forall (P: Prop).P)) (refl_equal K (Flat f))) f0 H0)) 
(\lambda (H0: (((eq F f f0) \to (\forall (P: Prop).P)))).(or_intror (eq K 
(Flat f) (Flat f0)) ((eq K (Flat f) (Flat f0)) \to (\forall (P: Prop).P)) 
(\lambda (H1: (eq K (Flat f) (Flat f0))).(\lambda (P: Prop).(let H2 \def 
(f_equal K F (\lambda (e: K).(match e in K return (\lambda (_: K).F) with 
[(Bind _) \Rightarrow f | (Flat f1) \Rightarrow f1])) (Flat f) (Flat f0) H1) 
in (let H3 \def (eq_ind_r F f0 (\lambda (f1: F).((eq F f f1) \to (\forall 
(P0: Prop).P0))) H0 f H2) in (H3 (refl_equal F f) P))))))) H)))) k2))) k1).
(* COMMENTS
Initial nodes: 799
END *)

theorem term_dec:
 \forall (t1: T).(\forall (t2: T).(or (eq T t1 t2) ((eq T t1 t2) \to (\forall 
(P: Prop).P))))
\def
 \lambda (t1: T).(T_ind (\lambda (t: T).(\forall (t2: T).(or (eq T t t2) ((eq 
T t t2) \to (\forall (P: Prop).P))))) (\lambda (n: nat).(\lambda (t2: 
T).(T_ind (\lambda (t: T).(or (eq T (TSort n) t) ((eq T (TSort n) t) \to 
(\forall (P: Prop).P)))) (\lambda (n0: nat).(let H_x \def (nat_dec n n0) in 
(let H \def H_x in (or_ind (eq nat n n0) ((eq nat n n0) \to (\forall (P: 
Prop).P)) (or (eq T (TSort n) (TSort n0)) ((eq T (TSort n) (TSort n0)) \to 
(\forall (P: Prop).P))) (\lambda (H0: (eq nat n n0)).(eq_ind nat n (\lambda 
(n1: nat).(or (eq T (TSort n) (TSort n1)) ((eq T (TSort n) (TSort n1)) \to 
(\forall (P: Prop).P)))) (or_introl (eq T (TSort n) (TSort n)) ((eq T (TSort 
n) (TSort n)) \to (\forall (P: Prop).P)) (refl_equal T (TSort n))) n0 H0)) 
(\lambda (H0: (((eq nat n n0) \to (\forall (P: Prop).P)))).(or_intror (eq T 
(TSort n) (TSort n0)) ((eq T (TSort n) (TSort n0)) \to (\forall (P: Prop).P)) 
(\lambda (H1: (eq T (TSort n) (TSort n0))).(\lambda (P: Prop).(let H2 \def 
(f_equal T nat (\lambda (e: T).(match e in T return (\lambda (_: T).nat) with 
[(TSort n1) \Rightarrow n1 | (TLRef _) \Rightarrow n | (THead _ _ _) 
\Rightarrow n])) (TSort n) (TSort n0) H1) in (let H3 \def (eq_ind_r nat n0 
(\lambda (n1: nat).((eq nat n n1) \to (\forall (P0: Prop).P0))) H0 n H2) in 
(H3 (refl_equal nat n) P))))))) H)))) (\lambda (n0: nat).(or_intror (eq T 
(TSort n) (TLRef n0)) ((eq T (TSort n) (TLRef n0)) \to (\forall (P: Prop).P)) 
(\lambda (H: (eq T (TSort n) (TLRef n0))).(\lambda (P: Prop).(let H0 \def 
(eq_ind T (TSort n) (\lambda (ee: T).(match ee in T return (\lambda (_: 
T).Prop) with [(TSort _) \Rightarrow True | (TLRef _) \Rightarrow False | 
(THead _ _ _) \Rightarrow False])) I (TLRef n0) H) in (False_ind P H0)))))) 
(\lambda (k: K).(\lambda (t: T).(\lambda (_: (or (eq T (TSort n) t) ((eq T 
(TSort n) t) \to (\forall (P: Prop).P)))).(\lambda (t0: T).(\lambda (_: (or 
(eq T (TSort n) t0) ((eq T (TSort n) t0) \to (\forall (P: 
Prop).P)))).(or_intror (eq T (TSort n) (THead k t t0)) ((eq T (TSort n) 
(THead k t t0)) \to (\forall (P: Prop).P)) (\lambda (H1: (eq T (TSort n) 
(THead k t t0))).(\lambda (P: Prop).(let H2 \def (eq_ind T (TSort n) (\lambda 
(ee: T).(match ee in T return (\lambda (_: T).Prop) with [(TSort _) 
\Rightarrow True | (TLRef _) \Rightarrow False | (THead _ _ _) \Rightarrow 
False])) I (THead k t t0) H1) in (False_ind P H2)))))))))) t2))) (\lambda (n: 
nat).(\lambda (t2: T).(T_ind (\lambda (t: T).(or (eq T (TLRef n) t) ((eq T 
(TLRef n) t) \to (\forall (P: Prop).P)))) (\lambda (n0: nat).(or_intror (eq T 
(TLRef n) (TSort n0)) ((eq T (TLRef n) (TSort n0)) \to (\forall (P: Prop).P)) 
(\lambda (H: (eq T (TLRef n) (TSort n0))).(\lambda (P: Prop).(let H0 \def 
(eq_ind T (TLRef n) (\lambda (ee: T).(match ee in T return (\lambda (_: 
T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) \Rightarrow True | 
(THead _ _ _) \Rightarrow False])) I (TSort n0) H) in (False_ind P H0)))))) 
(\lambda (n0: nat).(let H_x \def (nat_dec n n0) in (let H \def H_x in (or_ind 
(eq nat n n0) ((eq nat n n0) \to (\forall (P: Prop).P)) (or (eq T (TLRef n) 
(TLRef n0)) ((eq T (TLRef n) (TLRef n0)) \to (\forall (P: Prop).P))) (\lambda 
(H0: (eq nat n n0)).(eq_ind nat n (\lambda (n1: nat).(or (eq T (TLRef n) 
(TLRef n1)) ((eq T (TLRef n) (TLRef n1)) \to (\forall (P: Prop).P)))) 
(or_introl (eq T (TLRef n) (TLRef n)) ((eq T (TLRef n) (TLRef n)) \to 
(\forall (P: Prop).P)) (refl_equal T (TLRef n))) n0 H0)) (\lambda (H0: (((eq 
nat n n0) \to (\forall (P: Prop).P)))).(or_intror (eq T (TLRef n) (TLRef n0)) 
((eq T (TLRef n) (TLRef n0)) \to (\forall (P: Prop).P)) (\lambda (H1: (eq T 
(TLRef n) (TLRef n0))).(\lambda (P: Prop).(let H2 \def (f_equal T nat 
(\lambda (e: T).(match e in T return (\lambda (_: T).nat) with [(TSort _) 
\Rightarrow n | (TLRef n1) \Rightarrow n1 | (THead _ _ _) \Rightarrow n])) 
(TLRef n) (TLRef n0) H1) in (let H3 \def (eq_ind_r nat n0 (\lambda (n1: 
nat).((eq nat n n1) \to (\forall (P0: Prop).P0))) H0 n H2) in (H3 (refl_equal 
nat n) P))))))) H)))) (\lambda (k: K).(\lambda (t: T).(\lambda (_: (or (eq T 
(TLRef n) t) ((eq T (TLRef n) t) \to (\forall (P: Prop).P)))).(\lambda (t0: 
T).(\lambda (_: (or (eq T (TLRef n) t0) ((eq T (TLRef n) t0) \to (\forall (P: 
Prop).P)))).(or_intror (eq T (TLRef n) (THead k t t0)) ((eq T (TLRef n) 
(THead k t t0)) \to (\forall (P: Prop).P)) (\lambda (H1: (eq T (TLRef n) 
(THead k t t0))).(\lambda (P: Prop).(let H2 \def (eq_ind T (TLRef n) (\lambda 
(ee: T).(match ee in T return (\lambda (_: T).Prop) with [(TSort _) 
\Rightarrow False | (TLRef _) \Rightarrow True | (THead _ _ _) \Rightarrow 
False])) I (THead k t t0) H1) in (False_ind P H2)))))))))) t2))) (\lambda (k: 
K).(\lambda (t: T).(\lambda (H: ((\forall (t2: T).(or (eq T t t2) ((eq T t 
t2) \to (\forall (P: Prop).P)))))).(\lambda (t0: T).(\lambda (H0: ((\forall 
(t2: T).(or (eq T t0 t2) ((eq T t0 t2) \to (\forall (P: 
Prop).P)))))).(\lambda (t2: T).(T_ind (\lambda (t3: T).(or (eq T (THead k t 
t0) t3) ((eq T (THead k t t0) t3) \to (\forall (P: Prop).P)))) (\lambda (n: 
nat).(or_intror (eq T (THead k t t0) (TSort n)) ((eq T (THead k t t0) (TSort 
n)) \to (\forall (P: Prop).P)) (\lambda (H1: (eq T (THead k t t0) (TSort 
n))).(\lambda (P: Prop).(let H2 \def (eq_ind T (THead k t t0) (\lambda (ee: 
T).(match ee in T return (\lambda (_: T).Prop) with [(TSort _) \Rightarrow 
False | (TLRef _) \Rightarrow False | (THead _ _ _) \Rightarrow True])) I 
(TSort n) H1) in (False_ind P H2)))))) (\lambda (n: nat).(or_intror (eq T 
(THead k t t0) (TLRef n)) ((eq T (THead k t t0) (TLRef n)) \to (\forall (P: 
Prop).P)) (\lambda (H1: (eq T (THead k t t0) (TLRef n))).(\lambda (P: 
Prop).(let H2 \def (eq_ind T (THead k t t0) (\lambda (ee: T).(match ee in T 
return (\lambda (_: T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) 
\Rightarrow False | (THead _ _ _) \Rightarrow True])) I (TLRef n) H1) in 
(False_ind P H2)))))) (\lambda (k0: K).(\lambda (t3: T).(\lambda (H1: (or (eq 
T (THead k t t0) t3) ((eq T (THead k t t0) t3) \to (\forall (P: 
Prop).P)))).(\lambda (t4: T).(\lambda (H2: (or (eq T (THead k t t0) t4) ((eq 
T (THead k t t0) t4) \to (\forall (P: Prop).P)))).(let H_x \def (H t3) in 
(let H3 \def H_x in (or_ind (eq T t t3) ((eq T t t3) \to (\forall (P: 
Prop).P)) (or (eq T (THead k t t0) (THead k0 t3 t4)) ((eq T (THead k t t0) 
(THead k0 t3 t4)) \to (\forall (P: Prop).P))) (\lambda (H4: (eq T t t3)).(let 
H5 \def (eq_ind_r T t3 (\lambda (t5: T).(or (eq T (THead k t t0) t5) ((eq T 
(THead k t t0) t5) \to (\forall (P: Prop).P)))) H1 t H4) in (eq_ind T t 
(\lambda (t5: T).(or (eq T (THead k t t0) (THead k0 t5 t4)) ((eq T (THead k t 
t0) (THead k0 t5 t4)) \to (\forall (P: Prop).P)))) (let H_x0 \def (H0 t4) in 
(let H6 \def H_x0 in (or_ind (eq T t0 t4) ((eq T t0 t4) \to (\forall (P: 
Prop).P)) (or (eq T (THead k t t0) (THead k0 t t4)) ((eq T (THead k t t0) 
(THead k0 t t4)) \to (\forall (P: Prop).P))) (\lambda (H7: (eq T t0 t4)).(let 
H8 \def (eq_ind_r T t4 (\lambda (t5: T).(or (eq T (THead k t t0) t5) ((eq T 
(THead k t t0) t5) \to (\forall (P: Prop).P)))) H2 t0 H7) in (eq_ind T t0 
(\lambda (t5: T).(or (eq T (THead k t t0) (THead k0 t t5)) ((eq T (THead k t 
t0) (THead k0 t t5)) \to (\forall (P: Prop).P)))) (let H_x1 \def 
(terms_props__kind_dec k k0) in (let H9 \def H_x1 in (or_ind (eq K k k0) ((eq 
K k k0) \to (\forall (P: Prop).P)) (or (eq T (THead k t t0) (THead k0 t t0)) 
((eq T (THead k t t0) (THead k0 t t0)) \to (\forall (P: Prop).P))) (\lambda 
(H10: (eq K k k0)).(eq_ind K k (\lambda (k1: K).(or (eq T (THead k t t0) 
(THead k1 t t0)) ((eq T (THead k t t0) (THead k1 t t0)) \to (\forall (P: 
Prop).P)))) (or_introl (eq T (THead k t t0) (THead k t t0)) ((eq T (THead k t 
t0) (THead k t t0)) \to (\forall (P: Prop).P)) (refl_equal T (THead k t t0))) 
k0 H10)) (\lambda (H10: (((eq K k k0) \to (\forall (P: Prop).P)))).(or_intror 
(eq T (THead k t t0) (THead k0 t t0)) ((eq T (THead k t t0) (THead k0 t t0)) 
\to (\forall (P: Prop).P)) (\lambda (H11: (eq T (THead k t t0) (THead k0 t 
t0))).(\lambda (P: Prop).(let H12 \def (f_equal T K (\lambda (e: T).(match e 
in T return (\lambda (_: T).K) with [(TSort _) \Rightarrow k | (TLRef _) 
\Rightarrow k | (THead k1 _ _) \Rightarrow k1])) (THead k t t0) (THead k0 t 
t0) H11) in (let H13 \def (eq_ind_r K k0 (\lambda (k1: K).((eq K k k1) \to 
(\forall (P0: Prop).P0))) H10 k H12) in (H13 (refl_equal K k) P))))))) H9))) 
t4 H7))) (\lambda (H7: (((eq T t0 t4) \to (\forall (P: Prop).P)))).(or_intror 
(eq T (THead k t t0) (THead k0 t t4)) ((eq T (THead k t t0) (THead k0 t t4)) 
\to (\forall (P: Prop).P)) (\lambda (H8: (eq T (THead k t t0) (THead k0 t 
t4))).(\lambda (P: Prop).(let H9 \def (f_equal T K (\lambda (e: T).(match e 
in T return (\lambda (_: T).K) with [(TSort _) \Rightarrow k | (TLRef _) 
\Rightarrow k | (THead k1 _ _) \Rightarrow k1])) (THead k t t0) (THead k0 t 
t4) H8) in ((let H10 \def (f_equal T T (\lambda (e: T).(match e in T return 
(\lambda (_: T).T) with [(TSort _) \Rightarrow t0 | (TLRef _) \Rightarrow t0 
| (THead _ _ t5) \Rightarrow t5])) (THead k t t0) (THead k0 t t4) H8) in 
(\lambda (_: (eq K k k0)).(let H12 \def (eq_ind_r T t4 (\lambda (t5: T).((eq 
T t0 t5) \to (\forall (P0: Prop).P0))) H7 t0 H10) in (let H13 \def (eq_ind_r 
T t4 (\lambda (t5: T).(or (eq T (THead k t t0) t5) ((eq T (THead k t t0) t5) 
\to (\forall (P0: Prop).P0)))) H2 t0 H10) in (H12 (refl_equal T t0) P))))) 
H9)))))) H6))) t3 H4))) (\lambda (H4: (((eq T t t3) \to (\forall (P: 
Prop).P)))).(or_intror (eq T (THead k t t0) (THead k0 t3 t4)) ((eq T (THead k 
t t0) (THead k0 t3 t4)) \to (\forall (P: Prop).P)) (\lambda (H5: (eq T (THead 
k t t0) (THead k0 t3 t4))).(\lambda (P: Prop).(let H6 \def (f_equal T K 
(\lambda (e: T).(match e in T return (\lambda (_: T).K) with [(TSort _) 
\Rightarrow k | (TLRef _) \Rightarrow k | (THead k1 _ _) \Rightarrow k1])) 
(THead k t t0) (THead k0 t3 t4) H5) in ((let H7 \def (f_equal T T (\lambda 
(e: T).(match e in T return (\lambda (_: T).T) with [(TSort _) \Rightarrow t 
| (TLRef _) \Rightarrow t | (THead _ t5 _) \Rightarrow t5])) (THead k t t0) 
(THead k0 t3 t4) H5) in ((let H8 \def (f_equal T T (\lambda (e: T).(match e 
in T return (\lambda (_: T).T) with [(TSort _) \Rightarrow t0 | (TLRef _) 
\Rightarrow t0 | (THead _ _ t5) \Rightarrow t5])) (THead k t t0) (THead k0 t3 
t4) H5) in (\lambda (H9: (eq T t t3)).(\lambda (_: (eq K k k0)).(let H11 \def 
(eq_ind_r T t4 (\lambda (t5: T).(or (eq T (THead k t t0) t5) ((eq T (THead k 
t t0) t5) \to (\forall (P0: Prop).P0)))) H2 t0 H8) in (let H12 \def (eq_ind_r 
T t3 (\lambda (t5: T).((eq T t t5) \to (\forall (P0: Prop).P0))) H4 t H9) in 
(let H13 \def (eq_ind_r T t3 (\lambda (t5: T).(or (eq T (THead k t t0) t5) 
((eq T (THead k t t0) t5) \to (\forall (P0: Prop).P0)))) H1 t H9) in (H12 
(refl_equal T t) P))))))) H7)) H6)))))) H3)))))))) t2))))))) t1).
(* COMMENTS
Initial nodes: 2821
END *)

theorem binder_dec:
 \forall (t: T).(or (ex_3 B T T (\lambda (b: B).(\lambda (w: T).(\lambda (u: 
T).(eq T t (THead (Bind b) w u)))))) (\forall (b: B).(\forall (w: T).(\forall 
(u: T).((eq T t (THead (Bind b) w u)) \to (\forall (P: Prop).P))))))
\def
 \lambda (t: T).(T_ind (\lambda (t0: T).(or (ex_3 B T T (\lambda (b: 
B).(\lambda (w: T).(\lambda (u: T).(eq T t0 (THead (Bind b) w u)))))) 
(\forall (b: B).(\forall (w: T).(\forall (u: T).((eq T t0 (THead (Bind b) w 
u)) \to (\forall (P: Prop).P))))))) (\lambda (n: nat).(or_intror (ex_3 B T T 
(\lambda (b: B).(\lambda (w: T).(\lambda (u: T).(eq T (TSort n) (THead (Bind 
b) w u)))))) (\forall (b: B).(\forall (w: T).(\forall (u: T).((eq T (TSort n) 
(THead (Bind b) w u)) \to (\forall (P: Prop).P))))) (\lambda (b: B).(\lambda 
(w: T).(\lambda (u: T).(\lambda (H: (eq T (TSort n) (THead (Bind b) w 
u))).(\lambda (P: Prop).(let H0 \def (eq_ind T (TSort n) (\lambda (ee: 
T).(match ee in T return (\lambda (_: T).Prop) with [(TSort _) \Rightarrow 
True | (TLRef _) \Rightarrow False | (THead _ _ _) \Rightarrow False])) I 
(THead (Bind b) w u) H) in (False_ind P H0))))))))) (\lambda (n: 
nat).(or_intror (ex_3 B T T (\lambda (b: B).(\lambda (w: T).(\lambda (u: 
T).(eq T (TLRef n) (THead (Bind b) w u)))))) (\forall (b: B).(\forall (w: 
T).(\forall (u: T).((eq T (TLRef n) (THead (Bind b) w u)) \to (\forall (P: 
Prop).P))))) (\lambda (b: B).(\lambda (w: T).(\lambda (u: T).(\lambda (H: (eq 
T (TLRef n) (THead (Bind b) w u))).(\lambda (P: Prop).(let H0 \def (eq_ind T 
(TLRef n) (\lambda (ee: T).(match ee in T return (\lambda (_: T).Prop) with 
[(TSort _) \Rightarrow False | (TLRef _) \Rightarrow True | (THead _ _ _) 
\Rightarrow False])) I (THead (Bind b) w u) H) in (False_ind P H0))))))))) 
(\lambda (k: K).(K_ind (\lambda (k0: K).(\forall (t0: T).((or (ex_3 B T T 
(\lambda (b: B).(\lambda (w: T).(\lambda (u: T).(eq T t0 (THead (Bind b) w 
u)))))) (\forall (b: B).(\forall (w: T).(\forall (u: T).((eq T t0 (THead 
(Bind b) w u)) \to (\forall (P: Prop).P)))))) \to (\forall (t1: T).((or (ex_3 
B T T (\lambda (b: B).(\lambda (w: T).(\lambda (u: T).(eq T t1 (THead (Bind 
b) w u)))))) (\forall (b: B).(\forall (w: T).(\forall (u: T).((eq T t1 (THead 
(Bind b) w u)) \to (\forall (P: Prop).P)))))) \to (or (ex_3 B T T (\lambda 
(b: B).(\lambda (w: T).(\lambda (u: T).(eq T (THead k0 t0 t1) (THead (Bind b) 
w u)))))) (\forall (b: B).(\forall (w: T).(\forall (u: T).((eq T (THead k0 t0 
t1) (THead (Bind b) w u)) \to (\forall (P: Prop).P))))))))))) (\lambda (b: 
B).(\lambda (t0: T).(\lambda (_: (or (ex_3 B T T (\lambda (b0: B).(\lambda 
(w: T).(\lambda (u: T).(eq T t0 (THead (Bind b0) w u)))))) (\forall (b0: 
B).(\forall (w: T).(\forall (u: T).((eq T t0 (THead (Bind b0) w u)) \to 
(\forall (P: Prop).P))))))).(\lambda (t1: T).(\lambda (_: (or (ex_3 B T T 
(\lambda (b0: B).(\lambda (w: T).(\lambda (u: T).(eq T t1 (THead (Bind b0) w 
u)))))) (\forall (b0: B).(\forall (w: T).(\forall (u: T).((eq T t1 (THead 
(Bind b0) w u)) \to (\forall (P: Prop).P))))))).(or_introl (ex_3 B T T 
(\lambda (b0: B).(\lambda (w: T).(\lambda (u: T).(eq T (THead (Bind b) t0 t1) 
(THead (Bind b0) w u)))))) (\forall (b0: B).(\forall (w: T).(\forall (u: 
T).((eq T (THead (Bind b) t0 t1) (THead (Bind b0) w u)) \to (\forall (P: 
Prop).P))))) (ex_3_intro B T T (\lambda (b0: B).(\lambda (w: T).(\lambda (u: 
T).(eq T (THead (Bind b) t0 t1) (THead (Bind b0) w u))))) b t0 t1 (refl_equal 
T (THead (Bind b) t0 t1))))))))) (\lambda (f: F).(\lambda (t0: T).(\lambda 
(_: (or (ex_3 B T T (\lambda (b: B).(\lambda (w: T).(\lambda (u: T).(eq T t0 
(THead (Bind b) w u)))))) (\forall (b: B).(\forall (w: T).(\forall (u: 
T).((eq T t0 (THead (Bind b) w u)) \to (\forall (P: Prop).P))))))).(\lambda 
(t1: T).(\lambda (_: (or (ex_3 B T T (\lambda (b: B).(\lambda (w: T).(\lambda 
(u: T).(eq T t1 (THead (Bind b) w u)))))) (\forall (b: B).(\forall (w: 
T).(\forall (u: T).((eq T t1 (THead (Bind b) w u)) \to (\forall (P: 
Prop).P))))))).(or_intror (ex_3 B T T (\lambda (b: B).(\lambda (w: 
T).(\lambda (u: T).(eq T (THead (Flat f) t0 t1) (THead (Bind b) w u)))))) 
(\forall (b: B).(\forall (w: T).(\forall (u: T).((eq T (THead (Flat f) t0 t1) 
(THead (Bind b) w u)) \to (\forall (P: Prop).P))))) (\lambda (b: B).(\lambda 
(w: T).(\lambda (u: T).(\lambda (H1: (eq T (THead (Flat f) t0 t1) (THead 
(Bind b) w u))).(\lambda (P: Prop).(let H2 \def (eq_ind T (THead (Flat f) t0 
t1) (\lambda (ee: T).(match ee in T return (\lambda (_: T).Prop) with [(TSort 
_) \Rightarrow False | (TLRef _) \Rightarrow False | (THead k0 _ _) 
\Rightarrow (match k0 in K return (\lambda (_: K).Prop) with [(Bind _) 
\Rightarrow False | (Flat _) \Rightarrow True])])) I (THead (Bind b) w u) H1) 
in (False_ind P H2))))))))))))) k)) t).
(* COMMENTS
Initial nodes: 1063
END *)

theorem abst_dec:
 \forall (u: T).(\forall (v: T).(or (ex T (\lambda (t: T).(eq T u (THead 
(Bind Abst) v t)))) (\forall (t: T).((eq T u (THead (Bind Abst) v t)) \to 
(\forall (P: Prop).P)))))
\def
 \lambda (u: T).(T_ind (\lambda (t: T).(\forall (v: T).(or (ex T (\lambda 
(t0: T).(eq T t (THead (Bind Abst) v t0)))) (\forall (t0: T).((eq T t (THead 
(Bind Abst) v t0)) \to (\forall (P: Prop).P)))))) (\lambda (n: nat).(\lambda 
(v: T).(or_intror (ex T (\lambda (t: T).(eq T (TSort n) (THead (Bind Abst) v 
t)))) (\forall (t: T).((eq T (TSort n) (THead (Bind Abst) v t)) \to (\forall 
(P: Prop).P))) (\lambda (t: T).(\lambda (H: (eq T (TSort n) (THead (Bind 
Abst) v t))).(\lambda (P: Prop).(let H0 \def (eq_ind T (TSort n) (\lambda 
(ee: T).(match ee in T return (\lambda (_: T).Prop) with [(TSort _) 
\Rightarrow True | (TLRef _) \Rightarrow False | (THead _ _ _) \Rightarrow 
False])) I (THead (Bind Abst) v t) H) in (False_ind P H0)))))))) (\lambda (n: 
nat).(\lambda (v: T).(or_intror (ex T (\lambda (t: T).(eq T (TLRef n) (THead 
(Bind Abst) v t)))) (\forall (t: T).((eq T (TLRef n) (THead (Bind Abst) v t)) 
\to (\forall (P: Prop).P))) (\lambda (t: T).(\lambda (H: (eq T (TLRef n) 
(THead (Bind Abst) v t))).(\lambda (P: Prop).(let H0 \def (eq_ind T (TLRef n) 
(\lambda (ee: T).(match ee in T return (\lambda (_: T).Prop) with [(TSort _) 
\Rightarrow False | (TLRef _) \Rightarrow True | (THead _ _ _) \Rightarrow 
False])) I (THead (Bind Abst) v t) H) in (False_ind P H0)))))))) (\lambda (k: 
K).(\lambda (t: T).(\lambda (_: ((\forall (v: T).(or (ex T (\lambda (t0: 
T).(eq T t (THead (Bind Abst) v t0)))) (\forall (t0: T).((eq T t (THead (Bind 
Abst) v t0)) \to (\forall (P: Prop).P))))))).(\lambda (t0: T).(\lambda (_: 
((\forall (v: T).(or (ex T (\lambda (t1: T).(eq T t0 (THead (Bind Abst) v 
t1)))) (\forall (t1: T).((eq T t0 (THead (Bind Abst) v t1)) \to (\forall (P: 
Prop).P))))))).(\lambda (v: T).(let H_x \def (terms_props__kind_dec k (Bind 
Abst)) in (let H1 \def H_x in (or_ind (eq K k (Bind Abst)) ((eq K k (Bind 
Abst)) \to (\forall (P: Prop).P)) (or (ex T (\lambda (t1: T).(eq T (THead k t 
t0) (THead (Bind Abst) v t1)))) (\forall (t1: T).((eq T (THead k t t0) (THead 
(Bind Abst) v t1)) \to (\forall (P: Prop).P)))) (\lambda (H2: (eq K k (Bind 
Abst))).(eq_ind_r K (Bind Abst) (\lambda (k0: K).(or (ex T (\lambda (t1: 
T).(eq T (THead k0 t t0) (THead (Bind Abst) v t1)))) (\forall (t1: T).((eq T 
(THead k0 t t0) (THead (Bind Abst) v t1)) \to (\forall (P: Prop).P))))) (let 
H_x0 \def (term_dec t v) in (let H3 \def H_x0 in (or_ind (eq T t v) ((eq T t 
v) \to (\forall (P: Prop).P)) (or (ex T (\lambda (t1: T).(eq T (THead (Bind 
Abst) t t0) (THead (Bind Abst) v t1)))) (\forall (t1: T).((eq T (THead (Bind 
Abst) t t0) (THead (Bind Abst) v t1)) \to (\forall (P: Prop).P)))) (\lambda 
(H4: (eq T t v)).(eq_ind T t (\lambda (t1: T).(or (ex T (\lambda (t2: T).(eq 
T (THead (Bind Abst) t t0) (THead (Bind Abst) t1 t2)))) (\forall (t2: T).((eq 
T (THead (Bind Abst) t t0) (THead (Bind Abst) t1 t2)) \to (\forall (P: 
Prop).P))))) (or_introl (ex T (\lambda (t1: T).(eq T (THead (Bind Abst) t t0) 
(THead (Bind Abst) t t1)))) (\forall (t1: T).((eq T (THead (Bind Abst) t t0) 
(THead (Bind Abst) t t1)) \to (\forall (P: Prop).P))) (ex_intro T (\lambda 
(t1: T).(eq T (THead (Bind Abst) t t0) (THead (Bind Abst) t t1))) t0 
(refl_equal T (THead (Bind Abst) t t0)))) v H4)) (\lambda (H4: (((eq T t v) 
\to (\forall (P: Prop).P)))).(or_intror (ex T (\lambda (t1: T).(eq T (THead 
(Bind Abst) t t0) (THead (Bind Abst) v t1)))) (\forall (t1: T).((eq T (THead 
(Bind Abst) t t0) (THead (Bind Abst) v t1)) \to (\forall (P: Prop).P))) 
(\lambda (t1: T).(\lambda (H5: (eq T (THead (Bind Abst) t t0) (THead (Bind 
Abst) v t1))).(\lambda (P: Prop).(let H6 \def (f_equal T T (\lambda (e: 
T).(match e in T return (\lambda (_: T).T) with [(TSort _) \Rightarrow t | 
(TLRef _) \Rightarrow t | (THead _ t2 _) \Rightarrow t2])) (THead (Bind Abst) 
t t0) (THead (Bind Abst) v t1) H5) in ((let H7 \def (f_equal T T (\lambda (e: 
T).(match e in T return (\lambda (_: T).T) with [(TSort _) \Rightarrow t0 | 
(TLRef _) \Rightarrow t0 | (THead _ _ t2) \Rightarrow t2])) (THead (Bind 
Abst) t t0) (THead (Bind Abst) v t1) H5) in (\lambda (H8: (eq T t v)).(H4 H8 
P))) H6))))))) H3))) k H2)) (\lambda (H2: (((eq K k (Bind Abst)) \to (\forall 
(P: Prop).P)))).(or_intror (ex T (\lambda (t1: T).(eq T (THead k t t0) (THead 
(Bind Abst) v t1)))) (\forall (t1: T).((eq T (THead k t t0) (THead (Bind 
Abst) v t1)) \to (\forall (P: Prop).P))) (\lambda (t1: T).(\lambda (H3: (eq T 
(THead k t t0) (THead (Bind Abst) v t1))).(\lambda (P: Prop).(let H4 \def 
(f_equal T K (\lambda (e: T).(match e in T return (\lambda (_: T).K) with 
[(TSort _) \Rightarrow k | (TLRef _) \Rightarrow k | (THead k0 _ _) 
\Rightarrow k0])) (THead k t t0) (THead (Bind Abst) v t1) H3) in ((let H5 
\def (f_equal T T (\lambda (e: T).(match e in T return (\lambda (_: T).T) 
with [(TSort _) \Rightarrow t | (TLRef _) \Rightarrow t | (THead _ t2 _) 
\Rightarrow t2])) (THead k t t0) (THead (Bind Abst) v t1) H3) in ((let H6 
\def (f_equal T T (\lambda (e: T).(match e in T return (\lambda (_: T).T) 
with [(TSort _) \Rightarrow t0 | (TLRef _) \Rightarrow t0 | (THead _ _ t2) 
\Rightarrow t2])) (THead k t t0) (THead (Bind Abst) v t1) H3) in (\lambda (_: 
(eq T t v)).(\lambda (H8: (eq K k (Bind Abst))).(H2 H8 P)))) H5)) H4))))))) 
H1))))))))) u).
(* COMMENTS
Initial nodes: 1305
END *)

