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

include "Basic-1/pr2/clen.ma".

include "Basic-1/pr2/fwd.ma".

include "Basic-1/pr0/dec.ma".

include "Basic-1/C/props.ma".

theorem nf2_dec:
 \forall (c: C).(\forall (t1: T).(or (nf2 c t1) (ex2 T (\lambda (t2: T).((eq 
T t1 t2) \to (\forall (P: Prop).P))) (\lambda (t2: T).(pr2 c t1 t2)))))
\def
 \lambda (c: C).(c_tail_ind (\lambda (c0: C).(\forall (t1: T).(or (\forall 
(t2: T).((pr2 c0 t1 t2) \to (eq T t1 t2))) (ex2 T (\lambda (t2: T).((eq T t1 
t2) \to (\forall (P: Prop).P))) (\lambda (t2: T).(pr2 c0 t1 t2)))))) (\lambda 
(n: nat).(\lambda (t1: T).(let H_x \def (nf0_dec t1) in (let H \def H_x in 
(or_ind (\forall (t2: T).((pr0 t1 t2) \to (eq T t1 t2))) (ex2 T (\lambda (t2: 
T).((eq T t1 t2) \to (\forall (P: Prop).P))) (\lambda (t2: T).(pr0 t1 t2))) 
(or (\forall (t2: T).((pr2 (CSort n) t1 t2) \to (eq T t1 t2))) (ex2 T 
(\lambda (t2: T).((eq T t1 t2) \to (\forall (P: Prop).P))) (\lambda (t2: 
T).(pr2 (CSort n) t1 t2)))) (\lambda (H0: ((\forall (t2: T).((pr0 t1 t2) \to 
(eq T t1 t2))))).(or_introl (\forall (t2: T).((pr2 (CSort n) t1 t2) \to (eq T 
t1 t2))) (ex2 T (\lambda (t2: T).((eq T t1 t2) \to (\forall (P: Prop).P))) 
(\lambda (t2: T).(pr2 (CSort n) t1 t2))) (\lambda (t2: T).(\lambda (H1: (pr2 
(CSort n) t1 t2)).(let H_y \def (pr2_gen_csort t1 t2 n H1) in (H0 t2 
H_y)))))) (\lambda (H0: (ex2 T (\lambda (t2: T).((eq T t1 t2) \to (\forall 
(P: Prop).P))) (\lambda (t2: T).(pr0 t1 t2)))).(ex2_ind T (\lambda (t2: 
T).((eq T t1 t2) \to (\forall (P: Prop).P))) (\lambda (t2: T).(pr0 t1 t2)) 
(or (\forall (t2: T).((pr2 (CSort n) t1 t2) \to (eq T t1 t2))) (ex2 T 
(\lambda (t2: T).((eq T t1 t2) \to (\forall (P: Prop).P))) (\lambda (t2: 
T).(pr2 (CSort n) t1 t2)))) (\lambda (x: T).(\lambda (H1: (((eq T t1 x) \to 
(\forall (P: Prop).P)))).(\lambda (H2: (pr0 t1 x)).(or_intror (\forall (t2: 
T).((pr2 (CSort n) t1 t2) \to (eq T t1 t2))) (ex2 T (\lambda (t2: T).((eq T 
t1 t2) \to (\forall (P: Prop).P))) (\lambda (t2: T).(pr2 (CSort n) t1 t2))) 
(ex_intro2 T (\lambda (t2: T).((eq T t1 t2) \to (\forall (P: Prop).P))) 
(\lambda (t2: T).(pr2 (CSort n) t1 t2)) x H1 (pr2_free (CSort n) t1 x 
H2)))))) H0)) H))))) (\lambda (c0: C).(\lambda (H: ((\forall (t1: T).(or 
(\forall (t2: T).((pr2 c0 t1 t2) \to (eq T t1 t2))) (ex2 T (\lambda (t2: 
T).((eq T t1 t2) \to (\forall (P: Prop).P))) (\lambda (t2: T).(pr2 c0 t1 
t2))))))).(\lambda (k: K).(\lambda (t: T).(\lambda (t1: T).(let H_x \def (H 
t1) in (let H0 \def H_x in (or_ind (\forall (t2: T).((pr2 c0 t1 t2) \to (eq T 
t1 t2))) (ex2 T (\lambda (t2: T).((eq T t1 t2) \to (\forall (P: Prop).P))) 
(\lambda (t2: T).(pr2 c0 t1 t2))) (or (\forall (t2: T).((pr2 (CTail k t c0) 
t1 t2) \to (eq T t1 t2))) (ex2 T (\lambda (t2: T).((eq T t1 t2) \to (\forall 
(P: Prop).P))) (\lambda (t2: T).(pr2 (CTail k t c0) t1 t2)))) (\lambda (H1: 
((\forall (t2: T).((pr2 c0 t1 t2) \to (eq T t1 t2))))).(K_ind (\lambda (k0: 
K).(or (\forall (t2: T).((pr2 (CTail k0 t c0) t1 t2) \to (eq T t1 t2))) (ex2 
T (\lambda (t2: T).((eq T t1 t2) \to (\forall (P: Prop).P))) (\lambda (t2: 
T).(pr2 (CTail k0 t c0) t1 t2))))) (\lambda (b: B).(B_ind (\lambda (b0: 
B).(or (\forall (t2: T).((pr2 (CTail (Bind b0) t c0) t1 t2) \to (eq T t1 
t2))) (ex2 T (\lambda (t2: T).((eq T t1 t2) \to (\forall (P: Prop).P))) 
(\lambda (t2: T).(pr2 (CTail (Bind b0) t c0) t1 t2))))) (let H_x0 \def 
(dnf_dec t t1 (clen c0)) in (let H2 \def H_x0 in (ex_ind T (\lambda (v: 
T).(or (subst0 (clen c0) t t1 (lift (S O) (clen c0) v)) (eq T t1 (lift (S O) 
(clen c0) v)))) (or (\forall (t2: T).((pr2 (CTail (Bind Abbr) t c0) t1 t2) 
\to (eq T t1 t2))) (ex2 T (\lambda (t2: T).((eq T t1 t2) \to (\forall (P: 
Prop).P))) (\lambda (t2: T).(pr2 (CTail (Bind Abbr) t c0) t1 t2)))) (\lambda 
(x: T).(\lambda (H3: (or (subst0 (clen c0) t t1 (lift (S O) (clen c0) x)) (eq 
T t1 (lift (S O) (clen c0) x)))).(or_ind (subst0 (clen c0) t t1 (lift (S O) 
(clen c0) x)) (eq T t1 (lift (S O) (clen c0) x)) (or (\forall (t2: T).((pr2 
(CTail (Bind Abbr) t c0) t1 t2) \to (eq T t1 t2))) (ex2 T (\lambda (t2: 
T).((eq T t1 t2) \to (\forall (P: Prop).P))) (\lambda (t2: T).(pr2 (CTail 
(Bind Abbr) t c0) t1 t2)))) (\lambda (H4: (subst0 (clen c0) t t1 (lift (S O) 
(clen c0) x))).(let H_x1 \def (getl_ctail_clen Abbr t c0) in (let H5 \def 
H_x1 in (ex_ind nat (\lambda (n: nat).(getl (clen c0) (CTail (Bind Abbr) t 
c0) (CHead (CSort n) (Bind Abbr) t))) (or (\forall (t2: T).((pr2 (CTail (Bind 
Abbr) t c0) t1 t2) \to (eq T t1 t2))) (ex2 T (\lambda (t2: T).((eq T t1 t2) 
\to (\forall (P: Prop).P))) (\lambda (t2: T).(pr2 (CTail (Bind Abbr) t c0) t1 
t2)))) (\lambda (x0: nat).(\lambda (H6: (getl (clen c0) (CTail (Bind Abbr) t 
c0) (CHead (CSort x0) (Bind Abbr) t))).(or_intror (\forall (t2: T).((pr2 
(CTail (Bind Abbr) t c0) t1 t2) \to (eq T t1 t2))) (ex2 T (\lambda (t2: 
T).((eq T t1 t2) \to (\forall (P: Prop).P))) (\lambda (t2: T).(pr2 (CTail 
(Bind Abbr) t c0) t1 t2))) (ex_intro2 T (\lambda (t2: T).((eq T t1 t2) \to 
(\forall (P: Prop).P))) (\lambda (t2: T).(pr2 (CTail (Bind Abbr) t c0) t1 
t2)) (lift (S O) (clen c0) x) (\lambda (H7: (eq T t1 (lift (S O) (clen c0) 
x))).(\lambda (P: Prop).(let H8 \def (eq_ind T t1 (\lambda (t0: T).(subst0 
(clen c0) t t0 (lift (S O) (clen c0) x))) H4 (lift (S O) (clen c0) x) H7) in 
(subst0_gen_lift_false x t (lift (S O) (clen c0) x) (S O) (clen c0) (clen c0) 
(le_n (clen c0)) (eq_ind_r nat (plus (S O) (clen c0)) (\lambda (n: nat).(lt 
(clen c0) n)) (le_n (plus (S O) (clen c0))) (plus (clen c0) (S O)) (plus_sym 
(clen c0) (S O))) H8 P)))) (pr2_delta (CTail (Bind Abbr) t c0) (CSort x0) t 
(clen c0) H6 t1 t1 (pr0_refl t1) (lift (S O) (clen c0) x) H4))))) H5)))) 
(\lambda (H4: (eq T t1 (lift (S O) (clen c0) x))).(let H5 \def (eq_ind T t1 
(\lambda (t0: T).(\forall (t2: T).((pr2 c0 t0 t2) \to (eq T t0 t2)))) H1 
(lift (S O) (clen c0) x) H4) in (eq_ind_r T (lift (S O) (clen c0) x) (\lambda 
(t0: T).(or (\forall (t2: T).((pr2 (CTail (Bind Abbr) t c0) t0 t2) \to (eq T 
t0 t2))) (ex2 T (\lambda (t2: T).((eq T t0 t2) \to (\forall (P: Prop).P))) 
(\lambda (t2: T).(pr2 (CTail (Bind Abbr) t c0) t0 t2))))) (or_introl (\forall 
(t2: T).((pr2 (CTail (Bind Abbr) t c0) (lift (S O) (clen c0) x) t2) \to (eq T 
(lift (S O) (clen c0) x) t2))) (ex2 T (\lambda (t2: T).((eq T (lift (S O) 
(clen c0) x) t2) \to (\forall (P: Prop).P))) (\lambda (t2: T).(pr2 (CTail 
(Bind Abbr) t c0) (lift (S O) (clen c0) x) t2))) (\lambda (t2: T).(\lambda 
(H6: (pr2 (CTail (Bind Abbr) t c0) (lift (S O) (clen c0) x) t2)).(let H_x1 
\def (pr2_gen_ctail (Bind Abbr) c0 t (lift (S O) (clen c0) x) t2 H6) in (let 
H7 \def H_x1 in (or_ind (pr2 c0 (lift (S O) (clen c0) x) t2) (ex3 T (\lambda 
(_: T).(eq K (Bind Abbr) (Bind Abbr))) (\lambda (t0: T).(pr0 (lift (S O) 
(clen c0) x) t0)) (\lambda (t0: T).(subst0 (clen c0) t t0 t2))) (eq T (lift 
(S O) (clen c0) x) t2) (\lambda (H8: (pr2 c0 (lift (S O) (clen c0) x) 
t2)).(H5 t2 H8)) (\lambda (H8: (ex3 T (\lambda (_: T).(eq K (Bind Abbr) (Bind 
Abbr))) (\lambda (t0: T).(pr0 (lift (S O) (clen c0) x) t0)) (\lambda (t0: 
T).(subst0 (clen c0) t t0 t2)))).(ex3_ind T (\lambda (_: T).(eq K (Bind Abbr) 
(Bind Abbr))) (\lambda (t0: T).(pr0 (lift (S O) (clen c0) x) t0)) (\lambda 
(t0: T).(subst0 (clen c0) t t0 t2)) (eq T (lift (S O) (clen c0) x) t2) 
(\lambda (x0: T).(\lambda (_: (eq K (Bind Abbr) (Bind Abbr))).(\lambda (H10: 
(pr0 (lift (S O) (clen c0) x) x0)).(\lambda (H11: (subst0 (clen c0) t x0 
t2)).(ex2_ind T (\lambda (t3: T).(eq T x0 (lift (S O) (clen c0) t3))) 
(\lambda (t3: T).(pr0 x t3)) (eq T (lift (S O) (clen c0) x) t2) (\lambda (x1: 
T).(\lambda (H12: (eq T x0 (lift (S O) (clen c0) x1))).(\lambda (_: (pr0 x 
x1)).(let H14 \def (eq_ind T x0 (\lambda (t0: T).(subst0 (clen c0) t t0 t2)) 
H11 (lift (S O) (clen c0) x1) H12) in (subst0_gen_lift_false x1 t t2 (S O) 
(clen c0) (clen c0) (le_n (clen c0)) (eq_ind_r nat (plus (S O) (clen c0)) 
(\lambda (n: nat).(lt (clen c0) n)) (le_n (plus (S O) (clen c0))) (plus (clen 
c0) (S O)) (plus_sym (clen c0) (S O))) H14 (eq T (lift (S O) (clen c0) x) 
t2)))))) (pr0_gen_lift x x0 (S O) (clen c0) H10)))))) H8)) H7)))))) t1 H4))) 
H3))) H2))) (or_introl (\forall (t2: T).((pr2 (CTail (Bind Abst) t c0) t1 t2) 
\to (eq T t1 t2))) (ex2 T (\lambda (t2: T).((eq T t1 t2) \to (\forall (P: 
Prop).P))) (\lambda (t2: T).(pr2 (CTail (Bind Abst) t c0) t1 t2))) (\lambda 
(t2: T).(\lambda (H2: (pr2 (CTail (Bind Abst) t c0) t1 t2)).(let H_x0 \def 
(pr2_gen_ctail (Bind Abst) c0 t t1 t2 H2) in (let H3 \def H_x0 in (or_ind 
(pr2 c0 t1 t2) (ex3 T (\lambda (_: T).(eq K (Bind Abst) (Bind Abbr))) 
(\lambda (t0: T).(pr0 t1 t0)) (\lambda (t0: T).(subst0 (clen c0) t t0 t2))) 
(eq T t1 t2) (\lambda (H4: (pr2 c0 t1 t2)).(H1 t2 H4)) (\lambda (H4: (ex3 T 
(\lambda (_: T).(eq K (Bind Abst) (Bind Abbr))) (\lambda (t0: T).(pr0 t1 t0)) 
(\lambda (t0: T).(subst0 (clen c0) t t0 t2)))).(ex3_ind T (\lambda (_: T).(eq 
K (Bind Abst) (Bind Abbr))) (\lambda (t0: T).(pr0 t1 t0)) (\lambda (t0: 
T).(subst0 (clen c0) t t0 t2)) (eq T t1 t2) (\lambda (x0: T).(\lambda (H5: 
(eq K (Bind Abst) (Bind Abbr))).(\lambda (_: (pr0 t1 x0)).(\lambda (_: 
(subst0 (clen c0) t x0 t2)).(let H8 \def (eq_ind K (Bind Abst) (\lambda (ee: 
K).(match ee in K return (\lambda (_: K).Prop) with [(Bind b0) \Rightarrow 
(match b0 in B return (\lambda (_: B).Prop) with [Abbr \Rightarrow False | 
Abst \Rightarrow True | Void \Rightarrow False]) | (Flat _) \Rightarrow 
False])) I (Bind Abbr) H5) in (False_ind (eq T t1 t2) H8)))))) H4)) H3)))))) 
(or_introl (\forall (t2: T).((pr2 (CTail (Bind Void) t c0) t1 t2) \to (eq T 
t1 t2))) (ex2 T (\lambda (t2: T).((eq T t1 t2) \to (\forall (P: Prop).P))) 
(\lambda (t2: T).(pr2 (CTail (Bind Void) t c0) t1 t2))) (\lambda (t2: 
T).(\lambda (H2: (pr2 (CTail (Bind Void) t c0) t1 t2)).(let H_x0 \def 
(pr2_gen_ctail (Bind Void) c0 t t1 t2 H2) in (let H3 \def H_x0 in (or_ind 
(pr2 c0 t1 t2) (ex3 T (\lambda (_: T).(eq K (Bind Void) (Bind Abbr))) 
(\lambda (t0: T).(pr0 t1 t0)) (\lambda (t0: T).(subst0 (clen c0) t t0 t2))) 
(eq T t1 t2) (\lambda (H4: (pr2 c0 t1 t2)).(H1 t2 H4)) (\lambda (H4: (ex3 T 
(\lambda (_: T).(eq K (Bind Void) (Bind Abbr))) (\lambda (t0: T).(pr0 t1 t0)) 
(\lambda (t0: T).(subst0 (clen c0) t t0 t2)))).(ex3_ind T (\lambda (_: T).(eq 
K (Bind Void) (Bind Abbr))) (\lambda (t0: T).(pr0 t1 t0)) (\lambda (t0: 
T).(subst0 (clen c0) t t0 t2)) (eq T t1 t2) (\lambda (x0: T).(\lambda (H5: 
(eq K (Bind Void) (Bind Abbr))).(\lambda (_: (pr0 t1 x0)).(\lambda (_: 
(subst0 (clen c0) t x0 t2)).(let H8 \def (eq_ind K (Bind Void) (\lambda (ee: 
K).(match ee in K return (\lambda (_: K).Prop) with [(Bind b0) \Rightarrow 
(match b0 in B return (\lambda (_: B).Prop) with [Abbr \Rightarrow False | 
Abst \Rightarrow False | Void \Rightarrow True]) | (Flat _) \Rightarrow 
False])) I (Bind Abbr) H5) in (False_ind (eq T t1 t2) H8)))))) H4)) H3)))))) 
b)) (\lambda (f: F).(or_introl (\forall (t2: T).((pr2 (CTail (Flat f) t c0) 
t1 t2) \to (eq T t1 t2))) (ex2 T (\lambda (t2: T).((eq T t1 t2) \to (\forall 
(P: Prop).P))) (\lambda (t2: T).(pr2 (CTail (Flat f) t c0) t1 t2))) (\lambda 
(t2: T).(\lambda (H2: (pr2 (CTail (Flat f) t c0) t1 t2)).(let H_x0 \def 
(pr2_gen_ctail (Flat f) c0 t t1 t2 H2) in (let H3 \def H_x0 in (or_ind (pr2 
c0 t1 t2) (ex3 T (\lambda (_: T).(eq K (Flat f) (Bind Abbr))) (\lambda (t0: 
T).(pr0 t1 t0)) (\lambda (t0: T).(subst0 (clen c0) t t0 t2))) (eq T t1 t2) 
(\lambda (H4: (pr2 c0 t1 t2)).(H1 t2 H4)) (\lambda (H4: (ex3 T (\lambda (_: 
T).(eq K (Flat f) (Bind Abbr))) (\lambda (t0: T).(pr0 t1 t0)) (\lambda (t0: 
T).(subst0 (clen c0) t t0 t2)))).(ex3_ind T (\lambda (_: T).(eq K (Flat f) 
(Bind Abbr))) (\lambda (t0: T).(pr0 t1 t0)) (\lambda (t0: T).(subst0 (clen 
c0) t t0 t2)) (eq T t1 t2) (\lambda (x0: T).(\lambda (H5: (eq K (Flat f) 
(Bind Abbr))).(\lambda (_: (pr0 t1 x0)).(\lambda (_: (subst0 (clen c0) t x0 
t2)).(let H8 \def (eq_ind K (Flat f) (\lambda (ee: K).(match ee in K return 
(\lambda (_: K).Prop) with [(Bind _) \Rightarrow False | (Flat _) \Rightarrow 
True])) I (Bind Abbr) H5) in (False_ind (eq T t1 t2) H8)))))) H4)) H3))))))) 
k)) (\lambda (H1: (ex2 T (\lambda (t2: T).((eq T t1 t2) \to (\forall (P: 
Prop).P))) (\lambda (t2: T).(pr2 c0 t1 t2)))).(ex2_ind T (\lambda (t2: 
T).((eq T t1 t2) \to (\forall (P: Prop).P))) (\lambda (t2: T).(pr2 c0 t1 t2)) 
(or (\forall (t2: T).((pr2 (CTail k t c0) t1 t2) \to (eq T t1 t2))) (ex2 T 
(\lambda (t2: T).((eq T t1 t2) \to (\forall (P: Prop).P))) (\lambda (t2: 
T).(pr2 (CTail k t c0) t1 t2)))) (\lambda (x: T).(\lambda (H2: (((eq T t1 x) 
\to (\forall (P: Prop).P)))).(\lambda (H3: (pr2 c0 t1 x)).(or_intror (\forall 
(t2: T).((pr2 (CTail k t c0) t1 t2) \to (eq T t1 t2))) (ex2 T (\lambda (t2: 
T).((eq T t1 t2) \to (\forall (P: Prop).P))) (\lambda (t2: T).(pr2 (CTail k t 
c0) t1 t2))) (ex_intro2 T (\lambda (t2: T).((eq T t1 t2) \to (\forall (P: 
Prop).P))) (\lambda (t2: T).(pr2 (CTail k t c0) t1 t2)) x H2 (pr2_ctail c0 t1 
x H3 k t)))))) H1)) H0)))))))) c).
(* COMMENTS
Initial nodes: 3653
END *)

