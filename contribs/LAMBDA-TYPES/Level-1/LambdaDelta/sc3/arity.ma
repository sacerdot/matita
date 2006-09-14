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

set "baseuri" "cic:/matita/LAMBDA-TYPES/Level-1/LambdaDelta/sc3/arity".

include "ceqc/props.ma".

theorem sc3_arity:
 \forall (g: G).(\forall (c: C).(\forall (t: T).(\forall (a: A).((arity g c t 
a) \to (sc3 g a c t)))))
\def
 \lambda (g: G).(\lambda (c: C).(\lambda (t: T).(\lambda (a: A).(\lambda (H: 
(arity g c t a)).(arity_ind g (\lambda (c0: C).(\lambda (t0: T).(\lambda (a0: 
A).(sc3 g a0 c0 t0)))) (\lambda (c0: C).(\lambda (n: nat).(conj (arity g c0 
(TSort n) (ASort O n)) (sn3 c0 (TSort n)) (arity_sort g c0 n) (sn3_nf2 c0 
(TSort n) (nf2_sort c0 n))))) (\lambda (c0: C).(\lambda (d: C).(\lambda (u: 
T).(\lambda (i: nat).(\lambda (H0: (getl i c0 (CHead d (Bind Abbr) 
u))).(\lambda (a0: A).(\lambda (_: (arity g d u a0)).(\lambda (H2: (sc3 g a0 
d u)).(let H_y \def (sc3_abbr g a0 TNil) in (H_y i d u c0 (sc3_lift g a0 d u 
H2 c0 (S i) O (getl_drop Abbr c0 d u i H0)) H0)))))))))) (\lambda (c0: 
C).(\lambda (d: C).(\lambda (u: T).(\lambda (i: nat).(\lambda (H0: (getl i c0 
(CHead d (Bind Abst) u))).(\lambda (a0: A).(\lambda (H1: (arity g d u (asucc 
g a0))).(\lambda (_: (sc3 g (asucc g a0) d u)).(let H3 \def (sc3_abst g a0 
TNil) in (H3 c0 i (arity_abst g c0 d u i H0 a0 H1) (nf2_lref_abst c0 d u i 
H0) I)))))))))) (\lambda (b: B).(\lambda (H0: (not (eq B b Abst))).(\lambda 
(c0: C).(\lambda (u: T).(\lambda (a1: A).(\lambda (_: (arity g c0 u 
a1)).(\lambda (H2: (sc3 g a1 c0 u)).(\lambda (t0: T).(\lambda (a2: 
A).(\lambda (_: (arity g (CHead c0 (Bind b) u) t0 a2)).(\lambda (H4: (sc3 g 
a2 (CHead c0 (Bind b) u) t0)).(let H_y \def (sc3_bind g b H0 a1 a2 TNil) in 
(H_y c0 u t0 H4 H2))))))))))))) (\lambda (c0: C).(\lambda (u: T).(\lambda 
(a1: A).(\lambda (H0: (arity g c0 u (asucc g a1))).(\lambda (H1: (sc3 g 
(asucc g a1) c0 u)).(\lambda (t0: T).(\lambda (a2: A).(\lambda (H2: (arity g 
(CHead c0 (Bind Abst) u) t0 a2)).(\lambda (H3: (sc3 g a2 (CHead c0 (Bind 
Abst) u) t0)).(conj (arity g c0 (THead (Bind Abst) u t0) (AHead a1 a2)) 
(\forall (d: C).(\forall (w: T).((sc3 g a1 d w) \to (\forall (is: 
PList).((drop1 is d c0) \to (sc3 g a2 d (THead (Flat Appl) w (lift1 is (THead 
(Bind Abst) u t0))))))))) (arity_head g c0 u a1 H0 t0 a2 H2) (\lambda (d: 
C).(\lambda (w: T).(\lambda (H4: (sc3 g a1 d w)).(\lambda (is: 
PList).(\lambda (H5: (drop1 is d c0)).(let H6 \def (sc3_appl g a1 a2 TNil) in 
(eq_ind_r T (THead (Bind Abst) (lift1 is u) (lift1 (Ss is) t0)) (\lambda (t1: 
T).(sc3 g a2 d (THead (Flat Appl) w t1))) (H6 d w (lift1 (Ss is) t0) (let H_y 
\def (sc3_bind g Abbr (\lambda (H7: (eq B Abbr Abst)).(not_abbr_abst H7)) a1 
a2 TNil) in (H_y d w (lift1 (Ss is) t0) (let H7 \def (sc3_ceqc_trans g a2 
TNil) in (H7 (CHead d (Bind Abst) (lift1 is u)) (lift1 (Ss is) t0) (sc3_lift1 
g (CHead c0 (Bind Abst) u) a2 (Ss is) (CHead d (Bind Abst) (lift1 is u)) t0 
H3 (drop1_skip_bind Abst c0 is d u H5)) (CHead d (Bind Abbr) w) (or_intror 
(csubc g (CHead d (Bind Abbr) w) (CHead d (Bind Abst) (lift1 is u))) (csubc g 
(CHead d (Bind Abst) (lift1 is u)) (CHead d (Bind Abbr) w)) (csubc_abst g d d 
(csubc_refl g d) (lift1 is u) a1 (sc3_lift1 g c0 (asucc g a1) is d u H1 H5) w 
H4)))) H4)) H4 (lift1 is u) (sc3_lift1 g c0 (asucc g a1) is d u H1 H5)) 
(lift1 is (THead (Bind Abst) u t0)) (lift1_bind Abst is u 
t0)))))))))))))))))) (\lambda (c0: C).(\lambda (u: T).(\lambda (a1: 
A).(\lambda (_: (arity g c0 u a1)).(\lambda (H1: (sc3 g a1 c0 u)).(\lambda 
(t0: T).(\lambda (a2: A).(\lambda (_: (arity g c0 t0 (AHead a1 a2))).(\lambda 
(H3: (sc3 g (AHead a1 a2) c0 t0)).(let H4 \def H3 in (and_ind (arity g c0 t0 
(AHead a1 a2)) (\forall (d: C).(\forall (w: T).((sc3 g a1 d w) \to (\forall 
(is: PList).((drop1 is d c0) \to (sc3 g a2 d (THead (Flat Appl) w (lift1 is 
t0)))))))) (sc3 g a2 c0 (THead (Flat Appl) u t0)) (\lambda (_: (arity g c0 t0 
(AHead a1 a2))).(\lambda (H6: ((\forall (d: C).(\forall (w: T).((sc3 g a1 d 
w) \to (\forall (is: PList).((drop1 is d c0) \to (sc3 g a2 d (THead (Flat 
Appl) w (lift1 is t0)))))))))).(let H_y \def (H6 c0 u H1 PNil) in (H_y 
(drop1_nil c0))))) H4))))))))))) (\lambda (c0: C).(\lambda (u: T).(\lambda 
(a0: A).(\lambda (_: (arity g c0 u (asucc g a0))).(\lambda (H1: (sc3 g (asucc 
g a0) c0 u)).(\lambda (t0: T).(\lambda (_: (arity g c0 t0 a0)).(\lambda (H3: 
(sc3 g a0 c0 t0)).(let H_y \def (sc3_cast g a0 TNil) in (H_y c0 u H1 t0 
H3)))))))))) (\lambda (c0: C).(\lambda (t0: T).(\lambda (a1: A).(\lambda (_: 
(arity g c0 t0 a1)).(\lambda (H1: (sc3 g a1 c0 t0)).(\lambda (a2: A).(\lambda 
(H2: (leq g a1 a2)).(sc3_repl g a1 c0 t0 H1 a2 H2)))))))) c t a H))))).

