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

set "baseuri" "cic:/matita/LAMBDA-TYPES/Level-1/LambdaDelta/ex1/props".

include "ex1/defs.ma".

include "ty3/fwd.ma".

include "pc3/fwd.ma".

include "nf2/pr3.ma".

include "nf2/props.ma".

include "arity/defs.ma".

include "leq/props.ma".

theorem ex1__leq_sort_SS:
 \forall (g: G).(\forall (k: nat).(\forall (n: nat).(leq g (ASort k n) (asucc 
g (asucc g (ASort (S (S k)) n))))))
\def
 \lambda (g: G).(\lambda (k: nat).(\lambda (n: nat).(leq_refl g (asucc g 
(asucc g (ASort (S (S k)) n)))))).

theorem ex1_arity:
 \forall (g: G).(arity g ex1_c ex1_t (ASort O O))
\def
 \lambda (g: G).(arity_appl g (CHead (CHead (CHead (CSort O) (Bind Abst) 
(TSort O)) (Bind Abst) (TSort O)) (Bind Abst) (TLRef O)) (TLRef O) (ASort (S 
(S O)) O) (arity_abst g (CHead (CHead (CHead (CSort O) (Bind Abst) (TSort O)) 
(Bind Abst) (TSort O)) (Bind Abst) (TLRef O)) (CHead (CHead (CSort O) (Bind 
Abst) (TSort O)) (Bind Abst) (TSort O)) (TLRef O) O (getl_refl Abst (CHead 
(CHead (CSort O) (Bind Abst) (TSort O)) (Bind Abst) (TSort O)) (TLRef O)) 
(ASort (S (S O)) O) (arity_abst g (CHead (CHead (CSort O) (Bind Abst) (TSort 
O)) (Bind Abst) (TSort O)) (CHead (CSort O) (Bind Abst) (TSort O)) (TSort O) 
O (getl_refl Abst (CHead (CSort O) (Bind Abst) (TSort O)) (TSort O)) (asucc g 
(ASort (S (S O)) O)) (arity_repl g (CHead (CSort O) (Bind Abst) (TSort O)) 
(TSort O) (ASort O O) (arity_sort g (CHead (CSort O) (Bind Abst) (TSort O)) 
O) (asucc g (asucc g (ASort (S (S O)) O))) (ex1__leq_sort_SS g O O)))) (THead 
(Bind Abst) (TLRef (S (S O))) (TSort O)) (ASort O O) (arity_head g (CHead 
(CHead (CHead (CSort O) (Bind Abst) (TSort O)) (Bind Abst) (TSort O)) (Bind 
Abst) (TLRef O)) (TLRef (S (S O))) (ASort (S (S O)) O) (arity_abst g (CHead 
(CHead (CHead (CSort O) (Bind Abst) (TSort O)) (Bind Abst) (TSort O)) (Bind 
Abst) (TLRef O)) (CSort O) (TSort O) (S (S O)) (getl_clear_bind Abst (CHead 
(CHead (CHead (CSort O) (Bind Abst) (TSort O)) (Bind Abst) (TSort O)) (Bind 
Abst) (TLRef O)) (CHead (CHead (CSort O) (Bind Abst) (TSort O)) (Bind Abst) 
(TSort O)) (TLRef O) (clear_bind Abst (CHead (CHead (CSort O) (Bind Abst) 
(TSort O)) (Bind Abst) (TSort O)) (TLRef O)) (CHead (CSort O) (Bind Abst) 
(TSort O)) (S O) (getl_head (Bind Abst) O (CHead (CSort O) (Bind Abst) (TSort 
O)) (CHead (CSort O) (Bind Abst) (TSort O)) (getl_refl Abst (CSort O) (TSort 
O)) (TSort O))) (asucc g (ASort (S (S O)) O)) (arity_repl g (CSort O) (TSort 
O) (ASort O O) (arity_sort g (CSort O) O) (asucc g (asucc g (ASort (S (S O)) 
O))) (ex1__leq_sort_SS g O O))) (TSort O) (ASort O O) (arity_sort g (CHead 
(CHead (CHead (CHead (CSort O) (Bind Abst) (TSort O)) (Bind Abst) (TSort O)) 
(Bind Abst) (TLRef O)) (Bind Abst) (TLRef (S (S O)))) O))).

theorem ex1_ty3:
 \forall (g: G).(\forall (u: T).((ty3 g ex1_c ex1_t u) \to (\forall (P: 
Prop).P)))
\def
 \lambda (g: G).(\lambda (u: T).(\lambda (H: (ty3 g (CHead (CHead (CHead 
(CSort O) (Bind Abst) (TSort O)) (Bind Abst) (TSort O)) (Bind Abst) (TLRef 
O)) (THead (Flat Appl) (TLRef O) (THead (Bind Abst) (TLRef (S (S O))) (TSort 
O))) u)).(\lambda (P: Prop).(ex3_2_ind T T (\lambda (u0: T).(\lambda (t: 
T).(pc3 (CHead (CHead (CHead (CSort O) (Bind Abst) (TSort O)) (Bind Abst) 
(TSort O)) (Bind Abst) (TLRef O)) (THead (Flat Appl) (TLRef O) (THead (Bind 
Abst) u0 t)) u))) (\lambda (u0: T).(\lambda (t: T).(ty3 g (CHead (CHead 
(CHead (CSort O) (Bind Abst) (TSort O)) (Bind Abst) (TSort O)) (Bind Abst) 
(TLRef O)) (THead (Bind Abst) (TLRef (S (S O))) (TSort O)) (THead (Bind Abst) 
u0 t)))) (\lambda (u0: T).(\lambda (_: T).(ty3 g (CHead (CHead (CHead (CSort 
O) (Bind Abst) (TSort O)) (Bind Abst) (TSort O)) (Bind Abst) (TLRef O)) 
(TLRef O) u0))) P (\lambda (x0: T).(\lambda (x1: T).(\lambda (_: (pc3 (CHead 
(CHead (CHead (CSort O) (Bind Abst) (TSort O)) (Bind Abst) (TSort O)) (Bind 
Abst) (TLRef O)) (THead (Flat Appl) (TLRef O) (THead (Bind Abst) x0 x1)) 
u)).(\lambda (H1: (ty3 g (CHead (CHead (CHead (CSort O) (Bind Abst) (TSort 
O)) (Bind Abst) (TSort O)) (Bind Abst) (TLRef O)) (THead (Bind Abst) (TLRef 
(S (S O))) (TSort O)) (THead (Bind Abst) x0 x1))).(\lambda (H2: (ty3 g (CHead 
(CHead (CHead (CSort O) (Bind Abst) (TSort O)) (Bind Abst) (TSort O)) (Bind 
Abst) (TLRef O)) (TLRef O) x0)).(or_ind (ex3_3 C T T (\lambda (_: C).(\lambda 
(_: T).(\lambda (t: T).(pc3 (CHead (CHead (CHead (CSort O) (Bind Abst) (TSort 
O)) (Bind Abst) (TSort O)) (Bind Abst) (TLRef O)) (lift (S O) O t) x0)))) 
(\lambda (e: C).(\lambda (u0: T).(\lambda (_: T).(getl O (CHead (CHead (CHead 
(CSort O) (Bind Abst) (TSort O)) (Bind Abst) (TSort O)) (Bind Abst) (TLRef 
O)) (CHead e (Bind Abbr) u0))))) (\lambda (e: C).(\lambda (u0: T).(\lambda 
(t: T).(ty3 g e u0 t))))) (ex3_3 C T T (\lambda (_: C).(\lambda (u0: 
T).(\lambda (_: T).(pc3 (CHead (CHead (CHead (CSort O) (Bind Abst) (TSort O)) 
(Bind Abst) (TSort O)) (Bind Abst) (TLRef O)) (lift (S O) O u0) x0)))) 
(\lambda (e: C).(\lambda (u0: T).(\lambda (_: T).(getl O (CHead (CHead (CHead 
(CSort O) (Bind Abst) (TSort O)) (Bind Abst) (TSort O)) (Bind Abst) (TLRef 
O)) (CHead e (Bind Abst) u0))))) (\lambda (e: C).(\lambda (u0: T).(\lambda 
(t: T).(ty3 g e u0 t))))) P (\lambda (H3: (ex3_3 C T T (\lambda (_: 
C).(\lambda (_: T).(\lambda (t: T).(pc3 (CHead (CHead (CHead (CSort O) (Bind 
Abst) (TSort O)) (Bind Abst) (TSort O)) (Bind Abst) (TLRef O)) (lift (S O) O 
t) x0)))) (\lambda (e: C).(\lambda (u0: T).(\lambda (_: T).(getl O (CHead 
(CHead (CHead (CSort O) (Bind Abst) (TSort O)) (Bind Abst) (TSort O)) (Bind 
Abst) (TLRef O)) (CHead e (Bind Abbr) u0))))) (\lambda (e: C).(\lambda (u0: 
T).(\lambda (t: T).(ty3 g e u0 t)))))).(ex3_3_ind C T T (\lambda (_: 
C).(\lambda (_: T).(\lambda (t: T).(pc3 (CHead (CHead (CHead (CSort O) (Bind 
Abst) (TSort O)) (Bind Abst) (TSort O)) (Bind Abst) (TLRef O)) (lift (S O) O 
t) x0)))) (\lambda (e: C).(\lambda (u0: T).(\lambda (_: T).(getl O (CHead 
(CHead (CHead (CSort O) (Bind Abst) (TSort O)) (Bind Abst) (TSort O)) (Bind 
Abst) (TLRef O)) (CHead e (Bind Abbr) u0))))) (\lambda (e: C).(\lambda (u0: 
T).(\lambda (t: T).(ty3 g e u0 t)))) P (\lambda (x2: C).(\lambda (x3: 
T).(\lambda (x4: T).(\lambda (_: (pc3 (CHead (CHead (CHead (CSort O) (Bind 
Abst) (TSort O)) (Bind Abst) (TSort O)) (Bind Abst) (TLRef O)) (lift (S O) O 
x4) x0)).(\lambda (H5: (getl O (CHead (CHead (CHead (CSort O) (Bind Abst) 
(TSort O)) (Bind Abst) (TSort O)) (Bind Abst) (TLRef O)) (CHead x2 (Bind 
Abbr) x3))).(\lambda (_: (ty3 g x2 x3 x4)).(ex4_3_ind T T T (\lambda (t2: 
T).(\lambda (_: T).(\lambda (_: T).(pc3 (CHead (CHead (CHead (CSort O) (Bind 
Abst) (TSort O)) (Bind Abst) (TSort O)) (Bind Abst) (TLRef O)) (THead (Bind 
Abst) (TLRef (S (S O))) t2) (THead (Bind Abst) x0 x1))))) (\lambda (_: 
T).(\lambda (t: T).(\lambda (_: T).(ty3 g (CHead (CHead (CHead (CSort O) 
(Bind Abst) (TSort O)) (Bind Abst) (TSort O)) (Bind Abst) (TLRef O)) (TLRef 
(S (S O))) t)))) (\lambda (t2: T).(\lambda (_: T).(\lambda (_: T).(ty3 g 
(CHead (CHead (CHead (CHead (CSort O) (Bind Abst) (TSort O)) (Bind Abst) 
(TSort O)) (Bind Abst) (TLRef O)) (Bind Abst) (TLRef (S (S O)))) (TSort O) 
t2)))) (\lambda (t2: T).(\lambda (_: T).(\lambda (t0: T).(ty3 g (CHead (CHead 
(CHead (CHead (CSort O) (Bind Abst) (TSort O)) (Bind Abst) (TSort O)) (Bind 
Abst) (TLRef O)) (Bind Abst) (TLRef (S (S O)))) t2 t0)))) P (\lambda (x5: 
T).(\lambda (x6: T).(\lambda (x7: T).(\lambda (_: (pc3 (CHead (CHead (CHead 
(CSort O) (Bind Abst) (TSort O)) (Bind Abst) (TSort O)) (Bind Abst) (TLRef 
O)) (THead (Bind Abst) (TLRef (S (S O))) x5) (THead (Bind Abst) x0 
x1))).(\lambda (H8: (ty3 g (CHead (CHead (CHead (CSort O) (Bind Abst) (TSort 
O)) (Bind Abst) (TSort O)) (Bind Abst) (TLRef O)) (TLRef (S (S O))) 
x6)).(\lambda (_: (ty3 g (CHead (CHead (CHead (CHead (CSort O) (Bind Abst) 
(TSort O)) (Bind Abst) (TSort O)) (Bind Abst) (TLRef O)) (Bind Abst) (TLRef 
(S (S O)))) (TSort O) x5)).(\lambda (_: (ty3 g (CHead (CHead (CHead (CHead 
(CSort O) (Bind Abst) (TSort O)) (Bind Abst) (TSort O)) (Bind Abst) (TLRef 
O)) (Bind Abst) (TLRef (S (S O)))) x5 x7)).(or_ind (ex3_3 C T T (\lambda (_: 
C).(\lambda (_: T).(\lambda (t: T).(pc3 (CHead (CHead (CHead (CSort O) (Bind 
Abst) (TSort O)) (Bind Abst) (TSort O)) (Bind Abst) (TLRef O)) (lift (S (S (S 
O))) O t) x6)))) (\lambda (e: C).(\lambda (u0: T).(\lambda (_: T).(getl (S (S 
O)) (CHead (CHead (CHead (CSort O) (Bind Abst) (TSort O)) (Bind Abst) (TSort 
O)) (Bind Abst) (TLRef O)) (CHead e (Bind Abbr) u0))))) (\lambda (e: 
C).(\lambda (u0: T).(\lambda (t: T).(ty3 g e u0 t))))) (ex3_3 C T T (\lambda 
(_: C).(\lambda (u0: T).(\lambda (_: T).(pc3 (CHead (CHead (CHead (CSort O) 
(Bind Abst) (TSort O)) (Bind Abst) (TSort O)) (Bind Abst) (TLRef O)) (lift (S 
(S (S O))) O u0) x6)))) (\lambda (e: C).(\lambda (u0: T).(\lambda (_: 
T).(getl (S (S O)) (CHead (CHead (CHead (CSort O) (Bind Abst) (TSort O)) 
(Bind Abst) (TSort O)) (Bind Abst) (TLRef O)) (CHead e (Bind Abst) u0))))) 
(\lambda (e: C).(\lambda (u0: T).(\lambda (t: T).(ty3 g e u0 t))))) P 
(\lambda (H11: (ex3_3 C T T (\lambda (_: C).(\lambda (_: T).(\lambda (t: 
T).(pc3 (CHead (CHead (CHead (CSort O) (Bind Abst) (TSort O)) (Bind Abst) 
(TSort O)) (Bind Abst) (TLRef O)) (lift (S (S (S O))) O t) x6)))) (\lambda 
(e: C).(\lambda (u0: T).(\lambda (_: T).(getl (S (S O)) (CHead (CHead (CHead 
(CSort O) (Bind Abst) (TSort O)) (Bind Abst) (TSort O)) (Bind Abst) (TLRef 
O)) (CHead e (Bind Abbr) u0))))) (\lambda (e: C).(\lambda (u0: T).(\lambda 
(t: T).(ty3 g e u0 t)))))).(ex3_3_ind C T T (\lambda (_: C).(\lambda (_: 
T).(\lambda (t: T).(pc3 (CHead (CHead (CHead (CSort O) (Bind Abst) (TSort O)) 
(Bind Abst) (TSort O)) (Bind Abst) (TLRef O)) (lift (S (S (S O))) O t) x6)))) 
(\lambda (e: C).(\lambda (u0: T).(\lambda (_: T).(getl (S (S O)) (CHead 
(CHead (CHead (CSort O) (Bind Abst) (TSort O)) (Bind Abst) (TSort O)) (Bind 
Abst) (TLRef O)) (CHead e (Bind Abbr) u0))))) (\lambda (e: C).(\lambda (u0: 
T).(\lambda (t: T).(ty3 g e u0 t)))) P (\lambda (x8: C).(\lambda (x9: 
T).(\lambda (x10: T).(\lambda (_: (pc3 (CHead (CHead (CHead (CSort O) (Bind 
Abst) (TSort O)) (Bind Abst) (TSort O)) (Bind Abst) (TLRef O)) (lift (S (S (S 
O))) O x10) x6)).(\lambda (H13: (getl (S (S O)) (CHead (CHead (CHead (CSort 
O) (Bind Abst) (TSort O)) (Bind Abst) (TSort O)) (Bind Abst) (TLRef O)) 
(CHead x8 (Bind Abbr) x9))).(\lambda (_: (ty3 g x8 x9 x10)).(let H15 \def 
(getl_gen_all (CHead (CHead (CSort O) (Bind Abst) (TSort O)) (Bind Abst) 
(TSort O)) (CHead x8 (Bind Abbr) x9) (r (Bind Abst) (S O)) (getl_gen_S (Bind 
Abst) (CHead (CHead (CSort O) (Bind Abst) (TSort O)) (Bind Abst) (TSort O)) 
(CHead x8 (Bind Abbr) x9) (TLRef O) (S O) H13)) in (ex2_ind C (\lambda (e: 
C).(drop (S O) O (CHead (CHead (CSort O) (Bind Abst) (TSort O)) (Bind Abst) 
(TSort O)) e)) (\lambda (e: C).(clear e (CHead x8 (Bind Abbr) x9))) P 
(\lambda (x: C).(\lambda (_: (drop (S O) O (CHead (CHead (CSort O) (Bind 
Abst) (TSort O)) (Bind Abst) (TSort O)) x)).(\lambda (_: (clear x (CHead x8 
(Bind Abbr) x9))).(let H18 \def (eq_ind C (CHead x2 (Bind Abbr) x3) (\lambda 
(ee: C).(match ee in C return (\lambda (_: C).Prop) with [(CSort _) 
\Rightarrow False | (CHead _ k _) \Rightarrow (match k in K return (\lambda 
(_: K).Prop) with [(Bind b) \Rightarrow (match b in B return (\lambda (_: 
B).Prop) with [Abbr \Rightarrow True | Abst \Rightarrow False | Void 
\Rightarrow False]) | (Flat _) \Rightarrow False])])) I (CHead (CHead (CHead 
(CSort O) (Bind Abst) (TSort O)) (Bind Abst) (TSort O)) (Bind Abst) (TLRef 
O)) (clear_gen_bind Abst (CHead (CHead (CSort O) (Bind Abst) (TSort O)) (Bind 
Abst) (TSort O)) (CHead x2 (Bind Abbr) x3) (TLRef O) (getl_gen_O (CHead 
(CHead (CHead (CSort O) (Bind Abst) (TSort O)) (Bind Abst) (TSort O)) (Bind 
Abst) (TLRef O)) (CHead x2 (Bind Abbr) x3) H5))) in (False_ind P H18))))) 
H15)))))))) H11)) (\lambda (H11: (ex3_3 C T T (\lambda (_: C).(\lambda (u0: 
T).(\lambda (_: T).(pc3 (CHead (CHead (CHead (CSort O) (Bind Abst) (TSort O)) 
(Bind Abst) (TSort O)) (Bind Abst) (TLRef O)) (lift (S (S (S O))) O u0) 
x6)))) (\lambda (e: C).(\lambda (u0: T).(\lambda (_: T).(getl (S (S O)) 
(CHead (CHead (CHead (CSort O) (Bind Abst) (TSort O)) (Bind Abst) (TSort O)) 
(Bind Abst) (TLRef O)) (CHead e (Bind Abst) u0))))) (\lambda (e: C).(\lambda 
(u0: T).(\lambda (t: T).(ty3 g e u0 t)))))).(ex3_3_ind C T T (\lambda (_: 
C).(\lambda (u0: T).(\lambda (_: T).(pc3 (CHead (CHead (CHead (CSort O) (Bind 
Abst) (TSort O)) (Bind Abst) (TSort O)) (Bind Abst) (TLRef O)) (lift (S (S (S 
O))) O u0) x6)))) (\lambda (e: C).(\lambda (u0: T).(\lambda (_: T).(getl (S 
(S O)) (CHead (CHead (CHead (CSort O) (Bind Abst) (TSort O)) (Bind Abst) 
(TSort O)) (Bind Abst) (TLRef O)) (CHead e (Bind Abst) u0))))) (\lambda (e: 
C).(\lambda (u0: T).(\lambda (t: T).(ty3 g e u0 t)))) P (\lambda (x8: 
C).(\lambda (x9: T).(\lambda (x10: T).(\lambda (_: (pc3 (CHead (CHead (CHead 
(CSort O) (Bind Abst) (TSort O)) (Bind Abst) (TSort O)) (Bind Abst) (TLRef 
O)) (lift (S (S (S O))) O x9) x6)).(\lambda (H13: (getl (S (S O)) (CHead 
(CHead (CHead (CSort O) (Bind Abst) (TSort O)) (Bind Abst) (TSort O)) (Bind 
Abst) (TLRef O)) (CHead x8 (Bind Abst) x9))).(\lambda (_: (ty3 g x8 x9 
x10)).(let H15 \def (getl_gen_all (CHead (CHead (CSort O) (Bind Abst) (TSort 
O)) (Bind Abst) (TSort O)) (CHead x8 (Bind Abst) x9) (r (Bind Abst) (S O)) 
(getl_gen_S (Bind Abst) (CHead (CHead (CSort O) (Bind Abst) (TSort O)) (Bind 
Abst) (TSort O)) (CHead x8 (Bind Abst) x9) (TLRef O) (S O) H13)) in (ex2_ind 
C (\lambda (e: C).(drop (S O) O (CHead (CHead (CSort O) (Bind Abst) (TSort 
O)) (Bind Abst) (TSort O)) e)) (\lambda (e: C).(clear e (CHead x8 (Bind Abst) 
x9))) P (\lambda (x: C).(\lambda (_: (drop (S O) O (CHead (CHead (CSort O) 
(Bind Abst) (TSort O)) (Bind Abst) (TSort O)) x)).(\lambda (_: (clear x 
(CHead x8 (Bind Abst) x9))).(let H18 \def (eq_ind C (CHead x2 (Bind Abbr) x3) 
(\lambda (ee: C).(match ee in C return (\lambda (_: C).Prop) with [(CSort _) 
\Rightarrow False | (CHead _ k _) \Rightarrow (match k in K return (\lambda 
(_: K).Prop) with [(Bind b) \Rightarrow (match b in B return (\lambda (_: 
B).Prop) with [Abbr \Rightarrow True | Abst \Rightarrow False | Void 
\Rightarrow False]) | (Flat _) \Rightarrow False])])) I (CHead (CHead (CHead 
(CSort O) (Bind Abst) (TSort O)) (Bind Abst) (TSort O)) (Bind Abst) (TLRef 
O)) (clear_gen_bind Abst (CHead (CHead (CSort O) (Bind Abst) (TSort O)) (Bind 
Abst) (TSort O)) (CHead x2 (Bind Abbr) x3) (TLRef O) (getl_gen_O (CHead 
(CHead (CHead (CSort O) (Bind Abst) (TSort O)) (Bind Abst) (TSort O)) (Bind 
Abst) (TLRef O)) (CHead x2 (Bind Abbr) x3) H5))) in (False_ind P H18))))) 
H15)))))))) H11)) (ty3_gen_lref g (CHead (CHead (CHead (CSort O) (Bind Abst) 
(TSort O)) (Bind Abst) (TSort O)) (Bind Abst) (TLRef O)) x6 (S (S O)) 
H8))))))))) (ty3_gen_bind g Abst (CHead (CHead (CHead (CSort O) (Bind Abst) 
(TSort O)) (Bind Abst) (TSort O)) (Bind Abst) (TLRef O)) (TLRef (S (S O))) 
(TSort O) (THead (Bind Abst) x0 x1) H1)))))))) H3)) (\lambda (H3: (ex3_3 C T 
T (\lambda (_: C).(\lambda (u0: T).(\lambda (_: T).(pc3 (CHead (CHead (CHead 
(CSort O) (Bind Abst) (TSort O)) (Bind Abst) (TSort O)) (Bind Abst) (TLRef 
O)) (lift (S O) O u0) x0)))) (\lambda (e: C).(\lambda (u0: T).(\lambda (_: 
T).(getl O (CHead (CHead (CHead (CSort O) (Bind Abst) (TSort O)) (Bind Abst) 
(TSort O)) (Bind Abst) (TLRef O)) (CHead e (Bind Abst) u0))))) (\lambda (e: 
C).(\lambda (u0: T).(\lambda (t: T).(ty3 g e u0 t)))))).(ex3_3_ind C T T 
(\lambda (_: C).(\lambda (u0: T).(\lambda (_: T).(pc3 (CHead (CHead (CHead 
(CSort O) (Bind Abst) (TSort O)) (Bind Abst) (TSort O)) (Bind Abst) (TLRef 
O)) (lift (S O) O u0) x0)))) (\lambda (e: C).(\lambda (u0: T).(\lambda (_: 
T).(getl O (CHead (CHead (CHead (CSort O) (Bind Abst) (TSort O)) (Bind Abst) 
(TSort O)) (Bind Abst) (TLRef O)) (CHead e (Bind Abst) u0))))) (\lambda (e: 
C).(\lambda (u0: T).(\lambda (t: T).(ty3 g e u0 t)))) P (\lambda (x2: 
C).(\lambda (x3: T).(\lambda (x4: T).(\lambda (H4: (pc3 (CHead (CHead (CHead 
(CSort O) (Bind Abst) (TSort O)) (Bind Abst) (TSort O)) (Bind Abst) (TLRef 
O)) (lift (S O) O x3) x0)).(\lambda (H5: (getl O (CHead (CHead (CHead (CSort 
O) (Bind Abst) (TSort O)) (Bind Abst) (TSort O)) (Bind Abst) (TLRef O)) 
(CHead x2 (Bind Abst) x3))).(\lambda (H6: (ty3 g x2 x3 x4)).(ex4_3_ind T T T 
(\lambda (t2: T).(\lambda (_: T).(\lambda (_: T).(pc3 (CHead (CHead (CHead 
(CSort O) (Bind Abst) (TSort O)) (Bind Abst) (TSort O)) (Bind Abst) (TLRef 
O)) (THead (Bind Abst) (TLRef (S (S O))) t2) (THead (Bind Abst) x0 x1))))) 
(\lambda (_: T).(\lambda (t: T).(\lambda (_: T).(ty3 g (CHead (CHead (CHead 
(CSort O) (Bind Abst) (TSort O)) (Bind Abst) (TSort O)) (Bind Abst) (TLRef 
O)) (TLRef (S (S O))) t)))) (\lambda (t2: T).(\lambda (_: T).(\lambda (_: 
T).(ty3 g (CHead (CHead (CHead (CHead (CSort O) (Bind Abst) (TSort O)) (Bind 
Abst) (TSort O)) (Bind Abst) (TLRef O)) (Bind Abst) (TLRef (S (S O)))) (TSort 
O) t2)))) (\lambda (t2: T).(\lambda (_: T).(\lambda (t0: T).(ty3 g (CHead 
(CHead (CHead (CHead (CSort O) (Bind Abst) (TSort O)) (Bind Abst) (TSort O)) 
(Bind Abst) (TLRef O)) (Bind Abst) (TLRef (S (S O)))) t2 t0)))) P (\lambda 
(x5: T).(\lambda (x6: T).(\lambda (x7: T).(\lambda (H7: (pc3 (CHead (CHead 
(CHead (CSort O) (Bind Abst) (TSort O)) (Bind Abst) (TSort O)) (Bind Abst) 
(TLRef O)) (THead (Bind Abst) (TLRef (S (S O))) x5) (THead (Bind Abst) x0 
x1))).(\lambda (H8: (ty3 g (CHead (CHead (CHead (CSort O) (Bind Abst) (TSort 
O)) (Bind Abst) (TSort O)) (Bind Abst) (TLRef O)) (TLRef (S (S O))) 
x6)).(\lambda (_: (ty3 g (CHead (CHead (CHead (CHead (CSort O) (Bind Abst) 
(TSort O)) (Bind Abst) (TSort O)) (Bind Abst) (TLRef O)) (Bind Abst) (TLRef 
(S (S O)))) (TSort O) x5)).(\lambda (_: (ty3 g (CHead (CHead (CHead (CHead 
(CSort O) (Bind Abst) (TSort O)) (Bind Abst) (TSort O)) (Bind Abst) (TLRef 
O)) (Bind Abst) (TLRef (S (S O)))) x5 x7)).(or_ind (ex3_3 C T T (\lambda (_: 
C).(\lambda (_: T).(\lambda (t: T).(pc3 (CHead (CHead (CHead (CSort O) (Bind 
Abst) (TSort O)) (Bind Abst) (TSort O)) (Bind Abst) (TLRef O)) (lift (S (S (S 
O))) O t) x6)))) (\lambda (e: C).(\lambda (u0: T).(\lambda (_: T).(getl (S (S 
O)) (CHead (CHead (CHead (CSort O) (Bind Abst) (TSort O)) (Bind Abst) (TSort 
O)) (Bind Abst) (TLRef O)) (CHead e (Bind Abbr) u0))))) (\lambda (e: 
C).(\lambda (u0: T).(\lambda (t: T).(ty3 g e u0 t))))) (ex3_3 C T T (\lambda 
(_: C).(\lambda (u0: T).(\lambda (_: T).(pc3 (CHead (CHead (CHead (CSort O) 
(Bind Abst) (TSort O)) (Bind Abst) (TSort O)) (Bind Abst) (TLRef O)) (lift (S 
(S (S O))) O u0) x6)))) (\lambda (e: C).(\lambda (u0: T).(\lambda (_: 
T).(getl (S (S O)) (CHead (CHead (CHead (CSort O) (Bind Abst) (TSort O)) 
(Bind Abst) (TSort O)) (Bind Abst) (TLRef O)) (CHead e (Bind Abst) u0))))) 
(\lambda (e: C).(\lambda (u0: T).(\lambda (t: T).(ty3 g e u0 t))))) P 
(\lambda (H11: (ex3_3 C T T (\lambda (_: C).(\lambda (_: T).(\lambda (t: 
T).(pc3 (CHead (CHead (CHead (CSort O) (Bind Abst) (TSort O)) (Bind Abst) 
(TSort O)) (Bind Abst) (TLRef O)) (lift (S (S (S O))) O t) x6)))) (\lambda 
(e: C).(\lambda (u0: T).(\lambda (_: T).(getl (S (S O)) (CHead (CHead (CHead 
(CSort O) (Bind Abst) (TSort O)) (Bind Abst) (TSort O)) (Bind Abst) (TLRef 
O)) (CHead e (Bind Abbr) u0))))) (\lambda (e: C).(\lambda (u0: T).(\lambda 
(t: T).(ty3 g e u0 t)))))).(ex3_3_ind C T T (\lambda (_: C).(\lambda (_: 
T).(\lambda (t: T).(pc3 (CHead (CHead (CHead (CSort O) (Bind Abst) (TSort O)) 
(Bind Abst) (TSort O)) (Bind Abst) (TLRef O)) (lift (S (S (S O))) O t) x6)))) 
(\lambda (e: C).(\lambda (u0: T).(\lambda (_: T).(getl (S (S O)) (CHead 
(CHead (CHead (CSort O) (Bind Abst) (TSort O)) (Bind Abst) (TSort O)) (Bind 
Abst) (TLRef O)) (CHead e (Bind Abbr) u0))))) (\lambda (e: C).(\lambda (u0: 
T).(\lambda (t: T).(ty3 g e u0 t)))) P (\lambda (x8: C).(\lambda (x9: 
T).(\lambda (x10: T).(\lambda (_: (pc3 (CHead (CHead (CHead (CSort O) (Bind 
Abst) (TSort O)) (Bind Abst) (TSort O)) (Bind Abst) (TLRef O)) (lift (S (S (S 
O))) O x10) x6)).(\lambda (H13: (getl (S (S O)) (CHead (CHead (CHead (CSort 
O) (Bind Abst) (TSort O)) (Bind Abst) (TSort O)) (Bind Abst) (TLRef O)) 
(CHead x8 (Bind Abbr) x9))).(\lambda (_: (ty3 g x8 x9 x10)).(let H15 \def 
(getl_gen_all (CHead (CHead (CSort O) (Bind Abst) (TSort O)) (Bind Abst) 
(TSort O)) (CHead x8 (Bind Abbr) x9) (r (Bind Abst) (S O)) (getl_gen_S (Bind 
Abst) (CHead (CHead (CSort O) (Bind Abst) (TSort O)) (Bind Abst) (TSort O)) 
(CHead x8 (Bind Abbr) x9) (TLRef O) (S O) H13)) in (ex2_ind C (\lambda (e: 
C).(drop (S O) O (CHead (CHead (CSort O) (Bind Abst) (TSort O)) (Bind Abst) 
(TSort O)) e)) (\lambda (e: C).(clear e (CHead x8 (Bind Abbr) x9))) P 
(\lambda (x: C).(\lambda (H16: (drop (S O) O (CHead (CHead (CSort O) (Bind 
Abst) (TSort O)) (Bind Abst) (TSort O)) x)).(\lambda (H17: (clear x (CHead x8 
(Bind Abbr) x9))).(let H18 \def (f_equal C C (\lambda (e: C).(match e in C 
return (\lambda (_: C).C) with [(CSort _) \Rightarrow x2 | (CHead c _ _) 
\Rightarrow c])) (CHead x2 (Bind Abst) x3) (CHead (CHead (CHead (CSort O) 
(Bind Abst) (TSort O)) (Bind Abst) (TSort O)) (Bind Abst) (TLRef O)) 
(clear_gen_bind Abst (CHead (CHead (CSort O) (Bind Abst) (TSort O)) (Bind 
Abst) (TSort O)) (CHead x2 (Bind Abst) x3) (TLRef O) (getl_gen_O (CHead 
(CHead (CHead (CSort O) (Bind Abst) (TSort O)) (Bind Abst) (TSort O)) (Bind 
Abst) (TLRef O)) (CHead x2 (Bind Abst) x3) H5))) in ((let H19 \def (f_equal C 
T (\lambda (e: C).(match e in C return (\lambda (_: C).T) with [(CSort _) 
\Rightarrow x3 | (CHead _ _ t) \Rightarrow t])) (CHead x2 (Bind Abst) x3) 
(CHead (CHead (CHead (CSort O) (Bind Abst) (TSort O)) (Bind Abst) (TSort O)) 
(Bind Abst) (TLRef O)) (clear_gen_bind Abst (CHead (CHead (CSort O) (Bind 
Abst) (TSort O)) (Bind Abst) (TSort O)) (CHead x2 (Bind Abst) x3) (TLRef O) 
(getl_gen_O (CHead (CHead (CHead (CSort O) (Bind Abst) (TSort O)) (Bind Abst) 
(TSort O)) (Bind Abst) (TLRef O)) (CHead x2 (Bind Abst) x3) H5))) in (\lambda 
(H20: (eq C x2 (CHead (CHead (CSort O) (Bind Abst) (TSort O)) (Bind Abst) 
(TSort O)))).(let H21 \def (eq_ind T x3 (\lambda (t: T).(ty3 g x2 t x4)) H6 
(TLRef O) H19) in (let H22 \def (eq_ind T x3 (\lambda (t: T).(pc3 (CHead 
(CHead (CHead (CSort O) (Bind Abst) (TSort O)) (Bind Abst) (TSort O)) (Bind 
Abst) (TLRef O)) (lift (S O) O t) x0)) H4 (TLRef O) H19) in (let H23 \def 
(eq_ind C x2 (\lambda (c: C).(ty3 g c (TLRef O) x4)) H21 (CHead (CHead (CSort 
O) (Bind Abst) (TSort O)) (Bind Abst) (TSort O)) H20) in (let H24 \def 
(eq_ind_r C x (\lambda (c: C).(clear c (CHead x8 (Bind Abbr) x9))) H17 (CHead 
(CSort O) (Bind Abst) (TSort O)) (drop_gen_refl (CHead (CSort O) (Bind Abst) 
(TSort O)) x (drop_gen_drop (Bind Abst) (CHead (CSort O) (Bind Abst) (TSort 
O)) x (TSort O) O H16))) in (let H25 \def (eq_ind C (CHead x8 (Bind Abbr) x9) 
(\lambda (ee: C).(match ee in C return (\lambda (_: C).Prop) with [(CSort _) 
\Rightarrow False | (CHead _ k _) \Rightarrow (match k in K return (\lambda 
(_: K).Prop) with [(Bind b) \Rightarrow (match b in B return (\lambda (_: 
B).Prop) with [Abbr \Rightarrow True | Abst \Rightarrow False | Void 
\Rightarrow False]) | (Flat _) \Rightarrow False])])) I (CHead (CSort O) 
(Bind Abst) (TSort O)) (clear_gen_bind Abst (CSort O) (CHead x8 (Bind Abbr) 
x9) (TSort O) H24)) in (False_ind P H25)))))))) H18))))) H15)))))))) H11)) 
(\lambda (H11: (ex3_3 C T T (\lambda (_: C).(\lambda (u0: T).(\lambda (_: 
T).(pc3 (CHead (CHead (CHead (CSort O) (Bind Abst) (TSort O)) (Bind Abst) 
(TSort O)) (Bind Abst) (TLRef O)) (lift (S (S (S O))) O u0) x6)))) (\lambda 
(e: C).(\lambda (u0: T).(\lambda (_: T).(getl (S (S O)) (CHead (CHead (CHead 
(CSort O) (Bind Abst) (TSort O)) (Bind Abst) (TSort O)) (Bind Abst) (TLRef 
O)) (CHead e (Bind Abst) u0))))) (\lambda (e: C).(\lambda (u0: T).(\lambda 
(t: T).(ty3 g e u0 t)))))).(ex3_3_ind C T T (\lambda (_: C).(\lambda (u0: 
T).(\lambda (_: T).(pc3 (CHead (CHead (CHead (CSort O) (Bind Abst) (TSort O)) 
(Bind Abst) (TSort O)) (Bind Abst) (TLRef O)) (lift (S (S (S O))) O u0) 
x6)))) (\lambda (e: C).(\lambda (u0: T).(\lambda (_: T).(getl (S (S O)) 
(CHead (CHead (CHead (CSort O) (Bind Abst) (TSort O)) (Bind Abst) (TSort O)) 
(Bind Abst) (TLRef O)) (CHead e (Bind Abst) u0))))) (\lambda (e: C).(\lambda 
(u0: T).(\lambda (t: T).(ty3 g e u0 t)))) P (\lambda (x8: C).(\lambda (x9: 
T).(\lambda (x10: T).(\lambda (H12: (pc3 (CHead (CHead (CHead (CSort O) (Bind 
Abst) (TSort O)) (Bind Abst) (TSort O)) (Bind Abst) (TLRef O)) (lift (S (S (S 
O))) O x9) x6)).(\lambda (H13: (getl (S (S O)) (CHead (CHead (CHead (CSort O) 
(Bind Abst) (TSort O)) (Bind Abst) (TSort O)) (Bind Abst) (TLRef O)) (CHead 
x8 (Bind Abst) x9))).(\lambda (H14: (ty3 g x8 x9 x10)).(let H15 \def 
(getl_gen_all (CHead (CHead (CSort O) (Bind Abst) (TSort O)) (Bind Abst) 
(TSort O)) (CHead x8 (Bind Abst) x9) (r (Bind Abst) (S O)) (getl_gen_S (Bind 
Abst) (CHead (CHead (CSort O) (Bind Abst) (TSort O)) (Bind Abst) (TSort O)) 
(CHead x8 (Bind Abst) x9) (TLRef O) (S O) H13)) in (ex2_ind C (\lambda (e: 
C).(drop (S O) O (CHead (CHead (CSort O) (Bind Abst) (TSort O)) (Bind Abst) 
(TSort O)) e)) (\lambda (e: C).(clear e (CHead x8 (Bind Abst) x9))) P 
(\lambda (x: C).(\lambda (H16: (drop (S O) O (CHead (CHead (CSort O) (Bind 
Abst) (TSort O)) (Bind Abst) (TSort O)) x)).(\lambda (H17: (clear x (CHead x8 
(Bind Abst) x9))).(let H18 \def (f_equal C C (\lambda (e: C).(match e in C 
return (\lambda (_: C).C) with [(CSort _) \Rightarrow x2 | (CHead c _ _) 
\Rightarrow c])) (CHead x2 (Bind Abst) x3) (CHead (CHead (CHead (CSort O) 
(Bind Abst) (TSort O)) (Bind Abst) (TSort O)) (Bind Abst) (TLRef O)) 
(clear_gen_bind Abst (CHead (CHead (CSort O) (Bind Abst) (TSort O)) (Bind 
Abst) (TSort O)) (CHead x2 (Bind Abst) x3) (TLRef O) (getl_gen_O (CHead 
(CHead (CHead (CSort O) (Bind Abst) (TSort O)) (Bind Abst) (TSort O)) (Bind 
Abst) (TLRef O)) (CHead x2 (Bind Abst) x3) H5))) in ((let H19 \def (f_equal C 
T (\lambda (e: C).(match e in C return (\lambda (_: C).T) with [(CSort _) 
\Rightarrow x3 | (CHead _ _ t) \Rightarrow t])) (CHead x2 (Bind Abst) x3) 
(CHead (CHead (CHead (CSort O) (Bind Abst) (TSort O)) (Bind Abst) (TSort O)) 
(Bind Abst) (TLRef O)) (clear_gen_bind Abst (CHead (CHead (CSort O) (Bind 
Abst) (TSort O)) (Bind Abst) (TSort O)) (CHead x2 (Bind Abst) x3) (TLRef O) 
(getl_gen_O (CHead (CHead (CHead (CSort O) (Bind Abst) (TSort O)) (Bind Abst) 
(TSort O)) (Bind Abst) (TLRef O)) (CHead x2 (Bind Abst) x3) H5))) in (\lambda 
(H20: (eq C x2 (CHead (CHead (CSort O) (Bind Abst) (TSort O)) (Bind Abst) 
(TSort O)))).(let H21 \def (eq_ind T x3 (\lambda (t: T).(ty3 g x2 t x4)) H6 
(TLRef O) H19) in (let H22 \def (eq_ind T x3 (\lambda (t: T).(pc3 (CHead 
(CHead (CHead (CSort O) (Bind Abst) (TSort O)) (Bind Abst) (TSort O)) (Bind 
Abst) (TLRef O)) (lift (S O) O t) x0)) H4 (TLRef O) H19) in (let H23 \def 
(eq_ind C x2 (\lambda (c: C).(ty3 g c (TLRef O) x4)) H21 (CHead (CHead (CSort 
O) (Bind Abst) (TSort O)) (Bind Abst) (TSort O)) H20) in (let H24 \def 
(eq_ind_r C x (\lambda (c: C).(clear c (CHead x8 (Bind Abst) x9))) H17 (CHead 
(CSort O) (Bind Abst) (TSort O)) (drop_gen_refl (CHead (CSort O) (Bind Abst) 
(TSort O)) x (drop_gen_drop (Bind Abst) (CHead (CSort O) (Bind Abst) (TSort 
O)) x (TSort O) O H16))) in (let H25 \def (f_equal C C (\lambda (e: C).(match 
e in C return (\lambda (_: C).C) with [(CSort _) \Rightarrow x8 | (CHead c _ 
_) \Rightarrow c])) (CHead x8 (Bind Abst) x9) (CHead (CSort O) (Bind Abst) 
(TSort O)) (clear_gen_bind Abst (CSort O) (CHead x8 (Bind Abst) x9) (TSort O) 
H24)) in ((let H26 \def (f_equal C T (\lambda (e: C).(match e in C return 
(\lambda (_: C).T) with [(CSort _) \Rightarrow x9 | (CHead _ _ t) \Rightarrow 
t])) (CHead x8 (Bind Abst) x9) (CHead (CSort O) (Bind Abst) (TSort O)) 
(clear_gen_bind Abst (CSort O) (CHead x8 (Bind Abst) x9) (TSort O) H24)) in 
(\lambda (H27: (eq C x8 (CSort O))).(let H28 \def (eq_ind T x9 (\lambda (t: 
T).(ty3 g x8 t x10)) H14 (TSort O) H26) in (let H29 \def (eq_ind T x9 
(\lambda (t: T).(pc3 (CHead (CHead (CHead (CSort O) (Bind Abst) (TSort O)) 
(Bind Abst) (TSort O)) (Bind Abst) (TLRef O)) (lift (S (S (S O))) O t) x6)) 
H12 (TSort O) H26) in (let H30 \def (eq_ind C x8 (\lambda (c: C).(ty3 g c 
(TSort O) x10)) H28 (CSort O) H27) in (or_ind (ex3_3 C T T (\lambda (_: 
C).(\lambda (_: T).(\lambda (t: T).(pc3 (CHead (CHead (CSort O) (Bind Abst) 
(TSort O)) (Bind Abst) (TSort O)) (lift (S O) O t) x4)))) (\lambda (e: 
C).(\lambda (u0: T).(\lambda (_: T).(getl O (CHead (CHead (CSort O) (Bind 
Abst) (TSort O)) (Bind Abst) (TSort O)) (CHead e (Bind Abbr) u0))))) (\lambda 
(e: C).(\lambda (u0: T).(\lambda (t: T).(ty3 g e u0 t))))) (ex3_3 C T T 
(\lambda (_: C).(\lambda (u0: T).(\lambda (_: T).(pc3 (CHead (CHead (CSort O) 
(Bind Abst) (TSort O)) (Bind Abst) (TSort O)) (lift (S O) O u0) x4)))) 
(\lambda (e: C).(\lambda (u0: T).(\lambda (_: T).(getl O (CHead (CHead (CSort 
O) (Bind Abst) (TSort O)) (Bind Abst) (TSort O)) (CHead e (Bind Abst) u0))))) 
(\lambda (e: C).(\lambda (u0: T).(\lambda (t: T).(ty3 g e u0 t))))) P 
(\lambda (H31: (ex3_3 C T T (\lambda (_: C).(\lambda (_: T).(\lambda (t: 
T).(pc3 (CHead (CHead (CSort O) (Bind Abst) (TSort O)) (Bind Abst) (TSort O)) 
(lift (S O) O t) x4)))) (\lambda (e: C).(\lambda (u0: T).(\lambda (_: 
T).(getl O (CHead (CHead (CSort O) (Bind Abst) (TSort O)) (Bind Abst) (TSort 
O)) (CHead e (Bind Abbr) u0))))) (\lambda (e: C).(\lambda (u0: T).(\lambda 
(t: T).(ty3 g e u0 t)))))).(ex3_3_ind C T T (\lambda (_: C).(\lambda (_: 
T).(\lambda (t: T).(pc3 (CHead (CHead (CSort O) (Bind Abst) (TSort O)) (Bind 
Abst) (TSort O)) (lift (S O) O t) x4)))) (\lambda (e: C).(\lambda (u0: 
T).(\lambda (_: T).(getl O (CHead (CHead (CSort O) (Bind Abst) (TSort O)) 
(Bind Abst) (TSort O)) (CHead e (Bind Abbr) u0))))) (\lambda (e: C).(\lambda 
(u0: T).(\lambda (t: T).(ty3 g e u0 t)))) P (\lambda (x11: C).(\lambda (x12: 
T).(\lambda (x13: T).(\lambda (_: (pc3 (CHead (CHead (CSort O) (Bind Abst) 
(TSort O)) (Bind Abst) (TSort O)) (lift (S O) O x13) x4)).(\lambda (H33: 
(getl O (CHead (CHead (CSort O) (Bind Abst) (TSort O)) (Bind Abst) (TSort O)) 
(CHead x11 (Bind Abbr) x12))).(\lambda (_: (ty3 g x11 x12 x13)).(let H35 \def 
(eq_ind C (CHead x11 (Bind Abbr) x12) (\lambda (ee: C).(match ee in C return 
(\lambda (_: C).Prop) with [(CSort _) \Rightarrow False | (CHead _ k _) 
\Rightarrow (match k in K return (\lambda (_: K).Prop) with [(Bind b) 
\Rightarrow (match b in B return (\lambda (_: B).Prop) with [Abbr \Rightarrow 
True | Abst \Rightarrow False | Void \Rightarrow False]) | (Flat _) 
\Rightarrow False])])) I (CHead (CHead (CSort O) (Bind Abst) (TSort O)) (Bind 
Abst) (TSort O)) (clear_gen_bind Abst (CHead (CSort O) (Bind Abst) (TSort O)) 
(CHead x11 (Bind Abbr) x12) (TSort O) (getl_gen_O (CHead (CHead (CSort O) 
(Bind Abst) (TSort O)) (Bind Abst) (TSort O)) (CHead x11 (Bind Abbr) x12) 
H33))) in (False_ind P H35)))))))) H31)) (\lambda (H31: (ex3_3 C T T (\lambda 
(_: C).(\lambda (u0: T).(\lambda (_: T).(pc3 (CHead (CHead (CSort O) (Bind 
Abst) (TSort O)) (Bind Abst) (TSort O)) (lift (S O) O u0) x4)))) (\lambda (e: 
C).(\lambda (u0: T).(\lambda (_: T).(getl O (CHead (CHead (CSort O) (Bind 
Abst) (TSort O)) (Bind Abst) (TSort O)) (CHead e (Bind Abst) u0))))) (\lambda 
(e: C).(\lambda (u0: T).(\lambda (t: T).(ty3 g e u0 t)))))).(ex3_3_ind C T T 
(\lambda (_: C).(\lambda (u0: T).(\lambda (_: T).(pc3 (CHead (CHead (CSort O) 
(Bind Abst) (TSort O)) (Bind Abst) (TSort O)) (lift (S O) O u0) x4)))) 
(\lambda (e: C).(\lambda (u0: T).(\lambda (_: T).(getl O (CHead (CHead (CSort 
O) (Bind Abst) (TSort O)) (Bind Abst) (TSort O)) (CHead e (Bind Abst) u0))))) 
(\lambda (e: C).(\lambda (u0: T).(\lambda (t: T).(ty3 g e u0 t)))) P (\lambda 
(x11: C).(\lambda (x12: T).(\lambda (x13: T).(\lambda (H32: (pc3 (CHead 
(CHead (CSort O) (Bind Abst) (TSort O)) (Bind Abst) (TSort O)) (lift (S O) O 
x12) x4)).(\lambda (H33: (getl O (CHead (CHead (CSort O) (Bind Abst) (TSort 
O)) (Bind Abst) (TSort O)) (CHead x11 (Bind Abst) x12))).(\lambda (H34: (ty3 
g x11 x12 x13)).(let H35 \def (f_equal C C (\lambda (e: C).(match e in C 
return (\lambda (_: C).C) with [(CSort _) \Rightarrow x11 | (CHead c _ _) 
\Rightarrow c])) (CHead x11 (Bind Abst) x12) (CHead (CHead (CSort O) (Bind 
Abst) (TSort O)) (Bind Abst) (TSort O)) (clear_gen_bind Abst (CHead (CSort O) 
(Bind Abst) (TSort O)) (CHead x11 (Bind Abst) x12) (TSort O) (getl_gen_O 
(CHead (CHead (CSort O) (Bind Abst) (TSort O)) (Bind Abst) (TSort O)) (CHead 
x11 (Bind Abst) x12) H33))) in ((let H36 \def (f_equal C T (\lambda (e: 
C).(match e in C return (\lambda (_: C).T) with [(CSort _) \Rightarrow x12 | 
(CHead _ _ t) \Rightarrow t])) (CHead x11 (Bind Abst) x12) (CHead (CHead 
(CSort O) (Bind Abst) (TSort O)) (Bind Abst) (TSort O)) (clear_gen_bind Abst 
(CHead (CSort O) (Bind Abst) (TSort O)) (CHead x11 (Bind Abst) x12) (TSort O) 
(getl_gen_O (CHead (CHead (CSort O) (Bind Abst) (TSort O)) (Bind Abst) (TSort 
O)) (CHead x11 (Bind Abst) x12) H33))) in (\lambda (H37: (eq C x11 (CHead 
(CSort O) (Bind Abst) (TSort O)))).(let H38 \def (eq_ind T x12 (\lambda (t: 
T).(ty3 g x11 t x13)) H34 (TSort O) H36) in (let H39 \def (eq_ind T x12 
(\lambda (t: T).(pc3 (CHead (CHead (CSort O) (Bind Abst) (TSort O)) (Bind 
Abst) (TSort O)) (lift (S O) O t) x4)) H32 (TSort O) H36) in (let H40 \def 
(eq_ind C x11 (\lambda (c: C).(ty3 g c (TSort O) x13)) H38 (CHead (CSort O) 
(Bind Abst) (TSort O)) H37) in (and_ind (pc3 (CHead (CHead (CHead (CSort O) 
(Bind Abst) (TSort O)) (Bind Abst) (TSort O)) (Bind Abst) (TLRef O)) (TLRef 
(S (S O))) x0) (\forall (b: B).(\forall (u0: T).(pc3 (CHead (CHead (CHead 
(CHead (CSort O) (Bind Abst) (TSort O)) (Bind Abst) (TSort O)) (Bind Abst) 
(TLRef O)) (Bind b) u0) x5 x1))) P (\lambda (H41: (pc3 (CHead (CHead (CHead 
(CSort O) (Bind Abst) (TSort O)) (Bind Abst) (TSort O)) (Bind Abst) (TLRef 
O)) (TLRef (S (S O))) x0)).(\lambda (_: ((\forall (b: B).(\forall (u0: 
T).(pc3 (CHead (CHead (CHead (CHead (CSort O) (Bind Abst) (TSort O)) (Bind 
Abst) (TSort O)) (Bind Abst) (TLRef O)) (Bind b) u0) x5 x1))))).(let H43 \def 
(eq_ind T (lift (S O) O (TLRef O)) (\lambda (t: T).(pc3 (CHead (CHead (CHead 
(CSort O) (Bind Abst) (TSort O)) (Bind Abst) (TSort O)) (Bind Abst) (TLRef 
O)) (TLRef (S (S O))) t)) (pc3_t x0 (CHead (CHead (CHead (CSort O) (Bind 
Abst) (TSort O)) (Bind Abst) (TSort O)) (Bind Abst) (TLRef O)) (TLRef (S (S 
O))) H41 (lift (S O) O (TLRef O)) (pc3_s (CHead (CHead (CHead (CSort O) (Bind 
Abst) (TSort O)) (Bind Abst) (TSort O)) (Bind Abst) (TLRef O)) x0 (lift (S O) 
O (TLRef O)) H22)) (TLRef (plus O (S O))) (lift_lref_ge O (S O) O (le_n O))) 
in (let H44 \def H43 in (ex2_ind T (\lambda (t: T).(pr3 (CHead (CHead (CHead 
(CSort O) (Bind Abst) (TSort O)) (Bind Abst) (TSort O)) (Bind Abst) (TLRef 
O)) (TLRef (S (S O))) t)) (\lambda (t: T).(pr3 (CHead (CHead (CHead (CSort O) 
(Bind Abst) (TSort O)) (Bind Abst) (TSort O)) (Bind Abst) (TLRef O)) (TLRef 
(S O)) t)) P (\lambda (x14: T).(\lambda (H45: (pr3 (CHead (CHead (CHead 
(CSort O) (Bind Abst) (TSort O)) (Bind Abst) (TSort O)) (Bind Abst) (TLRef 
O)) (TLRef (S (S O))) x14)).(\lambda (H46: (pr3 (CHead (CHead (CHead (CSort 
O) (Bind Abst) (TSort O)) (Bind Abst) (TSort O)) (Bind Abst) (TLRef O)) 
(TLRef (S O)) x14)).(let H47 \def (eq_ind_r T x14 (\lambda (t: T).(eq T 
(TLRef (S (S O))) t)) (nf2_pr3_unfold (CHead (CHead (CHead (CSort O) (Bind 
Abst) (TSort O)) (Bind Abst) (TSort O)) (Bind Abst) (TLRef O)) (TLRef (S (S 
O))) x14 H45 (nf2_lref_abst (CHead (CHead (CHead (CSort O) (Bind Abst) (TSort 
O)) (Bind Abst) (TSort O)) (Bind Abst) (TLRef O)) (CSort O) (TSort O) (S (S 
O)) (getl_clear_bind Abst (CHead (CHead (CHead (CSort O) (Bind Abst) (TSort 
O)) (Bind Abst) (TSort O)) (Bind Abst) (TLRef O)) (CHead (CHead (CSort O) 
(Bind Abst) (TSort O)) (Bind Abst) (TSort O)) (TLRef O) (clear_bind Abst 
(CHead (CHead (CSort O) (Bind Abst) (TSort O)) (Bind Abst) (TSort O)) (TLRef 
O)) (CHead (CSort O) (Bind Abst) (TSort O)) (S O) (getl_head (Bind Abst) O 
(CHead (CSort O) (Bind Abst) (TSort O)) (CHead (CSort O) (Bind Abst) (TSort 
O)) (getl_refl Abst (CSort O) (TSort O)) (TSort O))))) (TLRef (S O)) 
(nf2_pr3_unfold (CHead (CHead (CHead (CSort O) (Bind Abst) (TSort O)) (Bind 
Abst) (TSort O)) (Bind Abst) (TLRef O)) (TLRef (S O)) x14 H46 (nf2_lref_abst 
(CHead (CHead (CHead (CSort O) (Bind Abst) (TSort O)) (Bind Abst) (TSort O)) 
(Bind Abst) (TLRef O)) (CHead (CSort O) (Bind Abst) (TSort O)) (TSort O) (S 
O) (getl_head (Bind Abst) O (CHead (CHead (CSort O) (Bind Abst) (TSort O)) 
(Bind Abst) (TSort O)) (CHead (CHead (CSort O) (Bind Abst) (TSort O)) (Bind 
Abst) (TSort O)) (getl_refl Abst (CHead (CSort O) (Bind Abst) (TSort O)) 
(TSort O)) (TLRef O))))) in (let H48 \def (eq_ind T (TLRef (S (S O))) 
(\lambda (ee: T).(match ee in T return (\lambda (_: T).Prop) with [(TSort _) 
\Rightarrow False | (TLRef n) \Rightarrow (match n in nat return (\lambda (_: 
nat).Prop) with [O \Rightarrow False | (S n0) \Rightarrow (match n0 in nat 
return (\lambda (_: nat).Prop) with [O \Rightarrow False | (S _) \Rightarrow 
True])]) | (THead _ _ _) \Rightarrow False])) I (TLRef (S O)) H47) in 
(False_ind P H48)))))) H44))))) (pc3_gen_abst (CHead (CHead (CHead (CSort O) 
(Bind Abst) (TSort O)) (Bind Abst) (TSort O)) (Bind Abst) (TLRef O)) (TLRef 
(S (S O))) x0 x5 x1 H7))))))) H35)))))))) H31)) (ty3_gen_lref g (CHead (CHead 
(CSort O) (Bind Abst) (TSort O)) (Bind Abst) (TSort O)) x4 O H23))))))) 
H25)))))))) H18))))) H15)))))))) H11)) (ty3_gen_lref g (CHead (CHead (CHead 
(CSort O) (Bind Abst) (TSort O)) (Bind Abst) (TSort O)) (Bind Abst) (TLRef 
O)) x6 (S (S O)) H8))))))))) (ty3_gen_bind g Abst (CHead (CHead (CHead (CSort 
O) (Bind Abst) (TSort O)) (Bind Abst) (TSort O)) (Bind Abst) (TLRef O)) 
(TLRef (S (S O))) (TSort O) (THead (Bind Abst) x0 x1) H1)))))))) H3)) 
(ty3_gen_lref g (CHead (CHead (CHead (CSort O) (Bind Abst) (TSort O)) (Bind 
Abst) (TSort O)) (Bind Abst) (TLRef O)) x0 O H2))))))) (ty3_gen_appl g (CHead 
(CHead (CHead (CSort O) (Bind Abst) (TSort O)) (Bind Abst) (TSort O)) (Bind 
Abst) (TLRef O)) (TLRef O) (THead (Bind Abst) (TLRef (S (S O))) (TSort O)) u 
H))))).

