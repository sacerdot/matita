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

include "Basic-1/ex1/defs.ma".

include "Basic-1/ty3/fwd.ma".

include "Basic-1/pc3/fwd.ma".

include "Basic-1/nf2/pr3.ma".

include "Basic-1/nf2/props.ma".

include "Basic-1/arity/defs.ma".

include "Basic-1/leq/props.ma".

theorem ex1__leq_sort_SS:
 \forall (g: G).(\forall (k: nat).(\forall (n: nat).(leq g (ASort k n) (asucc 
g (asucc g (ASort (S (S k)) n))))))
\def
 \lambda (g: G).(\lambda (k: nat).(\lambda (n: nat).(leq_refl g (asucc g 
(asucc g (ASort (S (S k)) n)))))).
(* COMMENTS
Initial nodes: 27
END *)

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
(* COMMENTS
Initial nodes: 753
END *)

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
Abbr) x3))).(\lambda (_: (ty3 g x2 x3 x4)).(ex3_2_ind T T (\lambda (t2: 
T).(\lambda (_: T).(pc3 (CHead (CHead (CHead (CSort O) (Bind Abst) (TSort O)) 
(Bind Abst) (TSort O)) (Bind Abst) (TLRef O)) (THead (Bind Abst) (TLRef (S (S 
O))) t2) (THead (Bind Abst) x0 x1)))) (\lambda (_: T).(\lambda (t: T).(ty3 g 
(CHead (CHead (CHead (CSort O) (Bind Abst) (TSort O)) (Bind Abst) (TSort O)) 
(Bind Abst) (TLRef O)) (TLRef (S (S O))) t))) (\lambda (t2: T).(\lambda (_: 
T).(ty3 g (CHead (CHead (CHead (CHead (CSort O) (Bind Abst) (TSort O)) (Bind 
Abst) (TSort O)) (Bind Abst) (TLRef O)) (Bind Abst) (TLRef (S (S O)))) (TSort 
O) t2))) P (\lambda (x5: T).(\lambda (x6: T).(\lambda (_: (pc3 (CHead (CHead 
(CHead (CSort O) (Bind Abst) (TSort O)) (Bind Abst) (TSort O)) (Bind Abst) 
(TLRef O)) (THead (Bind Abst) (TLRef (S (S O))) x5) (THead (Bind Abst) x0 
x1))).(\lambda (H8: (ty3 g (CHead (CHead (CHead (CSort O) (Bind Abst) (TSort 
O)) (Bind Abst) (TSort O)) (Bind Abst) (TLRef O)) (TLRef (S (S O))) 
x6)).(\lambda (_: (ty3 g (CHead (CHead (CHead (CHead (CSort O) (Bind Abst) 
(TSort O)) (Bind Abst) (TSort O)) (Bind Abst) (TLRef O)) (Bind Abst) (TLRef 
(S (S O)))) (TSort O) x5)).(or_ind (ex3_3 C T T (\lambda (_: C).(\lambda (_: 
T).(\lambda (t: T).(pc3 (CHead (CHead (CHead (CSort O) (Bind Abst) (TSort O)) 
(Bind Abst) (TSort O)) (Bind Abst) (TLRef O)) (lift (S (S (S O))) O t) x6)))) 
(\lambda (e: C).(\lambda (u0: T).(\lambda (_: T).(getl (S (S O)) (CHead 
(CHead (CHead (CSort O) (Bind Abst) (TSort O)) (Bind Abst) (TSort O)) (Bind 
Abst) (TLRef O)) (CHead e (Bind Abbr) u0))))) (\lambda (e: C).(\lambda (u0: 
T).(\lambda (t: T).(ty3 g e u0 t))))) (ex3_3 C T T (\lambda (_: C).(\lambda 
(u0: T).(\lambda (_: T).(pc3 (CHead (CHead (CHead (CSort O) (Bind Abst) 
(TSort O)) (Bind Abst) (TSort O)) (Bind Abst) (TLRef O)) (lift (S (S (S O))) 
O u0) x6)))) (\lambda (e: C).(\lambda (u0: T).(\lambda (_: T).(getl (S (S O)) 
(CHead (CHead (CHead (CSort O) (Bind Abst) (TSort O)) (Bind Abst) (TSort O)) 
(Bind Abst) (TLRef O)) (CHead e (Bind Abst) u0))))) (\lambda (e: C).(\lambda 
(u0: T).(\lambda (t: T).(ty3 g e u0 t))))) P (\lambda (H10: (ex3_3 C T T 
(\lambda (_: C).(\lambda (_: T).(\lambda (t: T).(pc3 (CHead (CHead (CHead 
(CSort O) (Bind Abst) (TSort O)) (Bind Abst) (TSort O)) (Bind Abst) (TLRef 
O)) (lift (S (S (S O))) O t) x6)))) (\lambda (e: C).(\lambda (u0: T).(\lambda 
(_: T).(getl (S (S O)) (CHead (CHead (CHead (CSort O) (Bind Abst) (TSort O)) 
(Bind Abst) (TSort O)) (Bind Abst) (TLRef O)) (CHead e (Bind Abbr) u0))))) 
(\lambda (e: C).(\lambda (u0: T).(\lambda (t: T).(ty3 g e u0 
t)))))).(ex3_3_ind C T T (\lambda (_: C).(\lambda (_: T).(\lambda (t: T).(pc3 
(CHead (CHead (CHead (CSort O) (Bind Abst) (TSort O)) (Bind Abst) (TSort O)) 
(Bind Abst) (TLRef O)) (lift (S (S (S O))) O t) x6)))) (\lambda (e: 
C).(\lambda (u0: T).(\lambda (_: T).(getl (S (S O)) (CHead (CHead (CHead 
(CSort O) (Bind Abst) (TSort O)) (Bind Abst) (TSort O)) (Bind Abst) (TLRef 
O)) (CHead e (Bind Abbr) u0))))) (\lambda (e: C).(\lambda (u0: T).(\lambda 
(t: T).(ty3 g e u0 t)))) P (\lambda (x7: C).(\lambda (x8: T).(\lambda (x9: 
T).(\lambda (_: (pc3 (CHead (CHead (CHead (CSort O) (Bind Abst) (TSort O)) 
(Bind Abst) (TSort O)) (Bind Abst) (TLRef O)) (lift (S (S (S O))) O x9) 
x6)).(\lambda (H12: (getl (S (S O)) (CHead (CHead (CHead (CSort O) (Bind 
Abst) (TSort O)) (Bind Abst) (TSort O)) (Bind Abst) (TLRef O)) (CHead x7 
(Bind Abbr) x8))).(\lambda (_: (ty3 g x7 x8 x9)).(let H14 \def (getl_gen_all 
(CHead (CHead (CSort O) (Bind Abst) (TSort O)) (Bind Abst) (TSort O)) (CHead 
x7 (Bind Abbr) x8) (r (Bind Abst) (S O)) (getl_gen_S (Bind Abst) (CHead 
(CHead (CSort O) (Bind Abst) (TSort O)) (Bind Abst) (TSort O)) (CHead x7 
(Bind Abbr) x8) (TLRef O) (S O) H12)) in (ex2_ind C (\lambda (e: C).(drop (S 
O) O (CHead (CHead (CSort O) (Bind Abst) (TSort O)) (Bind Abst) (TSort O)) 
e)) (\lambda (e: C).(clear e (CHead x7 (Bind Abbr) x8))) P (\lambda (x: 
C).(\lambda (_: (drop (S O) O (CHead (CHead (CSort O) (Bind Abst) (TSort O)) 
(Bind Abst) (TSort O)) x)).(\lambda (_: (clear x (CHead x7 (Bind Abbr) 
x8))).(let H17 \def (eq_ind C (CHead x2 (Bind Abbr) x3) (\lambda (ee: 
C).(match ee in C return (\lambda (_: C).Prop) with [(CSort _) \Rightarrow 
False | (CHead _ k _) \Rightarrow (match k in K return (\lambda (_: K).Prop) 
with [(Bind b) \Rightarrow (match b in B return (\lambda (_: B).Prop) with 
[Abbr \Rightarrow True | Abst \Rightarrow False | Void \Rightarrow False]) | 
(Flat _) \Rightarrow False])])) I (CHead (CHead (CHead (CSort O) (Bind Abst) 
(TSort O)) (Bind Abst) (TSort O)) (Bind Abst) (TLRef O)) (clear_gen_bind Abst 
(CHead (CHead (CSort O) (Bind Abst) (TSort O)) (Bind Abst) (TSort O)) (CHead 
x2 (Bind Abbr) x3) (TLRef O) (getl_gen_O (CHead (CHead (CHead (CSort O) (Bind 
Abst) (TSort O)) (Bind Abst) (TSort O)) (Bind Abst) (TLRef O)) (CHead x2 
(Bind Abbr) x3) H5))) in (False_ind P H17))))) H14)))))))) H10)) (\lambda 
(H10: (ex3_3 C T T (\lambda (_: C).(\lambda (u0: T).(\lambda (_: T).(pc3 
(CHead (CHead (CHead (CSort O) (Bind Abst) (TSort O)) (Bind Abst) (TSort O)) 
(Bind Abst) (TLRef O)) (lift (S (S (S O))) O u0) x6)))) (\lambda (e: 
C).(\lambda (u0: T).(\lambda (_: T).(getl (S (S O)) (CHead (CHead (CHead 
(CSort O) (Bind Abst) (TSort O)) (Bind Abst) (TSort O)) (Bind Abst) (TLRef 
O)) (CHead e (Bind Abst) u0))))) (\lambda (e: C).(\lambda (u0: T).(\lambda 
(t: T).(ty3 g e u0 t)))))).(ex3_3_ind C T T (\lambda (_: C).(\lambda (u0: 
T).(\lambda (_: T).(pc3 (CHead (CHead (CHead (CSort O) (Bind Abst) (TSort O)) 
(Bind Abst) (TSort O)) (Bind Abst) (TLRef O)) (lift (S (S (S O))) O u0) 
x6)))) (\lambda (e: C).(\lambda (u0: T).(\lambda (_: T).(getl (S (S O)) 
(CHead (CHead (CHead (CSort O) (Bind Abst) (TSort O)) (Bind Abst) (TSort O)) 
(Bind Abst) (TLRef O)) (CHead e (Bind Abst) u0))))) (\lambda (e: C).(\lambda 
(u0: T).(\lambda (t: T).(ty3 g e u0 t)))) P (\lambda (x7: C).(\lambda (x8: 
T).(\lambda (x9: T).(\lambda (_: (pc3 (CHead (CHead (CHead (CSort O) (Bind 
Abst) (TSort O)) (Bind Abst) (TSort O)) (Bind Abst) (TLRef O)) (lift (S (S (S 
O))) O x8) x6)).(\lambda (H12: (getl (S (S O)) (CHead (CHead (CHead (CSort O) 
(Bind Abst) (TSort O)) (Bind Abst) (TSort O)) (Bind Abst) (TLRef O)) (CHead 
x7 (Bind Abst) x8))).(\lambda (_: (ty3 g x7 x8 x9)).(let H14 \def 
(getl_gen_all (CHead (CHead (CSort O) (Bind Abst) (TSort O)) (Bind Abst) 
(TSort O)) (CHead x7 (Bind Abst) x8) (r (Bind Abst) (S O)) (getl_gen_S (Bind 
Abst) (CHead (CHead (CSort O) (Bind Abst) (TSort O)) (Bind Abst) (TSort O)) 
(CHead x7 (Bind Abst) x8) (TLRef O) (S O) H12)) in (ex2_ind C (\lambda (e: 
C).(drop (S O) O (CHead (CHead (CSort O) (Bind Abst) (TSort O)) (Bind Abst) 
(TSort O)) e)) (\lambda (e: C).(clear e (CHead x7 (Bind Abst) x8))) P 
(\lambda (x: C).(\lambda (_: (drop (S O) O (CHead (CHead (CSort O) (Bind 
Abst) (TSort O)) (Bind Abst) (TSort O)) x)).(\lambda (_: (clear x (CHead x7 
(Bind Abst) x8))).(let H17 \def (eq_ind C (CHead x2 (Bind Abbr) x3) (\lambda 
(ee: C).(match ee in C return (\lambda (_: C).Prop) with [(CSort _) 
\Rightarrow False | (CHead _ k _) \Rightarrow (match k in K return (\lambda 
(_: K).Prop) with [(Bind b) \Rightarrow (match b in B return (\lambda (_: 
B).Prop) with [Abbr \Rightarrow True | Abst \Rightarrow False | Void 
\Rightarrow False]) | (Flat _) \Rightarrow False])])) I (CHead (CHead (CHead 
(CSort O) (Bind Abst) (TSort O)) (Bind Abst) (TSort O)) (Bind Abst) (TLRef 
O)) (clear_gen_bind Abst (CHead (CHead (CSort O) (Bind Abst) (TSort O)) (Bind 
Abst) (TSort O)) (CHead x2 (Bind Abbr) x3) (TLRef O) (getl_gen_O (CHead 
(CHead (CHead (CSort O) (Bind Abst) (TSort O)) (Bind Abst) (TSort O)) (Bind 
Abst) (TLRef O)) (CHead x2 (Bind Abbr) x3) H5))) in (False_ind P H17))))) 
H14)))))))) H10)) (ty3_gen_lref g (CHead (CHead (CHead (CSort O) (Bind Abst) 
(TSort O)) (Bind Abst) (TSort O)) (Bind Abst) (TLRef O)) x6 (S (S O)) 
H8))))))) (ty3_gen_bind g Abst (CHead (CHead (CHead (CSort O) (Bind Abst) 
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
(CHead x2 (Bind Abst) x3))).(\lambda (H6: (ty3 g x2 x3 x4)).(ex3_2_ind T T 
(\lambda (t2: T).(\lambda (_: T).(pc3 (CHead (CHead (CHead (CSort O) (Bind 
Abst) (TSort O)) (Bind Abst) (TSort O)) (Bind Abst) (TLRef O)) (THead (Bind 
Abst) (TLRef (S (S O))) t2) (THead (Bind Abst) x0 x1)))) (\lambda (_: 
T).(\lambda (t: T).(ty3 g (CHead (CHead (CHead (CSort O) (Bind Abst) (TSort 
O)) (Bind Abst) (TSort O)) (Bind Abst) (TLRef O)) (TLRef (S (S O))) t))) 
(\lambda (t2: T).(\lambda (_: T).(ty3 g (CHead (CHead (CHead (CHead (CSort O) 
(Bind Abst) (TSort O)) (Bind Abst) (TSort O)) (Bind Abst) (TLRef O)) (Bind 
Abst) (TLRef (S (S O)))) (TSort O) t2))) P (\lambda (x5: T).(\lambda (x6: 
T).(\lambda (H7: (pc3 (CHead (CHead (CHead (CSort O) (Bind Abst) (TSort O)) 
(Bind Abst) (TSort O)) (Bind Abst) (TLRef O)) (THead (Bind Abst) (TLRef (S (S 
O))) x5) (THead (Bind Abst) x0 x1))).(\lambda (H8: (ty3 g (CHead (CHead 
(CHead (CSort O) (Bind Abst) (TSort O)) (Bind Abst) (TSort O)) (Bind Abst) 
(TLRef O)) (TLRef (S (S O))) x6)).(\lambda (_: (ty3 g (CHead (CHead (CHead 
(CHead (CSort O) (Bind Abst) (TSort O)) (Bind Abst) (TSort O)) (Bind Abst) 
(TLRef O)) (Bind Abst) (TLRef (S (S O)))) (TSort O) x5)).(or_ind (ex3_3 C T T 
(\lambda (_: C).(\lambda (_: T).(\lambda (t: T).(pc3 (CHead (CHead (CHead 
(CSort O) (Bind Abst) (TSort O)) (Bind Abst) (TSort O)) (Bind Abst) (TLRef 
O)) (lift (S (S (S O))) O t) x6)))) (\lambda (e: C).(\lambda (u0: T).(\lambda 
(_: T).(getl (S (S O)) (CHead (CHead (CHead (CSort O) (Bind Abst) (TSort O)) 
(Bind Abst) (TSort O)) (Bind Abst) (TLRef O)) (CHead e (Bind Abbr) u0))))) 
(\lambda (e: C).(\lambda (u0: T).(\lambda (t: T).(ty3 g e u0 t))))) (ex3_3 C 
T T (\lambda (_: C).(\lambda (u0: T).(\lambda (_: T).(pc3 (CHead (CHead 
(CHead (CSort O) (Bind Abst) (TSort O)) (Bind Abst) (TSort O)) (Bind Abst) 
(TLRef O)) (lift (S (S (S O))) O u0) x6)))) (\lambda (e: C).(\lambda (u0: 
T).(\lambda (_: T).(getl (S (S O)) (CHead (CHead (CHead (CSort O) (Bind Abst) 
(TSort O)) (Bind Abst) (TSort O)) (Bind Abst) (TLRef O)) (CHead e (Bind Abst) 
u0))))) (\lambda (e: C).(\lambda (u0: T).(\lambda (t: T).(ty3 g e u0 t))))) P 
(\lambda (H10: (ex3_3 C T T (\lambda (_: C).(\lambda (_: T).(\lambda (t: 
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
T).(\lambda (t: T).(ty3 g e u0 t)))) P (\lambda (x7: C).(\lambda (x8: 
T).(\lambda (x9: T).(\lambda (_: (pc3 (CHead (CHead (CHead (CSort O) (Bind 
Abst) (TSort O)) (Bind Abst) (TSort O)) (Bind Abst) (TLRef O)) (lift (S (S (S 
O))) O x9) x6)).(\lambda (H12: (getl (S (S O)) (CHead (CHead (CHead (CSort O) 
(Bind Abst) (TSort O)) (Bind Abst) (TSort O)) (Bind Abst) (TLRef O)) (CHead 
x7 (Bind Abbr) x8))).(\lambda (_: (ty3 g x7 x8 x9)).(let H14 \def 
(getl_gen_all (CHead (CHead (CSort O) (Bind Abst) (TSort O)) (Bind Abst) 
(TSort O)) (CHead x7 (Bind Abbr) x8) (r (Bind Abst) (S O)) (getl_gen_S (Bind 
Abst) (CHead (CHead (CSort O) (Bind Abst) (TSort O)) (Bind Abst) (TSort O)) 
(CHead x7 (Bind Abbr) x8) (TLRef O) (S O) H12)) in (ex2_ind C (\lambda (e: 
C).(drop (S O) O (CHead (CHead (CSort O) (Bind Abst) (TSort O)) (Bind Abst) 
(TSort O)) e)) (\lambda (e: C).(clear e (CHead x7 (Bind Abbr) x8))) P 
(\lambda (x: C).(\lambda (H15: (drop (S O) O (CHead (CHead (CSort O) (Bind 
Abst) (TSort O)) (Bind Abst) (TSort O)) x)).(\lambda (H16: (clear x (CHead x7 
(Bind Abbr) x8))).(let H17 \def (f_equal C C (\lambda (e: C).(match e in C 
return (\lambda (_: C).C) with [(CSort _) \Rightarrow x2 | (CHead c _ _) 
\Rightarrow c])) (CHead x2 (Bind Abst) x3) (CHead (CHead (CHead (CSort O) 
(Bind Abst) (TSort O)) (Bind Abst) (TSort O)) (Bind Abst) (TLRef O)) 
(clear_gen_bind Abst (CHead (CHead (CSort O) (Bind Abst) (TSort O)) (Bind 
Abst) (TSort O)) (CHead x2 (Bind Abst) x3) (TLRef O) (getl_gen_O (CHead 
(CHead (CHead (CSort O) (Bind Abst) (TSort O)) (Bind Abst) (TSort O)) (Bind 
Abst) (TLRef O)) (CHead x2 (Bind Abst) x3) H5))) in ((let H18 \def (f_equal C 
T (\lambda (e: C).(match e in C return (\lambda (_: C).T) with [(CSort _) 
\Rightarrow x3 | (CHead _ _ t) \Rightarrow t])) (CHead x2 (Bind Abst) x3) 
(CHead (CHead (CHead (CSort O) (Bind Abst) (TSort O)) (Bind Abst) (TSort O)) 
(Bind Abst) (TLRef O)) (clear_gen_bind Abst (CHead (CHead (CSort O) (Bind 
Abst) (TSort O)) (Bind Abst) (TSort O)) (CHead x2 (Bind Abst) x3) (TLRef O) 
(getl_gen_O (CHead (CHead (CHead (CSort O) (Bind Abst) (TSort O)) (Bind Abst) 
(TSort O)) (Bind Abst) (TLRef O)) (CHead x2 (Bind Abst) x3) H5))) in (\lambda 
(H19: (eq C x2 (CHead (CHead (CSort O) (Bind Abst) (TSort O)) (Bind Abst) 
(TSort O)))).(let H20 \def (eq_ind T x3 (\lambda (t: T).(ty3 g x2 t x4)) H6 
(TLRef O) H18) in (let H21 \def (eq_ind T x3 (\lambda (t: T).(pc3 (CHead 
(CHead (CHead (CSort O) (Bind Abst) (TSort O)) (Bind Abst) (TSort O)) (Bind 
Abst) (TLRef O)) (lift (S O) O t) x0)) H4 (TLRef O) H18) in (let H22 \def 
(eq_ind C x2 (\lambda (c: C).(ty3 g c (TLRef O) x4)) H20 (CHead (CHead (CSort 
O) (Bind Abst) (TSort O)) (Bind Abst) (TSort O)) H19) in (let H23 \def 
(eq_ind_r C x (\lambda (c: C).(clear c (CHead x7 (Bind Abbr) x8))) H16 (CHead 
(CSort O) (Bind Abst) (TSort O)) (drop_gen_refl (CHead (CSort O) (Bind Abst) 
(TSort O)) x (drop_gen_drop (Bind Abst) (CHead (CSort O) (Bind Abst) (TSort 
O)) x (TSort O) O H15))) in (let H24 \def (eq_ind C (CHead x7 (Bind Abbr) x8) 
(\lambda (ee: C).(match ee in C return (\lambda (_: C).Prop) with [(CSort _) 
\Rightarrow False | (CHead _ k _) \Rightarrow (match k in K return (\lambda 
(_: K).Prop) with [(Bind b) \Rightarrow (match b in B return (\lambda (_: 
B).Prop) with [Abbr \Rightarrow True | Abst \Rightarrow False | Void 
\Rightarrow False]) | (Flat _) \Rightarrow False])])) I (CHead (CSort O) 
(Bind Abst) (TSort O)) (clear_gen_bind Abst (CSort O) (CHead x7 (Bind Abbr) 
x8) (TSort O) H23)) in (False_ind P H24)))))))) H17))))) H14)))))))) H10)) 
(\lambda (H10: (ex3_3 C T T (\lambda (_: C).(\lambda (u0: T).(\lambda (_: 
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
(u0: T).(\lambda (t: T).(ty3 g e u0 t)))) P (\lambda (x7: C).(\lambda (x8: 
T).(\lambda (x9: T).(\lambda (H11: (pc3 (CHead (CHead (CHead (CSort O) (Bind 
Abst) (TSort O)) (Bind Abst) (TSort O)) (Bind Abst) (TLRef O)) (lift (S (S (S 
O))) O x8) x6)).(\lambda (H12: (getl (S (S O)) (CHead (CHead (CHead (CSort O) 
(Bind Abst) (TSort O)) (Bind Abst) (TSort O)) (Bind Abst) (TLRef O)) (CHead 
x7 (Bind Abst) x8))).(\lambda (H13: (ty3 g x7 x8 x9)).(let H14 \def 
(getl_gen_all (CHead (CHead (CSort O) (Bind Abst) (TSort O)) (Bind Abst) 
(TSort O)) (CHead x7 (Bind Abst) x8) (r (Bind Abst) (S O)) (getl_gen_S (Bind 
Abst) (CHead (CHead (CSort O) (Bind Abst) (TSort O)) (Bind Abst) (TSort O)) 
(CHead x7 (Bind Abst) x8) (TLRef O) (S O) H12)) in (ex2_ind C (\lambda (e: 
C).(drop (S O) O (CHead (CHead (CSort O) (Bind Abst) (TSort O)) (Bind Abst) 
(TSort O)) e)) (\lambda (e: C).(clear e (CHead x7 (Bind Abst) x8))) P 
(\lambda (x: C).(\lambda (H15: (drop (S O) O (CHead (CHead (CSort O) (Bind 
Abst) (TSort O)) (Bind Abst) (TSort O)) x)).(\lambda (H16: (clear x (CHead x7 
(Bind Abst) x8))).(let H17 \def (f_equal C C (\lambda (e: C).(match e in C 
return (\lambda (_: C).C) with [(CSort _) \Rightarrow x2 | (CHead c _ _) 
\Rightarrow c])) (CHead x2 (Bind Abst) x3) (CHead (CHead (CHead (CSort O) 
(Bind Abst) (TSort O)) (Bind Abst) (TSort O)) (Bind Abst) (TLRef O)) 
(clear_gen_bind Abst (CHead (CHead (CSort O) (Bind Abst) (TSort O)) (Bind 
Abst) (TSort O)) (CHead x2 (Bind Abst) x3) (TLRef O) (getl_gen_O (CHead 
(CHead (CHead (CSort O) (Bind Abst) (TSort O)) (Bind Abst) (TSort O)) (Bind 
Abst) (TLRef O)) (CHead x2 (Bind Abst) x3) H5))) in ((let H18 \def (f_equal C 
T (\lambda (e: C).(match e in C return (\lambda (_: C).T) with [(CSort _) 
\Rightarrow x3 | (CHead _ _ t) \Rightarrow t])) (CHead x2 (Bind Abst) x3) 
(CHead (CHead (CHead (CSort O) (Bind Abst) (TSort O)) (Bind Abst) (TSort O)) 
(Bind Abst) (TLRef O)) (clear_gen_bind Abst (CHead (CHead (CSort O) (Bind 
Abst) (TSort O)) (Bind Abst) (TSort O)) (CHead x2 (Bind Abst) x3) (TLRef O) 
(getl_gen_O (CHead (CHead (CHead (CSort O) (Bind Abst) (TSort O)) (Bind Abst) 
(TSort O)) (Bind Abst) (TLRef O)) (CHead x2 (Bind Abst) x3) H5))) in (\lambda 
(H19: (eq C x2 (CHead (CHead (CSort O) (Bind Abst) (TSort O)) (Bind Abst) 
(TSort O)))).(let H20 \def (eq_ind T x3 (\lambda (t: T).(ty3 g x2 t x4)) H6 
(TLRef O) H18) in (let H21 \def (eq_ind T x3 (\lambda (t: T).(pc3 (CHead 
(CHead (CHead (CSort O) (Bind Abst) (TSort O)) (Bind Abst) (TSort O)) (Bind 
Abst) (TLRef O)) (lift (S O) O t) x0)) H4 (TLRef O) H18) in (let H22 \def 
(eq_ind C x2 (\lambda (c: C).(ty3 g c (TLRef O) x4)) H20 (CHead (CHead (CSort 
O) (Bind Abst) (TSort O)) (Bind Abst) (TSort O)) H19) in (let H23 \def 
(eq_ind_r C x (\lambda (c: C).(clear c (CHead x7 (Bind Abst) x8))) H16 (CHead 
(CSort O) (Bind Abst) (TSort O)) (drop_gen_refl (CHead (CSort O) (Bind Abst) 
(TSort O)) x (drop_gen_drop (Bind Abst) (CHead (CSort O) (Bind Abst) (TSort 
O)) x (TSort O) O H15))) in (let H24 \def (f_equal C C (\lambda (e: C).(match 
e in C return (\lambda (_: C).C) with [(CSort _) \Rightarrow x7 | (CHead c _ 
_) \Rightarrow c])) (CHead x7 (Bind Abst) x8) (CHead (CSort O) (Bind Abst) 
(TSort O)) (clear_gen_bind Abst (CSort O) (CHead x7 (Bind Abst) x8) (TSort O) 
H23)) in ((let H25 \def (f_equal C T (\lambda (e: C).(match e in C return 
(\lambda (_: C).T) with [(CSort _) \Rightarrow x8 | (CHead _ _ t) \Rightarrow 
t])) (CHead x7 (Bind Abst) x8) (CHead (CSort O) (Bind Abst) (TSort O)) 
(clear_gen_bind Abst (CSort O) (CHead x7 (Bind Abst) x8) (TSort O) H23)) in 
(\lambda (H26: (eq C x7 (CSort O))).(let H27 \def (eq_ind T x8 (\lambda (t: 
T).(ty3 g x7 t x9)) H13 (TSort O) H25) in (let H28 \def (eq_ind T x8 (\lambda 
(t: T).(pc3 (CHead (CHead (CHead (CSort O) (Bind Abst) (TSort O)) (Bind Abst) 
(TSort O)) (Bind Abst) (TLRef O)) (lift (S (S (S O))) O t) x6)) H11 (TSort O) 
H25) in (let H29 \def (eq_ind C x7 (\lambda (c: C).(ty3 g c (TSort O) x9)) 
H27 (CSort O) H26) in (or_ind (ex3_3 C T T (\lambda (_: C).(\lambda (_: 
T).(\lambda (t: T).(pc3 (CHead (CHead (CSort O) (Bind Abst) (TSort O)) (Bind 
Abst) (TSort O)) (lift (S O) O t) x4)))) (\lambda (e: C).(\lambda (u0: 
T).(\lambda (_: T).(getl O (CHead (CHead (CSort O) (Bind Abst) (TSort O)) 
(Bind Abst) (TSort O)) (CHead e (Bind Abbr) u0))))) (\lambda (e: C).(\lambda 
(u0: T).(\lambda (t: T).(ty3 g e u0 t))))) (ex3_3 C T T (\lambda (_: 
C).(\lambda (u0: T).(\lambda (_: T).(pc3 (CHead (CHead (CSort O) (Bind Abst) 
(TSort O)) (Bind Abst) (TSort O)) (lift (S O) O u0) x4)))) (\lambda (e: 
C).(\lambda (u0: T).(\lambda (_: T).(getl O (CHead (CHead (CSort O) (Bind 
Abst) (TSort O)) (Bind Abst) (TSort O)) (CHead e (Bind Abst) u0))))) (\lambda 
(e: C).(\lambda (u0: T).(\lambda (t: T).(ty3 g e u0 t))))) P (\lambda (H30: 
(ex3_3 C T T (\lambda (_: C).(\lambda (_: T).(\lambda (t: T).(pc3 (CHead 
(CHead (CSort O) (Bind Abst) (TSort O)) (Bind Abst) (TSort O)) (lift (S O) O 
t) x4)))) (\lambda (e: C).(\lambda (u0: T).(\lambda (_: T).(getl O (CHead 
(CHead (CSort O) (Bind Abst) (TSort O)) (Bind Abst) (TSort O)) (CHead e (Bind 
Abbr) u0))))) (\lambda (e: C).(\lambda (u0: T).(\lambda (t: T).(ty3 g e u0 
t)))))).(ex3_3_ind C T T (\lambda (_: C).(\lambda (_: T).(\lambda (t: T).(pc3 
(CHead (CHead (CSort O) (Bind Abst) (TSort O)) (Bind Abst) (TSort O)) (lift 
(S O) O t) x4)))) (\lambda (e: C).(\lambda (u0: T).(\lambda (_: T).(getl O 
(CHead (CHead (CSort O) (Bind Abst) (TSort O)) (Bind Abst) (TSort O)) (CHead 
e (Bind Abbr) u0))))) (\lambda (e: C).(\lambda (u0: T).(\lambda (t: T).(ty3 g 
e u0 t)))) P (\lambda (x10: C).(\lambda (x11: T).(\lambda (x12: T).(\lambda 
(_: (pc3 (CHead (CHead (CSort O) (Bind Abst) (TSort O)) (Bind Abst) (TSort 
O)) (lift (S O) O x12) x4)).(\lambda (H32: (getl O (CHead (CHead (CSort O) 
(Bind Abst) (TSort O)) (Bind Abst) (TSort O)) (CHead x10 (Bind Abbr) 
x11))).(\lambda (_: (ty3 g x10 x11 x12)).(let H34 \def (eq_ind C (CHead x10 
(Bind Abbr) x11) (\lambda (ee: C).(match ee in C return (\lambda (_: C).Prop) 
with [(CSort _) \Rightarrow False | (CHead _ k _) \Rightarrow (match k in K 
return (\lambda (_: K).Prop) with [(Bind b) \Rightarrow (match b in B return 
(\lambda (_: B).Prop) with [Abbr \Rightarrow True | Abst \Rightarrow False | 
Void \Rightarrow False]) | (Flat _) \Rightarrow False])])) I (CHead (CHead 
(CSort O) (Bind Abst) (TSort O)) (Bind Abst) (TSort O)) (clear_gen_bind Abst 
(CHead (CSort O) (Bind Abst) (TSort O)) (CHead x10 (Bind Abbr) x11) (TSort O) 
(getl_gen_O (CHead (CHead (CSort O) (Bind Abst) (TSort O)) (Bind Abst) (TSort 
O)) (CHead x10 (Bind Abbr) x11) H32))) in (False_ind P H34)))))))) H30)) 
(\lambda (H30: (ex3_3 C T T (\lambda (_: C).(\lambda (u0: T).(\lambda (_: 
T).(pc3 (CHead (CHead (CSort O) (Bind Abst) (TSort O)) (Bind Abst) (TSort O)) 
(lift (S O) O u0) x4)))) (\lambda (e: C).(\lambda (u0: T).(\lambda (_: 
T).(getl O (CHead (CHead (CSort O) (Bind Abst) (TSort O)) (Bind Abst) (TSort 
O)) (CHead e (Bind Abst) u0))))) (\lambda (e: C).(\lambda (u0: T).(\lambda 
(t: T).(ty3 g e u0 t)))))).(ex3_3_ind C T T (\lambda (_: C).(\lambda (u0: 
T).(\lambda (_: T).(pc3 (CHead (CHead (CSort O) (Bind Abst) (TSort O)) (Bind 
Abst) (TSort O)) (lift (S O) O u0) x4)))) (\lambda (e: C).(\lambda (u0: 
T).(\lambda (_: T).(getl O (CHead (CHead (CSort O) (Bind Abst) (TSort O)) 
(Bind Abst) (TSort O)) (CHead e (Bind Abst) u0))))) (\lambda (e: C).(\lambda 
(u0: T).(\lambda (t: T).(ty3 g e u0 t)))) P (\lambda (x10: C).(\lambda (x11: 
T).(\lambda (x12: T).(\lambda (H31: (pc3 (CHead (CHead (CSort O) (Bind Abst) 
(TSort O)) (Bind Abst) (TSort O)) (lift (S O) O x11) x4)).(\lambda (H32: 
(getl O (CHead (CHead (CSort O) (Bind Abst) (TSort O)) (Bind Abst) (TSort O)) 
(CHead x10 (Bind Abst) x11))).(\lambda (H33: (ty3 g x10 x11 x12)).(let H34 
\def (f_equal C C (\lambda (e: C).(match e in C return (\lambda (_: C).C) 
with [(CSort _) \Rightarrow x10 | (CHead c _ _) \Rightarrow c])) (CHead x10 
(Bind Abst) x11) (CHead (CHead (CSort O) (Bind Abst) (TSort O)) (Bind Abst) 
(TSort O)) (clear_gen_bind Abst (CHead (CSort O) (Bind Abst) (TSort O)) 
(CHead x10 (Bind Abst) x11) (TSort O) (getl_gen_O (CHead (CHead (CSort O) 
(Bind Abst) (TSort O)) (Bind Abst) (TSort O)) (CHead x10 (Bind Abst) x11) 
H32))) in ((let H35 \def (f_equal C T (\lambda (e: C).(match e in C return 
(\lambda (_: C).T) with [(CSort _) \Rightarrow x11 | (CHead _ _ t) 
\Rightarrow t])) (CHead x10 (Bind Abst) x11) (CHead (CHead (CSort O) (Bind 
Abst) (TSort O)) (Bind Abst) (TSort O)) (clear_gen_bind Abst (CHead (CSort O) 
(Bind Abst) (TSort O)) (CHead x10 (Bind Abst) x11) (TSort O) (getl_gen_O 
(CHead (CHead (CSort O) (Bind Abst) (TSort O)) (Bind Abst) (TSort O)) (CHead 
x10 (Bind Abst) x11) H32))) in (\lambda (H36: (eq C x10 (CHead (CSort O) 
(Bind Abst) (TSort O)))).(let H37 \def (eq_ind T x11 (\lambda (t: T).(ty3 g 
x10 t x12)) H33 (TSort O) H35) in (let H38 \def (eq_ind T x11 (\lambda (t: 
T).(pc3 (CHead (CHead (CSort O) (Bind Abst) (TSort O)) (Bind Abst) (TSort O)) 
(lift (S O) O t) x4)) H31 (TSort O) H35) in (let H39 \def (eq_ind C x10 
(\lambda (c: C).(ty3 g c (TSort O) x12)) H37 (CHead (CSort O) (Bind Abst) 
(TSort O)) H36) in (land_ind (pc3 (CHead (CHead (CHead (CSort O) (Bind Abst) 
(TSort O)) (Bind Abst) (TSort O)) (Bind Abst) (TLRef O)) (TLRef (S (S O))) 
x0) (\forall (b: B).(\forall (u0: T).(pc3 (CHead (CHead (CHead (CHead (CSort 
O) (Bind Abst) (TSort O)) (Bind Abst) (TSort O)) (Bind Abst) (TLRef O)) (Bind 
b) u0) x5 x1))) P (\lambda (H40: (pc3 (CHead (CHead (CHead (CSort O) (Bind 
Abst) (TSort O)) (Bind Abst) (TSort O)) (Bind Abst) (TLRef O)) (TLRef (S (S 
O))) x0)).(\lambda (_: ((\forall (b: B).(\forall (u0: T).(pc3 (CHead (CHead 
(CHead (CHead (CSort O) (Bind Abst) (TSort O)) (Bind Abst) (TSort O)) (Bind 
Abst) (TLRef O)) (Bind b) u0) x5 x1))))).(let H42 \def (eq_ind T (lift (S O) 
O (TLRef O)) (\lambda (t: T).(pc3 (CHead (CHead (CHead (CSort O) (Bind Abst) 
(TSort O)) (Bind Abst) (TSort O)) (Bind Abst) (TLRef O)) (TLRef (S (S O))) 
t)) (pc3_t x0 (CHead (CHead (CHead (CSort O) (Bind Abst) (TSort O)) (Bind 
Abst) (TSort O)) (Bind Abst) (TLRef O)) (TLRef (S (S O))) H40 (lift (S O) O 
(TLRef O)) (ex2_sym T (pr3 (CHead (CHead (CHead (CSort O) (Bind Abst) (TSort 
O)) (Bind Abst) (TSort O)) (Bind Abst) (TLRef O)) (lift (S O) O (TLRef O))) 
(pr3 (CHead (CHead (CHead (CSort O) (Bind Abst) (TSort O)) (Bind Abst) (TSort 
O)) (Bind Abst) (TLRef O)) x0) H21)) (TLRef (plus O (S O))) (lift_lref_ge O 
(S O) O (le_n O))) in (let H43 \def H42 in (ex2_ind T (\lambda (t: T).(pr3 
(CHead (CHead (CHead (CSort O) (Bind Abst) (TSort O)) (Bind Abst) (TSort O)) 
(Bind Abst) (TLRef O)) (TLRef (S (S O))) t)) (\lambda (t: T).(pr3 (CHead 
(CHead (CHead (CSort O) (Bind Abst) (TSort O)) (Bind Abst) (TSort O)) (Bind 
Abst) (TLRef O)) (TLRef (S O)) t)) P (\lambda (x13: T).(\lambda (H44: (pr3 
(CHead (CHead (CHead (CSort O) (Bind Abst) (TSort O)) (Bind Abst) (TSort O)) 
(Bind Abst) (TLRef O)) (TLRef (S (S O))) x13)).(\lambda (H45: (pr3 (CHead 
(CHead (CHead (CSort O) (Bind Abst) (TSort O)) (Bind Abst) (TSort O)) (Bind 
Abst) (TLRef O)) (TLRef (S O)) x13)).(let H46 \def (eq_ind_r T x13 (\lambda 
(t: T).(eq T (TLRef (S (S O))) t)) (nf2_pr3_unfold (CHead (CHead (CHead 
(CSort O) (Bind Abst) (TSort O)) (Bind Abst) (TSort O)) (Bind Abst) (TLRef 
O)) (TLRef (S (S O))) x13 H44 (nf2_lref_abst (CHead (CHead (CHead (CSort O) 
(Bind Abst) (TSort O)) (Bind Abst) (TSort O)) (Bind Abst) (TLRef O)) (CSort 
O) (TSort O) (S (S O)) (getl_clear_bind Abst (CHead (CHead (CHead (CSort O) 
(Bind Abst) (TSort O)) (Bind Abst) (TSort O)) (Bind Abst) (TLRef O)) (CHead 
(CHead (CSort O) (Bind Abst) (TSort O)) (Bind Abst) (TSort O)) (TLRef O) 
(clear_bind Abst (CHead (CHead (CSort O) (Bind Abst) (TSort O)) (Bind Abst) 
(TSort O)) (TLRef O)) (CHead (CSort O) (Bind Abst) (TSort O)) (S O) 
(getl_head (Bind Abst) O (CHead (CSort O) (Bind Abst) (TSort O)) (CHead 
(CSort O) (Bind Abst) (TSort O)) (getl_refl Abst (CSort O) (TSort O)) (TSort 
O))))) (TLRef (S O)) (nf2_pr3_unfold (CHead (CHead (CHead (CSort O) (Bind 
Abst) (TSort O)) (Bind Abst) (TSort O)) (Bind Abst) (TLRef O)) (TLRef (S O)) 
x13 H45 (nf2_lref_abst (CHead (CHead (CHead (CSort O) (Bind Abst) (TSort O)) 
(Bind Abst) (TSort O)) (Bind Abst) (TLRef O)) (CHead (CSort O) (Bind Abst) 
(TSort O)) (TSort O) (S O) (getl_head (Bind Abst) O (CHead (CHead (CSort O) 
(Bind Abst) (TSort O)) (Bind Abst) (TSort O)) (CHead (CHead (CSort O) (Bind 
Abst) (TSort O)) (Bind Abst) (TSort O)) (getl_refl Abst (CHead (CSort O) 
(Bind Abst) (TSort O)) (TSort O)) (TLRef O))))) in (let H47 \def (eq_ind T 
(TLRef (S (S O))) (\lambda (ee: T).(match ee in T return (\lambda (_: 
T).Prop) with [(TSort _) \Rightarrow False | (TLRef n) \Rightarrow (match n 
in nat return (\lambda (_: nat).Prop) with [O \Rightarrow False | (S n0) 
\Rightarrow (match n0 in nat return (\lambda (_: nat).Prop) with [O 
\Rightarrow False | (S _) \Rightarrow True])]) | (THead _ _ _) \Rightarrow 
False])) I (TLRef (S O)) H46) in (False_ind P H47)))))) H43))))) 
(pc3_gen_abst (CHead (CHead (CHead (CSort O) (Bind Abst) (TSort O)) (Bind 
Abst) (TSort O)) (Bind Abst) (TLRef O)) (TLRef (S (S O))) x0 x5 x1 H7))))))) 
H34)))))))) H30)) (ty3_gen_lref g (CHead (CHead (CSort O) (Bind Abst) (TSort 
O)) (Bind Abst) (TSort O)) x4 O H22))))))) H24)))))))) H17))))) H14)))))))) 
H10)) (ty3_gen_lref g (CHead (CHead (CHead (CSort O) (Bind Abst) (TSort O)) 
(Bind Abst) (TSort O)) (Bind Abst) (TLRef O)) x6 (S (S O)) H8))))))) 
(ty3_gen_bind g Abst (CHead (CHead (CHead (CSort O) (Bind Abst) (TSort O)) 
(Bind Abst) (TSort O)) (Bind Abst) (TLRef O)) (TLRef (S (S O))) (TSort O) 
(THead (Bind Abst) x0 x1) H1)))))))) H3)) (ty3_gen_lref g (CHead (CHead 
(CHead (CSort O) (Bind Abst) (TSort O)) (Bind Abst) (TSort O)) (Bind Abst) 
(TLRef O)) x0 O H2))))))) (ty3_gen_appl g (CHead (CHead (CHead (CSort O) 
(Bind Abst) (TSort O)) (Bind Abst) (TSort O)) (Bind Abst) (TLRef O)) (TLRef 
O) (THead (Bind Abst) (TLRef (S (S O))) (TSort O)) u H))))).
(* COMMENTS
Initial nodes: 9973
END *)

