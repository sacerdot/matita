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

include "Basic-1/getl/props.ma".

theorem getl_dec:
 \forall (c: C).(\forall (i: nat).(or (ex_3 C B T (\lambda (e: C).(\lambda 
(b: B).(\lambda (v: T).(getl i c (CHead e (Bind b) v)))))) (\forall (d: 
C).((getl i c d) \to (\forall (P: Prop).P)))))
\def
 \lambda (c: C).(C_ind (\lambda (c0: C).(\forall (i: nat).(or (ex_3 C B T 
(\lambda (e: C).(\lambda (b: B).(\lambda (v: T).(getl i c0 (CHead e (Bind b) 
v)))))) (\forall (d: C).((getl i c0 d) \to (\forall (P: Prop).P)))))) 
(\lambda (n: nat).(\lambda (i: nat).(or_intror (ex_3 C B T (\lambda (e: 
C).(\lambda (b: B).(\lambda (v: T).(getl i (CSort n) (CHead e (Bind b) 
v)))))) (\forall (d: C).((getl i (CSort n) d) \to (\forall (P: Prop).P))) 
(\lambda (d: C).(\lambda (H: (getl i (CSort n) d)).(\lambda (P: 
Prop).(getl_gen_sort n i d H P))))))) (\lambda (c0: C).(\lambda (H: ((\forall 
(i: nat).(or (ex_3 C B T (\lambda (e: C).(\lambda (b: B).(\lambda (v: 
T).(getl i c0 (CHead e (Bind b) v)))))) (\forall (d: C).((getl i c0 d) \to 
(\forall (P: Prop).P))))))).(\lambda (k: K).(\lambda (t: T).(\lambda (i: 
nat).(nat_ind (\lambda (n: nat).(or (ex_3 C B T (\lambda (e: C).(\lambda (b: 
B).(\lambda (v: T).(getl n (CHead c0 k t) (CHead e (Bind b) v)))))) (\forall 
(d: C).((getl n (CHead c0 k t) d) \to (\forall (P: Prop).P))))) (K_ind 
(\lambda (k0: K).(or (ex_3 C B T (\lambda (e: C).(\lambda (b: B).(\lambda (v: 
T).(getl O (CHead c0 k0 t) (CHead e (Bind b) v)))))) (\forall (d: C).((getl O 
(CHead c0 k0 t) d) \to (\forall (P: Prop).P))))) (\lambda (b: B).(or_introl 
(ex_3 C B T (\lambda (e: C).(\lambda (b0: B).(\lambda (v: T).(getl O (CHead 
c0 (Bind b) t) (CHead e (Bind b0) v)))))) (\forall (d: C).((getl O (CHead c0 
(Bind b) t) d) \to (\forall (P: Prop).P))) (ex_3_intro C B T (\lambda (e: 
C).(\lambda (b0: B).(\lambda (v: T).(getl O (CHead c0 (Bind b) t) (CHead e 
(Bind b0) v))))) c0 b t (getl_refl b c0 t)))) (\lambda (f: F).(let H_x \def 
(H O) in (let H0 \def H_x in (or_ind (ex_3 C B T (\lambda (e: C).(\lambda (b: 
B).(\lambda (v: T).(getl O c0 (CHead e (Bind b) v)))))) (\forall (d: 
C).((getl O c0 d) \to (\forall (P: Prop).P))) (or (ex_3 C B T (\lambda (e: 
C).(\lambda (b: B).(\lambda (v: T).(getl O (CHead c0 (Flat f) t) (CHead e 
(Bind b) v)))))) (\forall (d: C).((getl O (CHead c0 (Flat f) t) d) \to 
(\forall (P: Prop).P)))) (\lambda (H1: (ex_3 C B T (\lambda (e: C).(\lambda 
(b: B).(\lambda (v: T).(getl O c0 (CHead e (Bind b) v))))))).(ex_3_ind C B T 
(\lambda (e: C).(\lambda (b: B).(\lambda (v: T).(getl O c0 (CHead e (Bind b) 
v))))) (or (ex_3 C B T (\lambda (e: C).(\lambda (b: B).(\lambda (v: T).(getl 
O (CHead c0 (Flat f) t) (CHead e (Bind b) v)))))) (\forall (d: C).((getl O 
(CHead c0 (Flat f) t) d) \to (\forall (P: Prop).P)))) (\lambda (x0: 
C).(\lambda (x1: B).(\lambda (x2: T).(\lambda (H2: (getl O c0 (CHead x0 (Bind 
x1) x2))).(or_introl (ex_3 C B T (\lambda (e: C).(\lambda (b: B).(\lambda (v: 
T).(getl O (CHead c0 (Flat f) t) (CHead e (Bind b) v)))))) (\forall (d: 
C).((getl O (CHead c0 (Flat f) t) d) \to (\forall (P: Prop).P))) (ex_3_intro 
C B T (\lambda (e: C).(\lambda (b: B).(\lambda (v: T).(getl O (CHead c0 (Flat 
f) t) (CHead e (Bind b) v))))) x0 x1 x2 (getl_flat c0 (CHead x0 (Bind x1) x2) 
O H2 f t))))))) H1)) (\lambda (H1: ((\forall (d: C).((getl O c0 d) \to 
(\forall (P: Prop).P))))).(or_intror (ex_3 C B T (\lambda (e: C).(\lambda (b: 
B).(\lambda (v: T).(getl O (CHead c0 (Flat f) t) (CHead e (Bind b) v)))))) 
(\forall (d: C).((getl O (CHead c0 (Flat f) t) d) \to (\forall (P: Prop).P))) 
(\lambda (d: C).(\lambda (H2: (getl O (CHead c0 (Flat f) t) d)).(\lambda (P: 
Prop).(H1 d (getl_intro O c0 d c0 (drop_refl c0) (clear_gen_flat f c0 d t 
(getl_gen_O (CHead c0 (Flat f) t) d H2))) P)))))) H0)))) k) (\lambda (n: 
nat).(\lambda (_: (or (ex_3 C B T (\lambda (e: C).(\lambda (b: B).(\lambda 
(v: T).(getl n (CHead c0 k t) (CHead e (Bind b) v)))))) (\forall (d: 
C).((getl n (CHead c0 k t) d) \to (\forall (P: Prop).P))))).(let H_x \def (H 
(r k n)) in (let H1 \def H_x in (or_ind (ex_3 C B T (\lambda (e: C).(\lambda 
(b: B).(\lambda (v: T).(getl (r k n) c0 (CHead e (Bind b) v)))))) (\forall 
(d: C).((getl (r k n) c0 d) \to (\forall (P: Prop).P))) (or (ex_3 C B T 
(\lambda (e: C).(\lambda (b: B).(\lambda (v: T).(getl (S n) (CHead c0 k t) 
(CHead e (Bind b) v)))))) (\forall (d: C).((getl (S n) (CHead c0 k t) d) \to 
(\forall (P: Prop).P)))) (\lambda (H2: (ex_3 C B T (\lambda (e: C).(\lambda 
(b: B).(\lambda (v: T).(getl (r k n) c0 (CHead e (Bind b) v))))))).(ex_3_ind 
C B T (\lambda (e: C).(\lambda (b: B).(\lambda (v: T).(getl (r k n) c0 (CHead 
e (Bind b) v))))) (or (ex_3 C B T (\lambda (e: C).(\lambda (b: B).(\lambda 
(v: T).(getl (S n) (CHead c0 k t) (CHead e (Bind b) v)))))) (\forall (d: 
C).((getl (S n) (CHead c0 k t) d) \to (\forall (P: Prop).P)))) (\lambda (x0: 
C).(\lambda (x1: B).(\lambda (x2: T).(\lambda (H3: (getl (r k n) c0 (CHead x0 
(Bind x1) x2))).(or_introl (ex_3 C B T (\lambda (e: C).(\lambda (b: 
B).(\lambda (v: T).(getl (S n) (CHead c0 k t) (CHead e (Bind b) v)))))) 
(\forall (d: C).((getl (S n) (CHead c0 k t) d) \to (\forall (P: Prop).P))) 
(ex_3_intro C B T (\lambda (e: C).(\lambda (b: B).(\lambda (v: T).(getl (S n) 
(CHead c0 k t) (CHead e (Bind b) v))))) x0 x1 x2 (getl_head k n c0 (CHead x0 
(Bind x1) x2) H3 t))))))) H2)) (\lambda (H2: ((\forall (d: C).((getl (r k n) 
c0 d) \to (\forall (P: Prop).P))))).(or_intror (ex_3 C B T (\lambda (e: 
C).(\lambda (b: B).(\lambda (v: T).(getl (S n) (CHead c0 k t) (CHead e (Bind 
b) v)))))) (\forall (d: C).((getl (S n) (CHead c0 k t) d) \to (\forall (P: 
Prop).P))) (\lambda (d: C).(\lambda (H3: (getl (S n) (CHead c0 k t) 
d)).(\lambda (P: Prop).(H2 d (getl_gen_S k c0 d t n H3) P)))))) H1))))) 
i)))))) c).
(* COMMENTS
Initial nodes: 1563
END *)

