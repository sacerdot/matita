(**************************************************************************)
(*       ___	                                                            *)
(*      ||M||                                                             *)
(*      ||A||       A project by Andrea Asperti                           *)
(*      ||T||                                                             *)
(*      ||I||       Developers:                                           *)
(*      ||T||       A.Asperti, C.Sacerdoti Coen,                          *)
(*      ||A||       E.Tassi, S.Zacchiroli                                 *)
(*      \   /                                                             *)
(*       \ /        This file is distributed under the terms of the       *)
(*        v         GNU Lesser General Public License Version 2.1         *)
(*                                                                        *)
(**************************************************************************)

include "higher_order_defs/relations.ma".

inductive eq (A:Type) (x:A) : A \to Prop \def
    refl_eq : eq A x x.

interpretation "leibnitz's equality" 'eq t x y = (eq t x y).

interpretation "leibnitz's non-equality" 'neq t x y = (Not (eq t x y)).

theorem eq_rect':
 \forall A. \forall x:A. \forall P: \forall y:A. x=y \to Type.
  P ? (refl_eq ? x) \to \forall y:A. \forall p:x=y. P y p.
 intros.
 exact
  (match p1 return \lambda y. \lambda p.P y p with
    [refl_eq \Rightarrow p]).
qed.
 
variant reflexive_eq : \forall A:Type. reflexive A (eq A)
\def refl_eq.
(* simplify.intros.apply refl_eq. *)
    
theorem symmetric_eq: \forall A:Type. symmetric A (eq A).
unfold symmetric.intros.elim H. apply refl_eq.
qed.

variant sym_eq : \forall A:Type.\forall x,y:A. x=y  \to y=x
\def symmetric_eq.

theorem transitive_eq : \forall A:Type. transitive A (eq A).
unfold transitive.intros.elim H1.assumption.
qed.

variant trans_eq : \forall A:Type.\forall x,y,z:A. x=y  \to y=z \to x=z
\def transitive_eq.

theorem symmetric_not_eq: \forall A:Type. symmetric A (λx,y.x ≠ y).
unfold symmetric.simplify.intros.unfold.intro.apply H.apply sym_eq.assumption.
qed.

variant sym_neq: ∀A:Type.∀x,y.x ≠ y →y ≠ x
≝ symmetric_not_eq.

theorem eq_elim_r:
 \forall A:Type.\forall x:A. \forall P: A \to Prop.
   P x \to \forall y:A. y=x \to P y.
intros. elim (sym_eq ? ? ? H1).assumption.
qed.

theorem eq_elim_r':
 \forall A:Type.\forall x:A. \forall P: A \to Set.
   P x \to \forall y:A. y=x \to P y.
intros. elim (sym_eq ? ? ? H).assumption.
qed.

theorem eq_elim_r'':
 \forall A:Type.\forall x:A. \forall P: A \to Type.
   P x \to \forall y:A. y=x \to P y.
intros. elim (sym_eq ? ? ? H).assumption.
qed.

theorem eq_f: \forall  A,B:Type.\forall f:A\to B.
\forall x,y:A. x=y \to f x = f y.
intros.elim H.apply refl_eq.
qed.

theorem eq_f': \forall  A,B:Type.\forall f:A\to B.
\forall x,y:A. x=y \to f y = f x.
intros.elim H.apply refl_eq.
qed.

(*  *)
coercion sym_eq.
coercion eq_f.
(* *)

default "equality"
 cic:/matita/logic/equality/eq.ind
 cic:/matita/logic/equality/sym_eq.con
 cic:/matita/logic/equality/transitive_eq.con
 cic:/matita/logic/equality/eq_ind.con
 cic:/matita/logic/equality/eq_elim_r.con
 cic:/matita/logic/equality/eq_rec.con
 cic:/matita/logic/equality/eq_elim_r'.con
 cic:/matita/logic/equality/eq_rect.con
 cic:/matita/logic/equality/eq_elim_r''.con
 cic:/matita/logic/equality/eq_f.con
(* *)
 cic:/matita/logic/equality/eq_OF_eq.con.
(* *)
(*  
 cic:/matita/logic/equality/eq_f'.con. (* \x.sym (eq_f x) *)
 *)
 
theorem eq_f2: \forall  A,B,C:Type.\forall f:A\to B \to C.
\forall x1,x2:A. \forall y1,y2:B.
x1=x2 \to y1=y2 \to f x1 y1 = f x2 y2.
intros.elim H1.elim H.reflexivity.
qed.

definition comp \def
 \lambda A.
  \lambda x,y,y':A.
   \lambda eq1:x=y.
    \lambda eq2:x=y'.
     eq_ind ? ? (\lambda a.a=y') eq2 ? eq1.
     
lemma trans_sym_eq:
 \forall A.
  \forall x,y:A.
   \forall u:x=y.
    comp ? ? ? ? u u = refl_eq ? y.
 intros.
 apply (eq_rect' ? ? ? ? ? u).
 reflexivity.
qed.

definition nu \def
 \lambda A.
  \lambda H: \forall x,y:A. decidable (x=y).
   \lambda x,y. \lambda p:x=y.
     match H x y with
      [ (or_introl p') \Rightarrow p'
      | (or_intror K) \Rightarrow False_ind ? (K p) ].

theorem nu_constant:
 \forall A.
  \forall H: \forall x,y:A. decidable (x=y).
   \forall x,y:A.
    \forall u,v:x=y.
     nu ? H ? ? u = nu ? H ? ? v.
 intros.
 unfold nu.
 unfold decidable in H.
 apply (Or_ind' ? ? ? ? ? (H x y)); simplify.
  intro; reflexivity.
  intro; elim (q u).
qed.

definition nu_inv \def
 \lambda A.
  \lambda H: \forall x,y:A. decidable (x=y).
   \lambda x,y:A.
    \lambda v:x=y.
     comp ? ? ? ? (nu ? H ? ? (refl_eq ? x)) v.

theorem nu_left_inv:
 \forall A.
  \forall H: \forall x,y:A. decidable (x=y).
   \forall x,y:A.
    \forall u:x=y.
     nu_inv ? H ? ? (nu ? H ? ? u) = u.
 intros.
 apply (eq_rect' ? ? ? ? ? u).
 unfold nu_inv.
 apply trans_sym_eq.
qed.

theorem eq_to_eq_to_eq_p_q:
 \forall A. \forall x,y:A.
  (\forall x,y:A. decidable (x=y)) \to
   \forall p,q:x=y. p=q.
 intros.
 rewrite < (nu_left_inv ? H ? ? p).
 rewrite < (nu_left_inv ? H ? ? q).
 elim (nu_constant ? H ? ? q).
 reflexivity.
qed.

(*CSC: alternative proof that does not pollute the environment with
  technical lemmata. Unfortunately, it is a pain to do without proper
  support for let-ins.
theorem eq_to_eq_to_eq_p_q:
 \forall A. \forall x,y:A.
  (\forall x,y:A. decidable (x=y)) \to
   \forall p,q:x=y. p=q.
intros.
letin nu \def
 (\lambda x,y. \lambda p:x=y.
   match H x y with
    [ (or_introl p') \Rightarrow p'
    | (or_intror K) \Rightarrow False_ind ? (K p) ]).
cut
 (\forall q:x=y.
   eq_ind ? ? (\lambda z. z=y) (nu ? ? q) ? (nu ? ? (refl_eq ? x))
   = q).
focus 8.
 clear q; clear p.
 intro.
 apply (eq_rect' ? ? ? ? ? q);
 fold simplify (nu ? ? (refl_eq ? x)).
 generalize in match (nu ? ? (refl_eq ? x)); intro.
 apply
  (eq_rect' A x
   (\lambda y. \lambda u.
    eq_ind A x (\lambda a.a=y) u y u = refl_eq ? y)
   ? x H1).
 reflexivity.
unfocus.
rewrite < (Hcut p); fold simplify (nu ? ? p).
rewrite < (Hcut q); fold simplify (nu ? ? q).
apply (Or_ind' (x=x) (x \neq x)
 (\lambda p:decidable (x=x). eq_ind A x (\lambda z.z=y) (nu x y p) x
   ([\lambda H1.eq A x x]
    match p with
    [(or_introl p') \Rightarrow p'
    |(or_intror K) \Rightarrow False_ind (x=x) (K (refl_eq A x))]) =
   eq_ind A x (\lambda z.z=y) (nu x y q) x
    ([\lambda H1.eq A x x]
     match p with
    [(or_introl p') \Rightarrow p'
    |(or_intror K) \Rightarrow False_ind (x=x) (K (refl_eq A x))]))
 ? ? (H x x)).
intro; simplify; reflexivity.
intro q; elim (q (refl_eq ? x)).
qed.
*)

(*
theorem a:\forall x.x=x\land True.
[ 
2:intros;
  split;
  [
    exact (refl_eq Prop x);
  |
    exact I;
  ]
1:
  skip
]
qed.
*)

