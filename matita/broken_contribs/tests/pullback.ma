
(*
axiom A : Type.
axiom B : Type.
axiom B1 : Type.
axiom C : Type.

axiom f1 : A → B.
axiom f2 : A → B1.
axiom f3 : B → C.
axiom f4 : B1 → C.

coercion f1.
coercion f2.
coercion f3.
coercion f4.




axiom P : Prop.

lemma x : P.
*)

include "logic/equality.ma".

record L : Type \def {
  l_c : Prop;
  l_op : l_c \to l_c \to l_c
}.

record R : Type \def {
  r_c : Prop;
  r_op : r_c \to r_c \to r_c
}.

record LR_ : Type \def {
  lr_L : L ;
  lr_R_ : R ;
  lr_w : r_c lr_R_ = l_c lr_L
}.

lemma lr_R : LR_ \to R.
intros;constructor 1;
[apply rule (l_c (lr_L l))
|rewrite < (lr_w l);apply (r_op (lr_R_ l));]
qed.

(*
axiom F : Prop → Prop.
axiom C : Prop → Prop. 

axiom daemon : ∀x.F x = C x.

lemma xxx : ∀x.F x = C x. apply daemon; qed.

axiom yyyy : ∀x.C (C x) = C (C x) → F (F x) = F (F x).

coercion yyyy. 

lemma x : ∀x. (λy:F (F x) = F (F x).True) (refl_eq ? (C (C x))).

include "nat/factorial.ma".
lemma xxx : 8! = 8 * 7!. intros; reflexivity; qed.

lemma x : (λy:8!=8!.True) (refl_eq ? (8 * 7!)).
apply (refl_eq ??);
*)

(*
lemma xxx : \forall x. r_c (lr_R x) = l_c (lr_L x).
intros; reflexivity;
qed.
*)



definition Prop_OR_LR_1 : LR_ → Prop.
apply (λx.r_c (lr_R x)).
qed.

(*
coercion Prop_OR_LR_1.
coercion lr_R.
*)

unification hint (\forall x. r_c (lr_R x) = l_c (lr_L x)).

lemma foo : \forall x,y.l_op ? x (r_op ? x y) = x.

r_c ?1 =?= l_c ?2


r_c (lr_R ?3) === l_c (lr_L ?3)
r_c (lr_R ?) === l_c (lr_L ?)   |---->   
   \forall x. r_c (lr_R x) === l_c (lr_L x)


inductive T : Type \def t : T.
inductive L : Type \def l : L.
inductive R : Type \def r : R.
inductive R1 : Type \def r1 : R1.
inductive P1 : Type \def p1 : P1.
inductive P2 : Type \def p2 : P2.

definition L_to_T : L \to T \def \lambda x.t.
definition R_to_T : R \to T \def \lambda x.t.
definition P1_to_L : P1 \to L \def \lambda x.l.
definition P1_to_R1 : P1 \to R1 \def \lambda x.r1.
definition R1_to_P2 : R1 \to P2 \def \lambda x.p2.
definition R1_to_R : R1 \to R \def \lambda x.r.
definition P2_to_L : P2 \to L \def \lambda x.l.
definition P2_to_R : P2 \to R \def \lambda x.r.
definition P1_to_P1 : P1 \to P1 \def \lambda x.p1.

coercion cic:/matita/tests/pullback/L_to_T.con.
coercion cic:/matita/tests/pullback/R_to_T.con.
coercion cic:/matita/tests/pullback/P1_to_L.con.
coercion cic:/matita/tests/pullback/P1_to_R1.con.
coercion cic:/matita/tests/pullback/R1_to_R.con.
coercion cic:/matita/tests/pullback/R1_to_P2.con.
coercion cic:/matita/tests/pullback/P2_to_L.con.
coercion cic:/matita/tests/pullback/P2_to_R.con.
coercion cic:/matita/tests/pullback/P1_to_P1.con.
