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

include "datatypes/bool.ma".
include "nat/nat.ma".

inductive Z : Set \def
  OZ : Z
| pos : nat \to Z
| neg : nat \to Z.

interpretation "Integers" 'Z = Z.

definition Z_of_nat \def
\lambda n. match n with
[ O \Rightarrow  OZ 
| (S n)\Rightarrow  pos n].

coercion Z_of_nat.

definition neg_Z_of_nat \def
\lambda n. match n with
[ O \Rightarrow  OZ 
| (S n)\Rightarrow  neg n].

lemma pos_n_eq_S_n : \forall n : nat.
  (pos n) = (S n).
intro.reflexivity. 
qed.

definition abs \def
\lambda z.
 match z with 
[ OZ \Rightarrow O
| (pos n) \Rightarrow (S n)
| (neg n) \Rightarrow (S n)].

definition OZ_test \def
\lambda z.
match z with 
[ OZ \Rightarrow true
| (pos n) \Rightarrow false
| (neg n) \Rightarrow false].

theorem OZ_test_to_Prop :\forall z:Z.
match OZ_test z with
[true \Rightarrow z=OZ 
|false \Rightarrow z \neq OZ].
intros.elim z.
simplify.reflexivity.
simplify. unfold Not. intros (H).
destruct H.
simplify. unfold Not. intros (H).
destruct H.
qed.

(* discrimination *)
theorem injective_pos: injective nat Z pos.
unfold injective.
intros.
apply inj_S.
change with (abs (pos x) = abs (pos y)).
apply eq_f.assumption.
qed.

variant inj_pos : \forall n,m:nat. pos n = pos m \to n = m
\def injective_pos.

theorem injective_neg: injective nat Z neg.
unfold injective.
intros.
apply inj_S.
change with (abs (neg x) = abs (neg y)).
apply eq_f.assumption.
qed.

variant inj_neg : \forall n,m:nat. neg n = neg m \to n = m
\def injective_neg.

theorem not_eq_OZ_pos: \forall n:nat. OZ \neq pos n.
unfold Not.intros (n H).
destruct H.
qed.

theorem not_eq_OZ_neg :\forall n:nat. OZ \neq neg n.
unfold Not.intros (n H).
destruct H.
qed.

theorem not_eq_pos_neg :\forall n,m:nat. pos n \neq neg m.
unfold Not.intros (n m H).
destruct H.
qed.

theorem decidable_eq_Z : \forall x,y:Z. decidable (x=y).
intros.unfold decidable.
elim x.
(* goal: x=OZ *)
  elim y.
  (* goal: x=OZ y=OZ *)
    left.reflexivity.
  (* goal: x=OZ 2=2 *)
    right.apply not_eq_OZ_pos.
  (* goal: x=OZ 2=3 *)
    right.apply not_eq_OZ_neg.
(* goal: x=pos *)
  elim y.
  (* goal: x=pos y=OZ *)
    right.unfold Not.intro.
    apply (not_eq_OZ_pos n). symmetry. assumption.
  (* goal: x=pos y=pos *)
    elim (decidable_eq_nat n n1:((n=n1) \lor ((n=n1) \to False))).
    left.apply eq_f.assumption.
    right.unfold Not.intros (H_inj).apply H. destruct H_inj. reflexivity.
  (* goal: x=pos y=neg *)
    right.unfold Not.intro.apply (not_eq_pos_neg n n1). assumption.
(* goal: x=neg *)
  elim y.
  (* goal: x=neg y=OZ *)
    right.unfold Not.intro.
    apply (not_eq_OZ_neg n). symmetry. assumption.
  (* goal: x=neg y=pos *)
    right. unfold Not.intro. apply (not_eq_pos_neg n1 n). symmetry. assumption.
  (* goal: x=neg y=neg *)
    elim (decidable_eq_nat n n1:((n=n1) \lor ((n=n1) \to False))).
    left.apply eq_f.assumption.
    right.unfold Not.intro.apply H.apply injective_neg.assumption.
qed.

(* end discrimination *)

definition Zsucc \def
\lambda z. match z with
[ OZ \Rightarrow pos O
| (pos n) \Rightarrow pos (S n)
| (neg n) \Rightarrow 
	  match n with
	  [ O \Rightarrow OZ
	  | (S p) \Rightarrow neg p]].

definition Zpred \def
\lambda z. match z with
[ OZ \Rightarrow neg O
| (pos n) \Rightarrow 
	  match n with
	  [ O \Rightarrow OZ
	  | (S p) \Rightarrow pos p]
| (neg n) \Rightarrow neg (S n)].

theorem Zpred_Zsucc: \forall z:Z. Zpred (Zsucc z) = z.
intros.
elim z.
  reflexivity.
  reflexivity.
  elim n.
    reflexivity.
    reflexivity.
qed.

theorem Zsucc_Zpred: \forall z:Z. Zsucc (Zpred z) = z.
intros.
elim z.
  reflexivity.
  elim n.
    reflexivity.
    reflexivity.
  reflexivity.
qed.

