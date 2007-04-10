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

set "baseuri" "cic:/matita/Fsub/util".
include "logic/equality.ma".
include "nat/compare.ma".
include "list/list.ma".

(*** useful definitions and lemmas not really related to Fsub ***)

lemma eqb_case : \forall x,y.(eqb x y) = true \lor (eqb x y) = false.
intros;elim (eqb x y);auto;
qed.
       
lemma eq_eqb_case : \forall x,y.((x = y) \land (eqb x y) = true) \lor
                                ((x \neq y) \land (eqb x y) = false).
intros;lapply (eqb_to_Prop x y);elim (eqb_case x y)
  [rewrite > H in Hletin;simplify in Hletin;left;auto
  |rewrite > H in Hletin;simplify in Hletin;right;auto]
qed.

let rec max m n \def
  match (leb m n) with
     [true \Rightarrow n
     |false \Rightarrow m]. 

inductive in_list (A : Type) : A \to (list A) \to Prop \def
  | in_Base : \forall x:A.\forall l:(list A).
              (in_list A x (x :: l))
  | in_Skip : \forall x,y:A.\forall l:(list A).
              (in_list A x l) \to (in_list A x (y :: l)).

definition incl : \forall A.(list A) \to (list A) \to Prop \def
  \lambda A,l,m.\forall x.(in_list A x l) \to (in_list A x m).               
              
(* FIXME: use the map in library/list (when there will be one) *)
definition map : \forall A,B,f.((list A) \to (list B)) \def
  \lambda A,B,f.let rec map (l : (list A)) : (list B) \def
    match l in list return \lambda l0:(list A).(list B) with
      [nil \Rightarrow (nil B)
      |(cons (a:A) (t:(list A))) \Rightarrow 
        (cons B (f a) (map t))] in map.

definition swap : nat \to nat \to nat \to nat \def
  \lambda u,v,x.match (eqb x u) with
    [true \Rightarrow v
    |false \Rightarrow match (eqb x v) with
       [true \Rightarrow u
       |false \Rightarrow x]].

lemma in_list_nil : \forall A,x.\lnot (in_list A x []).
intros.unfold.intro.inversion H
  [intros;lapply (sym_eq ? ? ? H2);absurd (a::l = [])
     [assumption|apply nil_cons]
  |intros;lapply (sym_eq ? ? ? H4);absurd (a1::l = [])
     [assumption|apply nil_cons]]
qed.

lemma notin_cons : \forall A,x,y,l.\lnot (in_list A x (y::l)) \to
                      (y \neq x) \land \lnot (in_list A x l).
intros.split
  [unfold;intro;apply H;rewrite > H1;constructor 1
  |unfold;intro;apply H;constructor 2;assumption]
qed.

lemma swap_left : \forall x,y.(swap x y x) = y.
intros;unfold swap;rewrite > eqb_n_n;simplify;reflexivity;
qed.

lemma swap_right : \forall x,y.(swap x y y) = x.
intros;unfold swap;elim (eq_eqb_case y x)
  [elim H;rewrite > H2;simplify;rewrite > H1;reflexivity
  |elim H;rewrite > H2;simplify;rewrite > eqb_n_n;simplify;reflexivity]
qed.

lemma swap_other : \forall x,y,z.(z \neq x) \to (z \neq y) \to (swap x y z) = z.
intros;unfold swap;elim (eq_eqb_case z x)
  [elim H2;lapply (H H3);elim Hletin
  |elim H2;rewrite > H4;simplify;elim (eq_eqb_case z y)
     [elim H5;lapply (H1 H6);elim Hletin
     |elim H5;rewrite > H7;simplify;reflexivity]]
qed. 

lemma swap_inv : \forall u,v,x.(swap u v (swap u v x)) = x.
intros;unfold in match (swap u v x);elim (eq_eqb_case x u)
  [elim H;rewrite > H2;simplify;rewrite > H1;apply swap_right
  |elim H;rewrite > H2;simplify;elim (eq_eqb_case x v)
     [elim H3;rewrite > H5;simplify;rewrite > H4;apply swap_left
     |elim H3;rewrite > H5;simplify;apply (swap_other ? ? ? H1 H4)]]
qed.

lemma swap_inj : \forall u,v,x,y.(swap u v x) = (swap u v y) \to x = y.
intros;unfold swap in H;elim (eq_eqb_case x u)
  [elim H1;elim (eq_eqb_case y u)
     [elim H4;rewrite > H5;assumption
     |elim H4;rewrite > H3 in H;rewrite > H6 in H;simplify in H;
      elim (eq_eqb_case y v)
        [elim H7;rewrite > H9 in H;simplify in H;rewrite > H in H8;
         lapply (H5 H8);elim Hletin
        |elim H7;rewrite > H9 in H;simplify in H;elim H8;symmetry;assumption]]
  |elim H1;elim (eq_eqb_case y u)
     [elim H4;rewrite > H3 in H;rewrite > H6 in H;simplify in H;
      elim (eq_eqb_case x v)
        [elim H7;rewrite > H9 in H;simplify in H;rewrite < H in H8;
         elim H2;assumption
        |elim H7;rewrite > H9 in H;simplify in H;elim H8;assumption]
     |elim H4;rewrite > H3 in H;rewrite > H6 in H;simplify in H;
      elim (eq_eqb_case x v)
        [elim H7;rewrite > H9 in H;elim (eq_eqb_case y v)
           [elim H10;rewrite > H11;assumption
           |elim H10;rewrite > H12 in H;simplify in H;elim H5;symmetry;
            assumption]
        |elim H7;rewrite > H9 in H;elim (eq_eqb_case y v)
           [elim H10;rewrite > H12 in H;simplify in H;elim H2;assumption
           |elim H10;rewrite > H12 in H;simplify in H;assumption]]]]
qed.

lemma max_case : \forall m,n.(max m n) = match (leb m n) with
      [ false \Rightarrow n
      | true \Rightarrow m ].
intros;elim m;simplify;reflexivity;
qed. 