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

lemma in_list_nil : \forall A,x.\lnot (in_list A x []).
intros.unfold.intro.inversion H
  [intros;lapply (sym_eq ? ? ? H2);absurd (a::l = [])
     [assumption|apply nil_cons]
  |intros;lapply (sym_eq ? ? ? H4);absurd (a1::l = [])
     [assumption|apply nil_cons]]
qed.

lemma max_case : \forall m,n.(max m n) = match (leb m n) with
      [ false \Rightarrow n
      | true \Rightarrow m ].
intros;elim m;simplify;reflexivity;
qed.