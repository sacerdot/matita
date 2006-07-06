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

set "baseuri" "cic:/matita/paramodulation/".

include "nat/nat.ma".
include "datatypes/bool.ma".

inductive List (U:Type) : nat \to Type \def
  | Nil : List U O
  | Cons : \forall n.U \to List U n \to List U (S n).

(*  
definition mk_T \def \lambda U:Type.\lambda n:nat.List U n \to Prop.

definition app_T' \def 
  \lambda n:nat.
  \lambda U:Type.
  \lambda a:U.
  \lambda t:mk_T U (S n).
  \lambda l:List U n.t (Cons U n a l).
    
let rec mk_Arrow' (n:nat) (U:Type) on n \def
  match n return \lambda x.\forall t:mk_T U x.Prop with 
  [ O ⇒ 
     \lambda t:mk_T U O.t (Nil U)
  | (S m) ⇒ 
     \lambda t:mk_T U (S m).\forall a.mk_Arrow' m U (app_T' m U a t)].

theorem leaf':
  \forall U:Type.
  \forall n:nat.
  \forall actual_params:List U n.
  \forall pred:mk_T U n.
  \forall H:mk_Arrow' n U pred.
  pred actual_params.
  intros 3.
  elim actual_params; 
    [ exact H.
    | simplify in H1.
      unfold app_T' in H1.
      lapply (H1 t).
      apply H.
      assumption
    ]   
qed.
*)
  
definition mk_Tside \def \lambda U:Type.\lambda n:nat.List U n \to U.

definition app_T \def 
  \lambda n:nat.
  \lambda U:Type.
  \lambda a:U.
  \lambda side:mk_Tside U (S n).
  \lambda args:List U n.side (Cons U n a args).
     
let rec mk_Arrow (n:nat) (U:Type) (eq:\forall T:Type.T\to T\to Prop) on n \def
  match n return \lambda x.\forall l:mk_Tside U x.\forall r:mk_Tside U x.Prop with 
  [ O ⇒ 
     \lambda l:mk_Tside U O.\lambda r:mk_Tside U O.eq U (l (Nil U)) (r (Nil U))
  | (S m) ⇒ 
     \lambda l:mk_Tside U (S m).\lambda r:mk_Tside U (S m).\forall a.
       mk_Arrow m U eq (app_T m U a l) (app_T m U a r)].    

definition sym \def
  \lambda eq:\forall T:Type.T\to T\to Prop.
  \lambda U:Type.
  \lambda l,r:U.
  \lambda b:bool.
  match b with 
  [ true ⇒ eq U r l
  | false ⇒ eq U l r].

let rec mk_TsideArr (n:nat) (U:Type) on n \def
  match n with 
  [ O ⇒ U
  | (S m) ⇒  U \to mk_TsideArr m U].

let rec mk_Statement 
  (n:nat) (U:Type) (eq:\forall T:Type.T\to T\to Prop) (b:bool) 
  (context:U \to U) on n  
\def
  match n return \lambda x.\forall l:mk_TsideArr x U.\forall r:mk_TsideArr x U.Prop with 
  [ O ⇒ 
     \lambda predl:mk_TsideArr O U.
     \lambda predr:mk_TsideArr O U.
       sym eq U (context predl) (context predr) b
  | (S m) ⇒ 
     \lambda predl:mk_TsideArr (S m) U.\lambda predr:mk_TsideArr (S m) U.
     \forall a:U.
       mk_Statement m U eq b context (predl a) (predr a)].    

theorem eq_f_to_mk_Statement:
  \forall eq:\forall T:Type.T\to T\to Prop.
  \forall sym_eq: \forall T:Type.\forall l,r:T.eq T l r \to eq T r l.
  \forall eq_f :
    \forall U,U1:Type.
    \forall f:U \to U1.\forall x,y:U. eq U x y \to eq U1 (f x) (f y).
  \forall b:bool.
  \forall U:Type.
  \forall context: U \to U.
  \forall n:nat.
  \forall predl:mk_TsideArr n U.
  \forall predr:mk_TsideArr n U.
  \forall H:mk_Statement n U eq false (\lambda x.x) predl predr.
  mk_Statement n U eq b context predl predr.
  intros 7.
  elim n;
  [ simplify in H2.
    elim b;
    [ simplify.
      apply H1.
      apply H.
      assumption.
    | simplify.
      apply H1.
      assumption.
    ]  
  | generalize in match H2.
    clear H2.
    elim b;
    [ simplify.
      intro.
      apply H2.
      simplify in H3.
      apply H3.
    | simplify.
      intro.
      apply H2.
      simplify in H3.
      apply H3.
    ]
  ]
qed.

variant rewrite : 
  \forall eq:\forall T:Type.T\to T\to Prop.
  \forall sym_eq: \forall T:Type.\forall l,r:T.eq T l r \to eq T r l.
  \forall eq_f :
    \forall U,U1:Type.
    \forall f:U \to U1.\forall x,y:U. eq U x y \to eq U1 (f x) (f y).
  \forall b:bool.
  \forall U:Type.
  \forall context: U \to U.
  \forall n:nat.
  \forall predl:mk_TsideArr n U.
  \forall predr:mk_TsideArr n U.
  \forall H:mk_Statement n U eq false (\lambda x.x) predl predr.
  mk_Statement n U eq b context predl predr
\def 
  eq_f_to_mk_Statement.

(*

definition make_eqs_smart' \def 
  \lambda Univ:Type.
  \lambda length:nat.
  \lambda initial:Univ.
  let rec aux (p:Univ) (n:nat) on n : Prop \def
    match n with
    [ O \Rightarrow \forall a:Univ. p = a \to initial = a   
    | (S n) \Rightarrow \forall a:Univ. p = a \to aux a n
    ]
  in 
    aux initial length.
  
theorem transl_smart' : 
  \forall Univ:Type.\forall n:nat.\forall initial:Univ.
    make_eqs_smart' Univ n initial.
  intros.
  unfold make_eqs_smart'.
  elim n
  [ simplify.intros.assumption
  | simplify.intros.rewrite < H1.assumption
  ]
qed.  

theorem prova':
  \forall Univ:Type.
  \forall a,b:Univ.
  \forall plus: Univ \to Univ \to Univ.
  \forall H:\forall x,y:Univ.plus x y = plus y x.
  \forall H1:plus b a = plus b b.
  plus a b = plus b b.
  intros.
  apply (transl_smart' ? (S O) ? ? (H a b) ? H1).
qed. 
  
*)