(**************************************************************************)
(*       ___                                                              *)
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

(* $Id: CSetoidFun.v,v 1.12 2004/09/22 11:06:10 loeb Exp $ *)

set "baseuri" "cic:/matita/algebra/CoRN/SetoidFun".
include "algebra/CoRN/Setoids.ma".


definition ap_fun : \forall A,B : CSetoid. \forall f,g : CSetoid_fun A B. Prop \def
\lambda A,B : CSetoid. \lambda f,g : CSetoid_fun A B.
 \exists a:A. (csf_fun A B f) a \neq (csf_fun A B g) a.
(* Definition ap_fun (A B : CSetoid) (f g : CSetoid_fun A B) :=
  {a : A | f a[#]g a}. *)

definition eq_fun : \forall A,B : CSetoid. \forall f,g : CSetoid_fun A B. Prop \def
\lambda A,B : CSetoid. \lambda f,g : CSetoid_fun A B.
 \forall a:A. (csf_fun A B f) a = (csf_fun A B g) a.
(* Definition eq_fun (A B : CSetoid) (f g : CSetoid_fun A B) :=
  forall a : A, f a[=]g a. *)   
  
lemma irrefl_apfun : \forall A,B : CSetoid. 
 irreflexive (CSetoid_fun A B) (ap_fun A B).
intros.
unfold irreflexive. intro f.
unfold ap_fun.
unfold.
intro.
elim H.
cut (csf_fun A B f a = csf_fun A B f a)
[ 
 apply eq_imp_not_ap.
 apply A.
 assumption. 
 assumption.
 auto. 
 auto 
|
 apply eq_reflexive_unfolded 
]
qed.

(*
Lemma irrefl_apfun : forall A B : CSetoid, irreflexive (ap_fun A B).
intros A B.
unfold irreflexive in |- *.
intros f.
unfold ap_fun in |- *.
red in |- *.
intro H.
elim H.
intros a H0.
set (H1 := ap_irreflexive_unfolded B (f a)) in *.
intuition.
Qed.
*)


(*
lemma cotrans_apfun : \forall A,B : CSetoid. cotransitive (CSetoid_fun A B) (ap_fun A B).
intros (A B).
unfold.
unfold ap_fun.
intros (f g H h).
decompose.
apply ap_cotransitive.
apply (ap_imp_neq B (csf_fun A B x a) (csf_fun A B y a) H1).
(* letin foo \def (\exist a:A.csf_fun A B x a\neq csf_fun A B z a). *)


apply (ap_cotransitive B ? ? H1 ?).

split.
left.
elim H.
clear H.
intros a H.
set (H1 := ap_cotransitive B (f a) (g a) H (h a)) in *.
elim H1.
clear H1.
intros H1.
left.
exists a.
exact H1.

clear H1.
intro H1.
right.
exists a.
exact H1.
Qed.
*)

(*
Lemma cotrans_apfun : forall A B : CSetoid, cotransitive (ap_fun A B).
intros A B.
unfold cotransitive in |- *.
unfold ap_fun in |- *.
intros f g H h.
elim H.
clear H.
intros a H.
set (H1 := ap_cotransitive B (f a) (g a) H (h a)) in *.
elim H1.
clear H1.
intros H1.
left.
exists a.
exact H1.

clear H1.
intro H1.
right.
exists a.
exact H1.
Qed.
*)

lemma ta_apfun : \forall A, B : CSetoid. tight_apart (CSetoid_fun A B) (eq_fun A B) (ap_fun A B).
unfold tight_apart.
intros (A B f g).
unfold ap_fun.
unfold eq_fun.
split
[ intros. 
  apply not_ap_imp_eq.unfold.intro.auto.
 |intros. unfold.intro.elim H1.
  apply (ap_imp_neq B ? ? H2). auto.
]
qed.

