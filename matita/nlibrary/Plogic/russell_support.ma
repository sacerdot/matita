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

include "Plogic/jmeq.ma".
include "logic/connectives.ma".
include "datatypes/sums.ma".

include "Plogic/connectives.ma".

(* experimental: Russell support *)

alias id "False" = "cic:/matita/ng/Plogic/connectives/False.ind(1,0,0)".

ndefinition P_to_P_option : ∀A:Type[0].∀P:A → CProp[0].option A → CProp[0] ≝
  λA,P,a.match a with [ None ⇒ False | Some y ⇒ P y ].

ndefinition subset : ∀A:Type[0].(A → CProp[0]) → Type[0] ≝
  λA,P.Σx.P_to_P_option A P x.

notation < "hvbox({ ident i : s | term 19 p })" with precedence 90
for @{ 'subset_spec $s (\lambda ${ident i} : $nonexistent . $p)}.

notation > "hvbox({ ident i : s | term 19 p })" with precedence 90
for @{ 'subset_spec $s (\lambda ${ident i}. $p)}.

(*
 * the advantage is that we can use None to mean that some branch of the 
 * function we are defining will never be reached
 * for all other purposes, they are the same as sigma types
 *
 * TODO: add on-the-fly rewriting for dependent types
 *)
interpretation "russell-style subset specification" 'subset_spec s p = (subset s p).

ndefinition inject : ∀A.∀P:A → CProp[0].∀a.∀p:P_to_P_option ? P a.{ x : A | P x } ≝ 
  λA.λP:A → CProp[0].λa:option A.λp:P_to_P_option ? P a. 
  sig_intro (option A) (P_to_P_option A P) a p.
ndefinition eject : ∀A.∀P: A → CProp[0].{ x : A | P x } → A ≝ 
  λA,P,c.match c with [ sig_intro w p ⇒ ?].
ngeneralize in match p;ncases w;nnormalize
##[*
##|#x;#_;napply x ##]
nqed.

ncoercion inject : 
  ∀A.∀P:A → CProp[0].∀a.∀p:P_to_P_option ? P a.subset ? (λx.P x) ≝ inject 
  on a:option ? to subset ? ?.
ncoercion eject : ∀A.∀P:A → CProp[0].∀c:subset ? P.A ≝ eject 
  on _c:subset ? ? to ?.

(*
(* tests...*)

include "datatypes/list.ma".

ndefinition head : ∀l.l ≠ [] → { x : nat | ∃l2.l = x::l2 } ≝
 λl,p.match l with 
  [ nil ⇒ None ?
  | cons x tl ⇒ Some ? x ].nnormalize;
##[ncases p;/3/
##|/2/ 
##]
nqed.

ninductive vec : nat → Type[0] ≝ 
| vnil : vec O
| vcons : ∀n:nat.nat → vec n → vec (S n).

ndefinition vtail : 
  ∀n.∀v:vec (S n). { w : vec (pred (S n)) | ∃m:nat.v ≃ vcons ? m w } ≝ 
λn,v.match v with
     [ vnil ⇒ None (vec (pred O))
     | vcons p hd tl ⇒ Some (vec (pred (S p))) tl ].
nnormalize;ndestruct;/2/;
nqed.*)