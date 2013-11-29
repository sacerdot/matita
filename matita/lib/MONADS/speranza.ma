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

include "basics/types.ma".
include "arithmetics/nat.ma".
include "basics/lists/list.ma".

inductive t : Type[0] ≝
   leaf: nat → t
 | node: t → t → t.

definition path ≝ list bool.

definition tp ≝ t × path.

let rec setleaf_fun (v:nat) (x:t) (p:path) on p : t × bool ≝
 match p with
 [ nil ⇒
    match x with
    [ leaf _ ⇒ 〈leaf v,true〉
    | node x1 x2 ⇒ 〈node x1 x2,false〉 ]
 | cons b tl ⇒
    match x with
    [ leaf n ⇒ 〈leaf n,false〉
    | node x1 x2 ⇒
       if b then
        let 〈x2',res〉 ≝ setleaf_fun v x2 tl in
         〈node x1 x2', res〉
       else
        let 〈x1',res〉 ≝ setleaf_fun v x1 tl in
         〈node x1' x2, res〉 ]].

let rec admissible (x:t) (p:path) on p : bool ≝
 match p with
 [ nil ⇒ true
 | cons b tl ⇒
    match x with
    [ leaf _ ⇒ false
    | node x1 x2 ⇒
       if b then admissible x2 tl else admissible x1 tl ]].

definition left: ∀A:Type[0]. (bool → tp → A) → tp → A ≝
 λA,k,x.
  let 〈t,p〉 ≝ x in
  let p' ≝ false::p in
   k (admissible t p') 〈t,p'〉.

definition right: ∀A:Type[0]. (bool → tp → A) → tp → A ≝
 λA,k,x.
  let 〈t,p〉 ≝ x in
  let p' ≝ true::p in
   k (admissible t p') 〈t,p'〉.

definition reset: ∀A:Type[0]. (tp → A) → tp → A ≝
 λA,k,x.
  let 〈t,p〉 ≝ x in
   k 〈t,nil …〉.

definition setleaf: ∀A:Type[0]. nat → (bool → tp → A) → tp → A ≝
 λA,v,k,x.
  let 〈t,p〉 ≝ x in
  let 〈t',res〉 ≝ setleaf_fun v t p in
   k res 〈t',p〉.

(*****************************)

let rec update (A:Type[0]) (v:nat) (k: bool → tp → A) (p:path) on p:
 tp → A
≝
 match p with
 [ nil ⇒ setleaf … v (λres. reset … (k res))
 | cons b tl ⇒
    if b then
     right … (λres1.update … v (λres2. k (res1 ∧ res2)) tl)
    else
     left … (λres1. update … v (λres2.k (res1 ∧ res2)) tl) ].

definition example ≝
 node (node (leaf 0) (leaf 1)) (node (leaf 2) (leaf 3)).

lemma test: update ? 5 (λres,x. 〈res,x〉) [false;false] 〈example,nil …〉 = ?.
 normalize //
qed.