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

include "ground_2/notation/functions/cocompose_2.ma".
include "ground_2/relocation/rtmap_coafter.ma".

(* RELOCATION N-STREAM ******************************************************)

rec definition fun0 (n1:nat) on n1: rtmap → nat.
* * [ | #n2 #f2 @0 ]
#f2 cases n1 -n1 [ @0 ]
#n1 @(↑(fun0 n1 f2))
defined.

rec definition fun2 (n1:nat) on n1: rtmap → rtmap.
* * [ | #n2 #f2 @(n2@f2) ]
#f2 cases n1 -n1 [ @f2 ]
#n1 @(fun2 n1 f2)
defined.

rec definition fun1 (n1:nat) (f1:rtmap) on n1: rtmap → rtmap.
* * [ | #n2 #f2 @(n1@f1) ]
#f2 cases n1 -n1 [ @f1 ]
#n1 @(fun1 n1 f1 f2)
defined.

corec definition cocompose: rtmap → rtmap → rtmap.
#f2 * #n1 #f1 @(seq … (fun0 n1 f2)) @(cocompose (fun2 n1 f2) (fun1 n1 f1 f2))
defined.

interpretation "functional co-composition (nstream)"
   'CoCompose f1 f2 = (cocompose f1 f2).

(* Basic properties on funs *************************************************)

(* Note: we need theese since matita blocks recursive δ when ι is blocked *)  
lemma fun0_xn: ∀f2,n1. 0 = fun0 n1 (↑f2).
* #n2 #f2 * //
qed.

lemma fun2_xn: ∀f2,n1. f2 = fun2 n1 (↑f2).
* #n2 #f2 * //
qed.

lemma fun1_xxn: ∀f2,f1,n1. fun1 n1 f1 (↑f2) = n1@f1.
* #n2 #f2 #f1 * //
qed.

(* Basic properies on cocompose *********************************************)

lemma cocompose_rew: ∀f2,f1,n1. (fun0 n1 f2)@(fun2 n1 f2)~∘(fun1 n1 f1 f2) = f2 ~∘ (n1@f1).
#f2 #f1 #n1 <(stream_rew … (f2~∘(n1@f1))) normalize //
qed.

(* Basic inversion lemmas on compose ****************************************)

lemma cocompose_inv_ppx: ∀f2,f1,f,x. (⫯f2) ~∘ (⫯f1) = x@f →
                         0 = x ∧ f2 ~∘ f1 = f.
#f2 #f1 #f #x
<cocompose_rew #H destruct
normalize /2 width=1 by conj/
qed-.

lemma cocompose_inv_pnx: ∀f2,f1,f,n1,x. (⫯f2) ~∘ ((↑n1)@f1) = x@f →
                         ∃∃n. ↑n = x & f2 ~∘ (n1@f1) = n@f.
#f2 #f1 #f #n1 #x
<cocompose_rew #H destruct
@(ex2_intro … (fun0 n1 f2)) // <cocompose_rew
/3 width=1 by eq_f2/
qed-.

lemma cocompose_inv_nxx: ∀f2,f1,f,n1,x. (↑f2) ~∘ (n1@f1) = x@f →
                         0 = x ∧ f2 ~∘ (n1@f1) = f.
#f2 #f1 #f #n1 #x
<cocompose_rew #H destruct
/2 width=1 by conj/
qed-.

(* Specific properties on coafter *******************************************)

corec lemma coafter_total_aux: ∀f2,f1,f. f2 ~∘ f1 = f → f2 ~⊚ f1 ≘ f.
* #n2 #f2 * #n1 #f1 * #n #f cases n2 -n2
[ cases n1 -n1
  [ #H cases (cocompose_inv_ppx … H) -H /3 width=7 by coafter_refl, eq_f2/
  | #n1 #H cases (cocompose_inv_pnx … H) -H /3 width=7 by coafter_push/
  ]
| #n2 >next_rew #H cases (cocompose_inv_nxx … H) -H /3 width=5 by coafter_next/
]
qed-.

theorem coafter_total: ∀f2,f1. f2 ~⊚ f1 ≘ f2 ~∘ f1.
/2 width=1 by coafter_total_aux/ qed.
