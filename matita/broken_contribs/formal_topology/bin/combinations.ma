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

include "datatypes/bool.ma".
include "datatypes/constructors.ma".

inductive ct: Type ≝
   C: option mmt → ct
with mmt: Type ≝
   M: option ct → mmt
 | MM: option ct → mmt.

inductive t: Type ≝
   E: t
 | CT: ct → t
 | MMT: mmt → t.

(*
let rec ct_rect' (P1: ct → Type) (P2: mmt → Type) (f1: ∀w: mmt. P2 w → P1 (C w)) (f2: P1 E) (f3: ∀w: ct. P1 w → P2 (M1 w)) (f4: ∀w: ct. P1 w → P2 (M2 w)) (f5: P2 E') (w:ct) on w : P1 w ≝
 match w return λw. P1 w with
  [ C w' ⇒ f1 w' (mmt_rect' P1 P2 f1 f2 f3 f4 f5 w')
  | E ⇒ f2 ]
and mmt_rect' (P1: ct → Type) (P2: mmt → Type) (f1: ∀w: mmt. P2 w → P1 (C w)) (f2: P1 E) (f3: ∀w: ct. P1 w → P2 (M1 w)) (f4: ∀w: ct. P1 w → P2 (M2 w)) (f5: P2 E') (w:mmt) on w : P2 w ≝
 match w return λw. P2 w with
  [ M1 w' ⇒ f3 w' (ct_rect' P1 P2 f1 f2 f3 f4 f5 w')
  | M2 w' ⇒ f4 w' (ct_rect' P1 P2 f1 f2 f3 f4 f5 w')
  | E' ⇒ f5 ].
*)

definition c: t → t ≝
 λw.
  match w with
   [ E ⇒ CT (C (None ?))
   | CT _ ⇒ w
   | MMT w' ⇒ CT (C (Some ? w')) ].

definition m: t → t ≝
 λw.
  match w with
   [ E ⇒ MMT (M (None ?))
   | CT w' ⇒ MMT (M (Some ? w'))
   | MMT w' ⇒
      match w' with
       [ M w'' ⇒ MMT (MM w'')
       | MM w'' ⇒ MMT (M w'') ]].

definition i: t → t ≝ λw.w.

inductive leq: t → t → Prop ≝
   leq0: ∀w. leq w w
 | leq1: ∀w1,w2,w3. leq w1 w2 → leq w2 w3 → leq w1 w3
 | leq2: ∀w1,w2. leq w1 w2 → leq w1 (c w2)
 | leq3: ∀w1,w2. leq w1 w2 → leq (c (c w1)) (c w2)
 | leq4: ∀w1,w2. leq w1 w2 → leq (c w1) (c w2)
 | leq5: ∀w1,w2. leq w1 w2 → leq (m w2) (m (m (m w1)))
 | leq6: ∀w1,w2. leq w1 w2 → leq w1 (m (m w2))
 | leq7: ∀w1,w2. leq w1 w2 → leq (m w2) (m w1).

theorem ok: ∀w1,w2. leq w1 w2 → leq w2 w1 → w1 = w2.
 

inductive leq: t → t → Prop ≝
   leq1: leq E (MMT (MM (None ?)))
 | leq2: leq E (CT (C (None ?)))
 | leq3: ∀w. leq (MMT w) (CT (C (Some ? w)))
 | leq4: ∀w. leq (CT w) (MMT (MM (Some ? w))).

theorem leq_ok: ∀w1,w2. leq w1 w2 → leq w2 w1 → w1 = w2.
 intros 3; elim H;
  [ reflexivity;
  | elim H5 in H1 H2 H3 H4 ⊢ %;
     [ reflexivity;
     | rewrite > H4; try assumption; try autobatch; [ apply H2;
       try autobatch; ] intro; [ transitivity t3;
        [ apply H2; try autobatch; ] intros;
     | 
     |

definition LEQ ≝ λw1,w2:t. bool.

definition leq: t → t → bool.
 intro w1; change with (∀w2. LEQ w1 w2); cases w1 (w1'); clear w1;
  [ apply (ct_rect' ? (λw1.∀w2.LEQ (MMT w1) w2) ????? w1'); simplify; clear w1';
     [
     |

 intros (w1 w2); change with (LEQ w1 w2);
 cases w1 (w1' w1'); [ apply (ct_rect' ??????? w1'); cases w1'; cases w2 (w2' w2'); cases w2';
  [

let rec leq (w1: t) (w2: t) : bool ≝
 match w1 with
  [ CT w1' ⇒
     match w1' with
      [ E ⇒ match w2 with [CT w2' ⇒ 
  