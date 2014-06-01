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

include "basic_2/substitution/lift.ma".
include "apps_2/functional/notation.ma".

(* FUNCTIONAL RELOCATION ****************************************************)

let rec flift d e U on U ≝ match U with
[ TAtom I     ⇒ match I with
  [ Sort _ ⇒ U
  | LRef i ⇒ #(tri … i d i (i + e) (i + e))
  | GRef _ ⇒ U
  ]
| TPair I V T ⇒ match I with
  [ Bind2 a I ⇒ ⓑ{a,I} (flift d e V). (flift (d+1) e T)
  | Flat2 I   ⇒ ⓕ{I} (flift d e V). (flift d e T)
  ]
].

interpretation "functional relocation" 'Lift d e T = (flift d e T).

(* Main properties **********************************************************)

theorem flift_lift: ∀T,d,e. ⇧[d, e] T ≡ ↑[d, e] T.
#T elim T -T
[ * #i #d #e //
  elim (lt_or_eq_or_gt i d) #Hid normalize
  [ >(tri_lt ?????? Hid) /2 width=1/
  | /2 width=1/
  | >(tri_gt ?????? Hid) /3 width=2/
  ]
| * /2/
]
qed.

(* Main inversion properties ************************************************)

theorem flift_inv_lift: ∀d,e,T1,T2. ⇧[d, e] T1 ≡ T2 → ↑[d, e] T1 = T2.
#d #e #T1 #T2 #H elim H -d -e -T1 -T2 normalize //
[ #i #d #e #Hid >(tri_lt ?????? Hid) //
| #i #d #e #Hid
  elim (le_to_or_lt_eq … Hid) -Hid #Hid
  [ >(tri_gt ?????? Hid) //
  | destruct //
  ]
]
qed-.

(* Derived properties *******************************************************)

lemma flift_join: ∀e1,e2,T. ⇧[e1, e2] ↑[0, e1] T ≡ ↑[0, e1 + e2] T.
#e1 #e2 #T
lapply (flift_lift T 0 (e1+e2)) #H
elim (lift_split … H e1 e1) -H // #U #H
>(flift_inv_lift … H) -H //
qed.
