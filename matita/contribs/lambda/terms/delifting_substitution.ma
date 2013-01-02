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

include "terms/lift.ma".

(* DELIFTING SUBSTITUTION ***************************************************)

(* Policy: depth (level) metavariables: d, e (as for lift) *)
let rec dsubst D d M on M ≝ match M with
[ VRef i   ⇒ tri … i d (#i) (↑[i] D) (#(i-1))
| Abst A   ⇒ 𝛌. (dsubst D (d+1) A)
| Appl B A ⇒ @ (dsubst D d B). (dsubst D d A)
].

interpretation "delifting substitution"
   'DSubst D d M = (dsubst D d M).

lemma dsubst_vref_lt: ∀i,d,D. i < d → [d ↙ D] #i = #i.
normalize /2 width=1/
qed.

lemma dsubst_vref_eq: ∀i,D. [i ↙ D] #i = ↑[i]D.
normalize //
qed.

lemma dsubst_vref_gt: ∀i,d,D. d < i → [d ↙ D] #i = #(i-1).
normalize /2 width=1/
qed.

theorem dsubst_lift_le: ∀h,D,M,d1,d2. d2 ≤ d1 →
                        [d2 ↙ ↑[d1 - d2, h] D] ↑[d1 + 1, h] M = ↑[d1, h] [d2 ↙ D] M.
#h #D #M elim M -M
[ #i #d1 #d2 #Hd21 elim (lt_or_eq_or_gt i d2) #Hid2
  [ lapply (lt_to_le_to_lt … Hid2 Hd21) -Hd21 #Hid1
    >(dsubst_vref_lt … Hid2) >(lift_vref_lt … Hid1) >lift_vref_lt /2 width=1/
  | destruct >dsubst_vref_eq >lift_vref_lt /2 width=1/
  | >(dsubst_vref_gt … Hid2) -Hd21 elim (lt_or_ge (i-1) d1) #Hi1d1
    [ >(lift_vref_lt … Hi1d1) >lift_vref_lt /2 width=1/
    | lapply (ltn_to_ltO … Hid2) #Hi
      >(lift_vref_ge … Hi1d1) >lift_vref_ge /2 width=1/ -Hi1d1 >plus_minus // /3 width=1/
    ]
  ]
| normalize #A #IHA #d1 #d2 #Hd21
  lapply (IHA (d1+1) (d2+1) ?) -IHA /2 width=1/
| normalize #B #A #IHB #IHA #d1 #d2 #Hd21
  >IHB -IHB // >IHA -IHA //
]
qed.

theorem dsubst_lift_be: ∀h,D,M,d1,d2. d1 ≤ d2 → d2 ≤ d1 + h →
                        [d2 ↙ D] ↑[d1, h + 1] M = ↑[d1, h] M.
#h #D #M elim M -M
[ #i #d1 #d2 #Hd12 #Hd21 elim (lt_or_ge i d1) #Hid1
  [ lapply (lt_to_le_to_lt … Hid1 Hd12) -Hd12 -Hd21 #Hid2
    >(lift_vref_lt … Hid1) >(lift_vref_lt … Hid1) /2 width=1/
  | lapply (transitive_le … (i+h) Hd21 ?) -Hd12 -Hd21 /2 width=1/ #Hd2
    >(lift_vref_ge … Hid1) >(lift_vref_ge … Hid1) -Hid1
    >dsubst_vref_gt // /2 width=1/
  ]
| normalize #A #IHA #d1 #d2 #Hd12 #Hd21
  >IHA -IHA // /2 width=1/
| normalize #B #A #IHB #IHA #d1 #d2 #Hd12 #Hd21
  >IHB -IHB // >IHA -IHA //
]
qed.

theorem dsubst_lift_ge: ∀h,D,M,d1,d2. d1 + h ≤ d2 →
                        [d2 ↙ D] ↑[d1, h] M = ↑[d1, h] [d2 - h ↙ D] M.
#h #D #M elim M -M
[ #i #d1 #d2 #Hd12 elim (lt_or_eq_or_gt i (d2-h)) #Hid2h
  [ >(dsubst_vref_lt … Hid2h) elim (lt_or_ge i d1) #Hid1
    [ lapply (lt_to_le_to_lt … (d1+h) Hid1 ?) -Hid2h // #Hid1h
      lapply (lt_to_le_to_lt … Hid1h Hd12) -Hid1h -Hd12 #Hid2
      >(lift_vref_lt … Hid1) -Hid1 /2 width=1/
    | >(lift_vref_ge … Hid1) -Hid1 -Hd12 /3 width=1/
    ]
  | destruct elim (le_inv_plus_l … Hd12) -Hd12 #Hd12 #Hhd2
    >dsubst_vref_eq >lift_vref_ge // >lift_lift_be // <plus_minus_m_m //
  | elim (le_inv_plus_l … Hd12) -Hd12 #Hd12 #_
    lapply (le_to_lt_to_lt … Hd12 Hid2h) -Hd12 #Hid1
    lapply (ltn_to_ltO … Hid2h) #Hi
    >(dsubst_vref_gt … Hid2h)
    >lift_vref_ge /2 width=1/ >lift_vref_ge /2 width=1/ -Hid1
    >dsubst_vref_gt /2 width=1/ -Hid2h >plus_minus //
  ]
| normalize #A #IHA #d1 #d2 #Hd12
  elim (le_inv_plus_l … Hd12) #_ #Hhd2
  >IHA -IHA /2 width=1/ <plus_minus //
| normalize #B #A #IHB #IHA #d1 #d2 #Hd12
  >IHB -IHB // >IHA -IHA //
]
qed.

theorem dsubst_dsubst_ge: ∀D1,D2,M,d1,d2. d1 ≤ d2 →
                          [d2 ↙ D2] [d1 ↙ D1] M = [d1 ↙ [d2 - d1 ↙ D2] D1] [d2 + 1 ↙ D2] M.
#D1 #D2 #M elim M -M
[ #i #d1 #d2 #Hd12 elim (lt_or_eq_or_gt i d1) #Hid1
  [ lapply (lt_to_le_to_lt … Hid1 Hd12) -Hd12 #Hid2
    >(dsubst_vref_lt … Hid1) >(dsubst_vref_lt … Hid2) >dsubst_vref_lt /2 width=1/
  | destruct >dsubst_vref_eq >dsubst_vref_lt /2 width=1/
  | >(dsubst_vref_gt … Hid1) elim (lt_or_eq_or_gt i (d2+1)) #Hid2
    [ lapply (ltn_to_ltO … Hid1) #Hi
      >(dsubst_vref_lt … Hid2) >dsubst_vref_lt /2 width=1/
    | destruct /2 width=1/
    | lapply (le_to_lt_to_lt (d1+1) … Hid2) -Hid1 /2 width=1/ -Hd12 #Hid1
      >(dsubst_vref_gt … Hid2) >dsubst_vref_gt /2 width=1/
      >dsubst_vref_gt // /2 width=1/
    ]
  ]
| normalize #A #IHA #d1 #d2 #Hd12
  lapply (IHA (d1+1) (d2+1) ?) -IHA /2 width=1/
| normalize #B #A #IHB #IHA #d1 #d2 #Hd12
  >IHB -IHB // >IHA -IHA //
]
qed.

theorem dsubst_dsubst_lt: ∀D1,D2,M,d1,d2. d2 < d1 →
                          [d2 ↙ [d1 - d2 -1 ↙ D1] D2] [d1 ↙ D1] M = [d1 - 1 ↙ D1] [d2 ↙ D2] M.
#D1 #D2 #M #d1 #d2 #Hd21
lapply (ltn_to_ltO … Hd21) #Hd1
>dsubst_dsubst_ge in ⊢ (???%); /2 width=1/ <plus_minus_m_m //
qed.

definition dsubstable_dx: predicate (relation term) ≝ λR.
                          ∀D,M1,M2. R M1 M2 → ∀d. R ([d ↙ D] M1) ([d ↙ D] M2).

definition dsubstable: predicate (relation term) ≝ λR.
                       ∀D1,D2. R D1 D2 → ∀M1,M2. R M1 M2 → ∀d. R ([d ↙ D1] M1) ([d ↙ D2] M2).

lemma star_dsubstable_dx: ∀R. dsubstable_dx R → dsubstable_dx (star … R).
#R #HR #D #M1 #M2 #H elim H -M2 // /3 width=3/
qed.

lemma lstar_dsubstable_dx: ∀S,R. (∀a. dsubstable_dx (R a)) →
                           ∀l. dsubstable_dx (lstar S … R l).
#S #R #HR #l #D #M1 #M2 #H
@(lstar_ind_l ????????? H) -l -M1 // /3 width=3/
qed.

lemma star_dsubstable: ∀R. reflexive ? R →
                       dsubstable R → dsubstable (star … R).
#R #H1R #H2 #D1 #D2 #H elim H -D2 /3 width=1/ /3 width=5/
qed.
